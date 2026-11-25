import Leaf.Core.Types
import Leaf.Core.Policy
import Leaf.Core.Schema
import Leaf.Core.Crc32
import Leaf.Core.Sha256Spec
import Leaf.Core.Sha256
import Leaf.Core.Sha256Vectors
import Leaf.Core.Codec
import Leaf.Core.Frame
import Leaf.Core.DbModel
import Leaf.Core.WalLog
import Leaf.Core.BucketModel
import Leaf.Core.StoreModel

open Leaf.Core

def check (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw <| IO.userError s!"Assertion failed: {msg}"

local instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

def testTypesAndPolicy : IO Unit := do
  let p1 : PostId := ⟨1⟩
  let p2 : PostId := ⟨2⟩
  check (p1 < p2) "PostId ordering"
  check (p1 != p2) "PostId inequality"

  -- ObjectLocation dependent bounds
  let loc : ObjectLocation 16777216 := ⟨⟨1⟩, 100, 64, by decide, by decide⟩
  check (loc.offset == 100 && loc.length == 64) "ObjectLocation fields"

  -- MIME sniffing
  let jpegBytes := ByteArray.mk #[0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x10]
  let pngBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00]
  let webpBytes := ByteArray.mk #[0x52, 0x49, 0x46, 0x46, 0x24, 0x00, 0x00, 0x00, 0x57, 0x45, 0x42, 0x50]
  let gifBytes := "GIF89a...".toUTF8
  let badBytes := "not an image".toUTF8
  check (detectMimeType jpegBytes == some .jpeg) "JPEG magic"
  check (detectMimeType pngBytes == some .png) "PNG magic"
  check (detectMimeType webpBytes == some .webp) "WebP magic"
  check (detectMimeType gifBytes == some .gif) "GIF magic"
  check (detectMimeType badBytes == none) "Invalid magic"

  -- FeedKey descending order across same-second ties
  let k1 : FeedKey := ⟨1000, ⟨1⟩⟩
  let k2 : FeedKey := ⟨1000, ⟨2⟩⟩
  let k3 : FeedKey := ⟨1001, ⟨1⟩⟩
  check (FeedKey.cmpDesc k3 k2 == .lt) "Newer timestamp sorts first"
  check (FeedKey.cmpDesc k2 k1 == .lt) "Higher PostId breaks tie first"
  check (FeedKey.cmpDesc k1 k1 == .eq) "Reflexive FeedKey cmpDesc"

  -- Sha256Digest construction & hex
  let zeros := ByteArray.mk (Array.replicate 32 0)
  let some d := Sha256Digest.ofBytes? zeros | throw <| IO.userError "expected 32 bytes"
  check (d.toHex == String.ofList (List.replicate 64 '0')) "Sha256Digest hex"
  check (Sha256Digest.ofBytes? (ByteArray.mk #[1, 2, 3]) |>.isNone) "Reject non-32-byte digest"

  -- Default StoragePolicy
  let pol := StoragePolicy.default
  check (pol.maxImageBytes == 10 * 1024 * 1024) "Default max image 10 MiB"
  check (pol.segmentSize == 16 * 1024 * 1024) "Default segment size 16 MiB"

def testSchemaAndValidation : IO Unit := do
  let pol := StoragePolicy.default
  let pngBytes := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x01, 0x02]

  -- Valid caption-only draft trims fields
  let d1 : PostDraft := {
    author := "  alice  "
    title := some "  Morning  "
    caption := "  Hello Leaf  "
    tags := #[" lean ", "systems", "lean"]
    imageBytes := none
  }
  match validateDraft pol d1 with
  | .error e => throw <| IO.userError s!"Unexpected validation failure: {repr e}"
  | .ok vd =>
    check (vd.author == "alice") "Trimmed author"
    check (vd.title == some "Morning") "Trimmed title"
    check (vd.caption == "Hello Leaf") "Trimmed caption"
    check (vd.tags == #["lean", "systems"]) "Trimmed deduplicated tags"
    check (vd.image.isNone) "No image"

  -- Valid image-only draft
  let d2 : PostDraft := { author := "bob", caption := "", imageBytes := some pngBytes }
  match validateDraft pol d2 with
  | .error e => throw <| IO.userError s!"Unexpected image-only validation failure: {repr e}"
  | .ok vd =>
    check (vd.image.map (·.1) == some .png) "Detected PNG"

  -- Reject empty author, empty content, bad image signature, oversized caption, too many tags
  check (validateDraft pol { author := "   ", caption := "hi" } == .error .emptyAuthor) "Reject blank author"
  check (validateDraft pol { author := "a", caption := "   " } == .error .emptyContent) "Reject empty content"
  check (validateDraft pol { author := "a", title := some "  ", caption := "ok" } == .error .emptyTitle) "Reject blank title"
  check (validateDraft pol { author := "a", caption := "", imageBytes := some "bad".toUTF8 } == .error .invalidImageSignature) "Reject bad image"
  check (validateDraft pol { author := "a", caption := String.ofList (List.replicate 2001 'x') } == .error .captionTooLong) "Reject long caption"
  check (validateDraft pol { author := "a", caption := "ok", tags := Array.replicate 17 "t" } == .error .tooManyTags) "Reject >16 tags"
  check (validateDraft { pol with maxImageBytes := 4, imageFitsSegment := by decide } { author := "a", imageBytes := some pngBytes } == .error .imageTooLarge) "Reject oversized image"

  -- Patch validation rejects removing the only image when caption is empty
  let imgOnlyPost : Post := {
    id := ⟨1⟩
    author := "bob"
    title := none
    caption := ""
    tags := #[]
    createdAt := 100
    updatedAt := none
    version := ⟨1⟩
    image := some ⟨default, .png, 10⟩
  }
  check (validatePostPatch pol imgOnlyPost { imagePatch := .remove } == .error .emptyContent) "Patch cannot leave post empty"
  match validatePostPatch pol imgOnlyPost { caption? := some "now with text", imagePatch := .remove } with
  | .error e => throw <| IO.userError s!"Unexpected patch failure: {repr e}"
  | .ok vp =>
    check (vp.caption == "now with text") "Updated caption"
    check (vp.imagePatch == .remove) "Image removal patch"

def testCrc32 : IO Unit := do
  check (crc32 ByteArray.empty == 0) "CRC32 empty"
  check (crc32 "123456789".toUTF8 == 0xCBF43926) "CRC32 standard test vector"
  let sample := ByteArray.mk #[0x00, 0xFF, 0x12, 0x34, 0x89, 0xAB, 0xCD, 0xEF]
  check (crc32 sample == crc32Spec sample) "CRC32 matches bitwise spec"
  check (crc32 "Leaf journal".toUTF8 != crc32 "Leaf journam".toUTF8) "CRC32 sensitivity"

def testSha256 : IO Unit := do
  check ((sha256 ByteArray.empty).toHex ==
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") "SHA-256 empty"
  check ((sha256 "abc".toUTF8).toHex ==
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") "SHA-256 abc"
  check ((sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8).toHex ==
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1") "SHA-256 448-bit 2-block"
  let b55 := ByteArray.mk (Array.replicate 55 0x61)
  let b56 := ByteArray.mk (Array.replicate 56 0x61)
  let b64 := ByteArray.mk (Array.replicate 64 0x61)
  check (sha256 b55 == sha256Spec b55) "SHA-256 55-byte boundary matches spec"
  check (sha256 b56 == sha256Spec b56) "SHA-256 56-byte boundary matches spec"
  check (sha256 b64 == sha256Spec b64) "SHA-256 64-byte boundary matches spec"
  let millionA := ByteArray.mk (Array.replicate 1000000 0x61)
  check ((sha256 millionA).toHex ==
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0") "SHA-256 1M 'a'"

def testCodec : IO Unit := do
  -- Integer primitives with prefix/suffix framing
  let pfx := ByteArray.mk #[0xAA, 0xBB, 0xCC]
  let sfx := ByteArray.mk #[0xDD, 0xEE]
  let u16 : UInt16 := 0x1234
  let u32 : UInt32 := 0x89ABCDEF
  let u64 : UInt64 := 0x0123456789ABCDEF
  let i64 : Int64 := -9876543210123
  check (decodeUInt8At (pfx ++ encodeUInt8 0x7F ++ sfx) pfx.size == .ok (0x7F, pfx.size + 1)) "UInt8 roundtrip"
  check (decodeUInt16LEAt (pfx ++ encodeUInt16LE u16 ++ sfx) pfx.size == .ok (u16, pfx.size + 2)) "UInt16 roundtrip"
  check (decodeUInt32LEAt (pfx ++ encodeUInt32LE u32 ++ sfx) pfx.size == .ok (u32, pfx.size + 4)) "UInt32 roundtrip"
  check (decodeUInt64LEAt (pfx ++ encodeUInt64LE u64 ++ sfx) pfx.size == .ok (u64, pfx.size + 8)) "UInt64 roundtrip"
  check (decodeInt64LEAt (pfx ++ encodeInt64LE i64 ++ sfx) pfx.size == .ok (i64, pfx.size + 8)) "Int64 roundtrip"
  check (decodeUInt32LEAt (ByteArray.mk #[1, 2, 3]) 0 == .error .unexpectedEof) "UInt32 short buffer EOF"

  -- Invalid UTF-8 & invalid tag rejection
  let badUtf8Bytes := encodeUInt32LE 2 ++ ByteArray.mk #[0xFF, 0xFE]
  check (decodeStringAt badUtf8Bytes 0 == .error .invalidUtf8) "Reject invalid UTF-8"
  check (decodeOptionAt decodeUInt8At (ByteArray.mk #[0x02, 0x01]) 0 == .error .invalidTag) "Reject bad Option tag"
  check (decodeMimeTypeAt (ByteArray.mk #[0x09]) 0 == .error .invalidTag) "Reject bad MimeType tag"
  check (decodeWalOpAt (ByteArray.mk #[0x7F]) 0 == .error .invalidTag) "Reject bad WalOp tag"

  -- Domain types & deterministic PRNG property checks
  let digest := sha256 "leaf-sample".toUTF8
  let key : ObjectKey := ⟨digest, ⟨7⟩⟩
  let ref : ImageRef := ⟨key, .webp, 4096⟩
  let post : Post := {
    id := ⟨42⟩
    author := "carol"
    title := some "Sunbeam"
    caption := "Pure Lean journal!"
    tags := #["lean4", "storage", "cas"]
    createdAt := 1795763000
    updatedAt := some 1795763100
    version := ⟨9⟩
    image := some ref
  }
  let encPost := encodePost post
  check (decodePostAt (pfx ++ encPost ++ sfx) pfx.size == .ok (post, pfx.size + encPost.size)) "Post prefix/suffix roundtrip"

  let rawLoc : RawObjectLocation := ⟨⟨3⟩, 1024, 4096⟩
  let wEntry : WalBucketEntry := ⟨key, rawLoc, .jpeg, 0x12345678⟩
  let ops : Array WalOp := #[
    .beginTx, .allocObject wEntry, .putPost post, .updatePost post,
    .incRef key, .decRef key, .deletePost ⟨42⟩, .commitTx, .abortTx
  ]
  for op in ops do
    let b := encodeWalOp op
    check (decodeWalOpAt (pfx ++ b ++ sfx) pfx.size == .ok (op, pfx.size + b.size)) s!"WalOp roundtrip: {repr op}"

  let segRec : BucketSegmentRecord := ⟨key, .png, ByteArray.mk #[1, 2, 3, 4, 5]⟩
  let encSeg := encodeBucketSegmentRecord segRec
  check (decodeBucketSegmentRecordAt (pfx ++ encSeg ++ sfx) pfx.size == .ok (segRec, pfx.size + encSeg.size)) "SegmentRecord roundtrip"

  let dbMan : DbManifest := ⟨1, 4, 12, ⟨100⟩, ⟨55⟩, ⟨250⟩⟩
  check (decodeDbManifestAt (encodeDbManifest dbMan) 0 == .ok (dbMan, (encodeDbManifest dbMan).size)) "DbManifest roundtrip"
  let bktMan : BucketManifest := ⟨1, 16777216, ⟨2⟩, 8192⟩
  check (decodeBucketManifestAt (encodeBucketManifest bktMan) 0 == .ok (bktMan, (encodeBucketManifest bktMan).size)) "BucketManifest roundtrip"
  let ckpt : DbCheckpoint := ⟨⟨100⟩, ⟨250⟩, #[post], #[⟨5⟩, ⟨9⟩]⟩
  check (decodeDbCheckpointAt (encodeDbCheckpoint ckpt) 0 == .ok (ckpt, (encodeDbCheckpoint ckpt).size)) "DbCheckpoint roundtrip"

  -- Deterministic LCG PRNG fuzzing (50 randomized posts)
  let mut seed : UInt64 := 0x9E3779B97F4A7C15
  for idx in List.range 50 do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let randLen := (seed >>> 56).toNat % 40
    let randStr := String.ofList (List.replicate randLen (Char.ofNat (65 + idx % 26)))
    let randPost : Post := {
      id := ⟨idx.toUInt64 + 1⟩
      author := s!"u_{idx}"
      title := if seed &&& 1 == 1 then some s!"t_{randLen}" else none
      caption := randStr
      tags := Array.replicate (idx % 5) s!"tag{idx}"
      createdAt := (seed &&& 0xFFFFFFFF).toInt64 - 50000
      updatedAt := if seed &&& 2 == 2 then some 99 else none
      version := ⟨seed &&& 0xFFFF⟩
      image := if idx % 3 == 0 then some ⟨⟨sha256 randStr.toUTF8, ⟨idx.toUInt64⟩⟩, .gif, randLen.toUInt32⟩ else none
    }
    let b := encodePost randPost
    check (decodePostAt (pfx ++ b ++ sfx) pfx.size == .ok (randPost, pfx.size + b.size)) s!"PRNG post #{idx}"

def testFrame : IO Unit := do
  let pol := StoragePolicy.default
  let pfx := ByteArray.mk #[0x11, 0x22, 0x33, 0x44]
  let sfx := ByteArray.mk #[0x55, 0x66]
  let payload := "hello framed record".toUTF8

  for kind in [FrameKind.wal, .segment, .checkpoint, .manifest] do
    let hdr : FrameHeader := {
      kind := kind
      formatVersion := frameFormatVersion
      recordType := 3
      flags := 0
      txId := ⟨12⟩
      seqNo := ⟨99⟩
      payloadLen := payload.size.toUInt32
    }
    let frame : Frame := ⟨hdr, payload⟩
    let enc ← match encodeFrame pol frame with
      | .ok b => pure b
      | .error e => throw <| IO.userError s!"encodeFrame unexpected error: {repr e}"
    check (enc.size == 32 + payload.size) "Framed record length = 32 + payload"
    check (decodeFrameAt pol kind (pfx ++ enc ++ sfx) pfx.size == .ok (frame, pfx.size + enc.size))
      s!"Frame roundtrip for {repr kind}"

  -- Rejection checks
  let hdr0 : FrameHeader := ⟨.wal, 1, 1, 0, ⟨5⟩, ⟨6⟩, payload.size.toUInt32⟩
  let frame0 : Frame := ⟨hdr0, payload⟩
  let .ok validBytes := encodeFrame pol frame0 | throw <| IO.userError "expected valid frame"

  -- Wrong magic / kind
  check (decodeFrameAt pol .segment validBytes 0 == .error .invalidMagic) "Reject wrong frame kind/magic"
  -- Unsupported version
  let badVer : Frame := ⟨{ hdr0 with formatVersion := 2 }, payload⟩
  let badVerBytes := encodeFrameRaw badVer
  check (decodeFrameAt pol .wal badVerBytes 0 == .error .unsupportedVersion) "Reject unsupported version"
  -- Payload exceeds policy
  let smallPol : StoragePolicy := { pol with maxFramePayloadBytes := 4, frameFitsUInt32 := by decide }
  check (encodeFrame smallPol frame0 == .error .boundsExceeded) "Encode rejects payload > maxFramePayloadBytes"
  check (decodeFrameAt smallPol .wal validBytes 0 == .error .boundsExceeded) "Decode rejects payload > maxFramePayloadBytes"
  -- Truncation at header, payload, and CRC trailer
  check (decodeFrameAt pol .wal (validBytes.extract 0 10) 0 == .error .unexpectedEof) "Reject truncated header"
  check (decodeFrameAt pol .wal (validBytes.extract 0 30) 0 == .error .unexpectedEof) "Reject truncated payload"
  check (decodeFrameAt pol .wal (validBytes.extract 0 (validBytes.size - 1)) 0 == .error .unexpectedEof) "Reject truncated CRC trailer"
  -- Single-bit flip in header, payload, and CRC trailer -> checksumMismatch
  for flipIdx in [4, 15, 29, validBytes.size - 1] do
    let mutated := validBytes.set! flipIdx (validBytes.get! flipIdx ^^^ 0x01)
    let expectedErr := if flipIdx == 4 then DecodeError.unsupportedVersion else DecodeError.checksumMismatch
    check (decodeFrameAt pol .wal mutated 0 == .error expectedErr) s!"Detect corruption at byte {flipIdx}"

def testDbModel : IO Unit := do
  let pol : StoragePolicy := {}
  let okDraft (author caption : String) : IO ValidPostDraft :=
    match validateDraft pol { author := author, caption := caption } with
    | .ok d => pure d
    | .error e => throw <| IO.userError s!"draft error: {repr e}"
  let d1 ← okDraft "Alice" "First post"
  let d2 ← okDraft "Bob" "Second post same sec"
  let d3 ← okDraft "Carol" "Third post same sec"
  let d4 ← okDraft "Dave" "Fourth post same sec"

  let db0 := DbState.empty
  let .ok (p1, db1) := db0.createPost 1000 d1 none | throw <| IO.userError "create p1"
  let .ok (p2, db2) := db1.createPost 2000 d2 none | throw <| IO.userError "create p2"
  let .ok (p3, db3) := db2.createPost 2000 d3 none | throw <| IO.userError "create p3"
  let .ok (p4, db4) := db3.createPost 2000 d4 none | throw <| IO.userError "create p4"

  check (db4.getPost p1.id == some p1) "DbModel getPost p1"
  check (db4.getPost p4.id == some p4) "DbModel getPost p4"
  check (db4.getPost ⟨999⟩ == none) "DbModel missing post none"

  -- Feed order: p4 (2000,4) > p3 (2000,3) > p2 (2000,2) > p1 (1000,1)
  let page1 := db4.queryFeed none 2
  check (page1 == #[p4, p3]) "DbModel page 1 breaks same-second ties by id desc"
  let cur1 := some (FeedKey.ofPost p3)
  let page2 := db4.queryFeed cur1 2
  check (page2 == #[p2, p1]) "DbModel page 2 resumes strictly after cursor"
  let cur2 := some (FeedKey.ofPost p1)
  let page3 := db4.queryFeed cur2 2
  check (page3.isEmpty) "DbModel page 3 past end is empty"

  -- Update p2 preserves createdAt and id, updates updatedAt, version, caption
  let .ok patch2 := validatePostPatch pol p2 { caption? := some "Updated second" }
    | throw <| IO.userError "patch2"
  let .ok (p2', db5) := db4.updatePost p2.id 2500 patch2 none
    | throw <| IO.userError "update p2"
  check (p2'.createdAt == 2000) "Update preserves createdAt"
  check (p2'.updatedAt == some 2500) "Update sets updatedAt"
  check (p2'.version.val > p2.version.val) "Update advances version"
  check (p2'.caption == "Updated second") "Update modifies caption"
  check (db5.getPost p2.id == some p2') "DbModel getPost sees updated post"
  check (db5.queryFeed none 10 == #[p4, p3, p2', p1]) "Update keeps feed ordering"
  check (match db5.updatePost ⟨999⟩ 2500 patch2 none with | .error (.postNotFound ⟨999⟩) => true | _ => false)
    "Update missing post returns postNotFound"

  -- Delete p3 adds tombstone and excludes from getPost and queryFeed
  let .ok (rel3, db6) := db5.deletePost p3.id | throw <| IO.userError "delete p3"
  check (rel3 == none) "Deleted post had no image"
  check (db6.getPost p3.id == none) "Deleted post absent from getPost"
  check (p3.id ∈ db6.tombstones) "Deleted post recorded in tombstones"
  check (db6.queryFeed none 10 == #[p4, p2', p1]) "Deleted post excluded from queryFeed"
  check (match db6.deletePost p3.id with | .error (.postNotFound id) => id == p3.id | _ => false)
    "Double delete returns postNotFound"

  -- Compact removes tombstones without altering live posts or feed
  let db7 := db6.compactDb
  check (db7.tombstones.isEmpty) "Compact clears tombstones"
  check (db7.getPost p4.id == some p4 && db7.getPost p2.id == some p2') "Compact preserves live posts"
  check (db7.queryFeed none 10 == #[p4, p2', p1]) "Compact preserves queryFeed"

def testBucketModel : IO Unit := do
  let smallPol : StoragePolicy :=
    { maxImageBytes := 60
      segmentSize := 200
      maxFramePayloadBytes := 120
      imageFitsSegment := by decide
      frameFitsUInt32 := by decide }
  let pngHeader := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
  let mkImg (tag : UInt8) : ByteArray :=
    pngHeader ++ ByteArray.mk (Array.replicate 12 tag) -- total 20 bytes -> 97B record
  let img1 := mkImg 1
  let img2 := mkImg 2
  let img3 := mkImg 3
  let fakeDigest := sha256 img1

  let b0 := BucketState.empty smallPol
  let .ok (k1, b1) := b0.putObject .png img1 | throw <| IO.userError "put img1"
  let .ok (k1Dup, b1Dup) := b1.putObject .png img1 | throw <| IO.userError "dedup img1"
  check (k1 == k1Dup) "putObject deduplicates identical bytes"
  check (b1Dup.objects.size == 1) "dedup does not insert duplicate object"
  check (b1Dup.getObject k1 == some img1) "getObject returns stored bytes"

  -- Explicit hash collision handling with distinct bytes sharing fakeDigest
  let .ok (kCol1, b2) := b1Dup.putObjectWithHash fakeDigest .png img2
    | throw <| IO.userError "put collision 2"
  check (kCol1 != k1) "Collision disambiguates distinct bytes under same digest"
  check (kCol1.digest == fakeDigest && kCol1.tag == ⟨1⟩) "Collision increments CollisionTag"
  check (b2.getObject k1 == some img1 && b2.getObject kCol1 == some img2)
    "Both colliding payloads retrieve accurately"
  let .ok (kCol1Dup, _) := b2.putObjectWithHash fakeDigest .png img2
    | throw <| IO.userError "dedup collision 2"
  check (kCol1Dup == kCol1) "Collision bucket deduplicates second payload too"

  -- Segment rollover on 3rd 97B record (97 + 97 = 194 <= 200, 194 + 97 > 200)
  let .ok (k3, b3) := b2.putObject .png img3 | throw <| IO.userError "put img3"
  let some m1 := b3.getMeta k1 | throw <| IO.userError "meta k1"
  let some m2 := b3.getMeta kCol1 | throw <| IO.userError "meta kCol1"
  let some m3 := b3.getMeta k3 | throw <| IO.userError "meta k3"
  check (m1.location.segment == ⟨1⟩ && m2.location.segment == ⟨1⟩) "First two objects in segment 1"
  check (m1.location.offset + m1.location.length ≤ m2.location.offset) "Segment 1 offsets non-overlapping"
  check (m3.location.segment == ⟨2⟩ && m3.location.offset == 0) "Third object rolls over to segment 2"
  check (b3.activeSeg == ⟨2⟩) "activeSeg advances on rollover"

  -- Refcounting and GC
  let .ok b4 := b3.incRef k1 | throw <| IO.userError "incRef k1"
  let .ok b5 := b4.incRef k3 | throw <| IO.userError "incRef k3"
  let b6 := b5.gcStep
  check (b6.getObject kCol1 == none && b6.getMeta kCol1 == none) "gcStep reclaims refCount=0 object"
  check (b6.getObject k1 == some img1 && b6.getObject k3 == some img3)
    "gcStep preserves refCount>0 objects"

  -- Compaction packs live objects into fresh segments starting at nextSegId
  let prevNextSeg := b6.nextSegId
  let .ok b7 := b6.compactBucket | throw <| IO.userError "compactBucket"
  check (b7.segments[(⟨1⟩ : SegmentId)]? == none && b7.segments[(⟨2⟩ : SegmentId)]? == none) "Compaction drops old segments"
  check (b7.getObject k1 == some img1 && b7.getObject k3 == some img3)
    "Compaction preserves live object bytes"
  let some m1' := b7.getMeta k1 | throw <| IO.userError "meta k1 post-compact"
  let some m3' := b7.getMeta k3 | throw <| IO.userError "meta k3 post-compact"
  check (m1'.location.segment.val ≥ prevNextSeg.val && m3'.location.segment.val ≥ prevNextSeg.val)
    "Compaction assigns fresh segment IDs"
  check (m1'.crc32 == m1.crc32 && m1'.mime == m1.mime && m1'.refCount == 1)
    "Compaction preserves entry metadata and refCount"

def testStoreModel : IO Unit := do
  let pol : StoragePolicy := {}
  let pngHeader := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
  let imgA := pngHeader ++ ByteArray.mk (Array.replicate 16 0x11)
  let imgB := pngHeader ++ ByteArray.mk (Array.replicate 16 0x22)

  let s0 := StoreState.empty pol
  let .ok dA := validateDraft pol { author := "Alice", caption := "Post A", imageBytes := some imgA }
    | throw <| IO.userError "draft A"
  let .ok dB := validateDraft pol { author := "Bob", caption := "Post B", imageBytes := some imgB }
    | throw <| IO.userError "draft B"

  -- Tx 1: stage imgA + commitCreate
  let .ok (tx1, s1) := s0.beginTx | throw <| IO.userError "beginTx 1"
  check (tx1 == ⟨1⟩) "First txId is 1"
  let .ok (refA, s2) := s1.stageImage .png imgA | throw <| IO.userError "stage imgA"
  let .ok (p1, s3) := s2.commitCreate 1000 dA (some refA) | throw <| IO.userError "commitCreate 1"
  check (s3.activeTx.isNone) "activeTx cleared on commitCreate"
  check (s3.db.getPost p1.id == some p1) "commitCreate visible in db"
  check ((s3.bucket.getMeta refA.key).map (·.refCount) == some 1) "refA refCount == 1"

  -- Tx 2: stage imgB then abortTx -> orphaned blob with refCount = 0
  let .ok (_, s4) := s3.beginTx | throw <| IO.userError "beginTx 2"
  let .ok (refB, s5) := s4.stageImage .png imgB | throw <| IO.userError "stage imgB"
  check ((s5.bucket.getMeta refB.key).map (·.refCount) == some 0) "staged imgB refCount == 0"
  let .ok s6 := s5.abortTx | throw <| IO.userError "abortTx 2"
  check (s6.activeTx.isNone) "activeTx cleared on abortTx"
  check (s6.db.getPost ⟨2⟩ == none) "aborted post never committed"
  check ((s6.bucket.getMeta refA.key).map (·.refCount) == some 1) "abort leaves live refA intact"

  -- runGC reclaims orphaned imgB while preserving live imgA
  let .ok s7 := s6.runGC | throw <| IO.userError "runGC"
  check (s7.bucket.getObject refB.key == none) "runGC reclaims orphaned refB"
  check (s7.bucket.getObject refA.key == some imgA) "runGC preserves live refA"

  -- Tx 3: create post 2 sharing imgA (dedup) -> refCount == 2
  let .ok (_, s8) := s7.beginTx | throw <| IO.userError "beginTx 3"
  let .ok (refA2, s9) := s8.stageImage .png imgA | throw <| IO.userError "stage imgA dedup"
  check (refA2.key == refA.key) "stageImage deduplicates imgA"
  let .ok (p2, s10) := s9.commitCreate 1000 dB (some refA2) | throw <| IO.userError "commitCreate 2"
  check ((s10.bucket.getMeta refA.key).map (·.refCount) == some 2) "deduped refA refCount == 2"

  -- Tx 4: update p1 replacing imgA with imgB -> refA == 1, refB' == 1
  let .ok (_, s11) := s10.beginTx | throw <| IO.userError "beginTx 4"
  let .ok (refB', s12) := s11.stageImage .png imgB | throw <| IO.userError "stage imgB'"
  let .ok patch1 := validatePostPatch pol p1 { caption? := some "Swapped", imagePatch := .replace imgB }
    | throw <| IO.userError "patch1"
  let .ok (p1', s13) := s12.commitUpdate p1.id 1500 patch1 (some refB') | throw <| IO.userError "commitUpdate"
  check (p1'.caption == "Swapped") "commitUpdate updates post"
  check ((s13.bucket.getMeta refA.key).map (·.refCount) == some 1) "commitUpdate decrements old image"
  check ((s13.bucket.getMeta refB'.key).map (·.refCount) == some 1) "commitUpdate increments new image"

  -- Tx 5: delete p2 -> refA == 0, runGC reclaims refA, runCompact succeeds
  let .ok (_, s14) := s13.beginTx | throw <| IO.userError "beginTx 5"
  let .ok (_, s15) := s14.commitDelete p2.id | throw <| IO.userError "commitDelete"
  check ((s15.bucket.getMeta refA.key).map (·.refCount) == some 0) "commitDelete decrements refA to 0"
  let .ok s16 := s15.runGC | throw <| IO.userError "runGC 2"
  check (s16.bucket.getObject refA.key == none) "runGC reclaims unreferenced refA"
  let .ok s17 := s16.runCompact | throw <| IO.userError "runCompact"
  check (s17.db.getPost p1.id == some p1' && s17.bucket.getObject refB'.key == some imgB)
    "runCompact preserves live post and image"

def testWalLog : IO Unit := do
  let pol : StoragePolicy := {}
  let post1 : Post :=
    { id := ⟨1⟩, author := "alice", title := some "t1", caption := "c1"
      tags := #[], createdAt := 10, updatedAt := none, version := ⟨1⟩, image := none }
  let post2 : Post :=
    { id := ⟨2⟩, author := "bob", title := none, caption := "c2"
      tags := #[], createdAt := 20, updatedAt := none, version := ⟨2⟩, image := none }
  -- Encode two WAL frames + trailing garbage bytes -> scanFrames recovers the 2 valid frames
  let op1 := encodeWalOp (.putPost post1)
  let op2 := encodeWalOp (.putPost post2)
  let f1 : Frame := ⟨⟨.wal, 1, 1, 0, ⟨1⟩, ⟨1⟩, op1.size.toUInt32⟩, op1⟩
  let f2 : Frame := ⟨⟨.wal, 1, 1, 0, ⟨2⟩, ⟨2⟩, op2.size.toUInt32⟩, op2⟩
  let .ok b1 := encodeFrame pol f1 | throw <| IO.userError "encode f1"
  let .ok b2 := encodeFrame pol f2 | throw <| IO.userError "encode f2"
  let partialTail := ByteArray.mk #[0x4C, 0x46, 0x57, 0x00, 0x01]
  let (frames, validEnd) := scanFrames pol .wal (b1 ++ b2 ++ partialTail)
  check (frames.size == 2) "scanFrames recovers 2 valid frames before corrupt tail"
  check (validEnd == b1.size + b2.size) "scanFrames returns exact valid prefix offset"

  -- Uncommitted tx ignored, committed tx applied
  let entries : List (TxId × SeqNo × WalOp) :=
    [ (⟨1⟩, ⟨1⟩, .beginTx)
    , (⟨1⟩, ⟨2⟩, .putPost post1)
    , (⟨2⟩, ⟨3⟩, .beginTx)
    , (⟨2⟩, ⟨4⟩, .putPost post2)
    , (⟨1⟩, ⟨5⟩, .commitTx)
    ]
  let replayed := DbState.replayWalOps DbState.empty entries
  check (replayed.getPost ⟨1⟩ == some post1) "Committed tx 1 applied"
  check (replayed.getPost ⟨2⟩ == none) "Uncommitted tx 2 ignored"

  -- BoundedCache capacity & lookup
  let mut cache := BoundedCache.empty 2
  cache := cache.insert 1 (ByteArray.mk #[1])
  cache := cache.insert 2 (ByteArray.mk #[2])
  cache := cache.insert 3 (ByteArray.mk #[3])
  check (cache.entries.length == 2) "BoundedCache enforces capacity 2"
  check (cache.lookup 1 == none) "BoundedCache evicts oldest entry"
  check (cache.lookup 3 == some (ByteArray.mk #[3])) "BoundedCache returns latest entry"

def main : IO Unit := do
  testTypesAndPolicy
  testSchemaAndValidation
  testCrc32
  testSha256
  testCodec
  testFrame
  testDbModel
  testBucketModel
  testStoreModel
  testWalLog
  IO.println "CoreTests: Tasks 1-10 passed"
