import Leaf.Core.Codec
import Leaf.Core.BucketModel
import Leaf.Core.WalLog
import Leaf.Storage.SeqIO

namespace Leaf.Storage

open Leaf.Core

/-- Persistent content-addressed segmented object storage engine with bounded read cache. -/
structure BucketEngine (policy : StoragePolicy) where
  dir       : System.FilePath
  objects   : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize)
  byDigest  : Std.ExtTreeMap Sha256Digest (Array ObjectKey)
  segments  : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)
  activeSeg : SegmentId
  nextSegId : SegmentId
  cache     : BoundedCache

namespace BucketEngine

def manifestPath (dir : System.FilePath) : System.FilePath :=
  dir / "manifest.bin"

def manifestTmpPath (dir : System.FilePath) : System.FilePath :=
  dir / "manifest.bin.tmp"

def segmentsDir (dir : System.FilePath) : System.FilePath :=
  dir / "segments"

def packPath (dir : System.FilePath) (segId : SegmentId) : System.FilePath :=
  segmentsDir dir / packFileName segId

private def writeManifest {policy : StoragePolicy} (e : BucketEngine policy) : IO (Except String Unit) := do
  let activeUsed := (e.segments[e.activeSeg]?.map (·.used)).getD 0
  let m : BucketManifest :=
    { formatVersion := frameFormatVersion
      segmentSize := policy.segmentSize.toUInt64
      activeSegmentId := e.activeSeg
      activeSegmentOffset := activeUsed.toUInt64 }
  let payload := encodeBucketManifest m
  writeFramedFileAtomic (manifestTmpPath e.dir) (manifestPath e.dir)
    policy .manifest 2 ⟨0⟩ ⟨0⟩ payload

private def scanSegmentFile (dir : System.FilePath) (policy : StoragePolicy) (segId : SegmentId)
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize))
    (byDigest : Std.ExtTreeMap Sha256Digest (Array ObjectKey))
    (segments : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)) :
    IO (Except String (Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize) ×
      Std.ExtTreeMap Sha256Digest (Array ObjectKey) ×
      Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize) × Nat)) := do
  let p := packPath dir segId
  if !(← p.pathExists) then
    return .ok (objects, byDigest, segments, 0)
  try
    let raw ← IO.FS.readBinFile p
    let (frames, validEnd) := scanFrames policy .segment raw
    let mut repaired := 0
    if validEnd < raw.size then
      repaired := raw.size - validEnd
      let tmpP := segmentsDir dir / s!"{packFileName segId}.tmp"
      match ← rewritePrefixAtomic tmpP p (raw.extract 0 validEnd) with
      | .error e => return .error e
      | .ok () => pure ()
    let mut objs := objects
    let mut byD := byDigest
    let mut segs := segments
    let mut off : Nat := 0
    let mut live : Array (ObjectLocation policy.segmentSize) := #[]
    for f in frames do
      let frameSize := frameOverhead + f.payload.size
      match decodeBucketSegmentRecordAt f.payload 0 with
      | .error e => return .error s!"decodeBucketSegmentRecordAt({p}) failed: {repr e}"
      | .ok (rec, _) =>
        if hBound : off + frameSize ≤ policy.segmentSize ∧ 0 < frameSize then
          let loc : ObjectLocation policy.segmentSize :=
            { segment := segId, offset := off, length := frameSize
              validBounds := hBound.1, nonEmpty := hBound.2 }
          let entryMeta : BucketEntryMeta policy.segmentSize :=
            { key := rec.key
              location := loc
              mime := rec.mime
              crc32 := crc32 rec.payload
              byteSize := rec.payload.size
              refCount := 0 }
          objs := objs.insert rec.key entryMeta
          let arr := (byD[rec.key.digest]?).getD #[]
          if !arr.contains rec.key then
            byD := byD.insert rec.key.digest (arr.push rec.key)
          live := live.push loc
      off := off + frameSize
    if hUsed : off ≤ policy.segmentSize then
      segs := segs.insert segId { id := segId, used := off, used_le := hUsed, live := live }
    return .ok (objs, byD, segs, repaired)
  catch e =>
    return .error s!"scanSegmentFile({p}) failed: {e}"

/-- Initializes or opens a `BucketEngine` at `dir`, repairing any truncated pack tails and returning
    `(engine, repairedSegmentBytes)`. -/
def initWithReport (dir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (BucketEngine policy × Nat)) := do
  try
    IO.FS.createDirAll (segmentsDir dir)
    let mPath := manifestPath dir
    if !(← mPath.pathExists) then
      let seg1 : SegmentId := ⟨1⟩
      let emptySeg : SegmentMeta policy.segmentSize :=
        { id := seg1, used := 0, used_le := Nat.zero_le _, live := #[] }
      let eng : BucketEngine policy :=
        { dir := dir
          objects := ∅
          byDigest := ∅
          segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert seg1 emptySeg
          activeSeg := seg1
          nextSegId := ⟨2⟩
          cache := BoundedCache.empty policy.segmentCacheCapacity }
      match ← writeManifest eng with
      | .error e => return .error e
      | .ok () => return .ok (eng, 0)
    else
      match ← readFramedFile mPath policy .manifest with
      | .error e => return .error e
      | .ok mFrame =>
        match decodeBucketManifestAt mFrame.payload 0 with
        | .error e => return .error s!"decodeBucketManifestAt failed: {repr e}"
        | .ok (m, _) =>
          let mut objs : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize) := ∅
          let mut byD : Std.ExtTreeMap Sha256Digest (Array ObjectKey) := ∅
          let mut segs : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize) := ∅
          let mut repairedTotal := 0
          let maxSeg := m.activeSegmentId.val.toNat
          for i in [1 : maxSeg + 1] do
            let sid : SegmentId := ⟨i.toUInt64⟩
            match ← scanSegmentFile dir policy sid objs byD segs with
            | .error e => return .error e
            | .ok (o', b', s', rep) =>
              objs := o'; byD := b'; segs := s'; repairedTotal := repairedTotal + rep
          if segs[m.activeSegmentId]?.isNone then
            segs := segs.insert m.activeSegmentId
              { id := m.activeSegmentId, used := 0, used_le := Nat.zero_le _, live := #[] }
          return .ok
            ({ dir := dir
               objects := objs
               byDigest := byD
               segments := segs
               activeSeg := m.activeSegmentId
               nextSegId := ⟨m.activeSegmentId.val + 1⟩
               cache := BoundedCache.empty policy.segmentCacheCapacity }, repairedTotal)
  catch e =>
    return .error s!"BucketEngine.init failed: {e}"

/-- Initializes or opens a `BucketEngine` at `dir`. -/
def init (dir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (BucketEngine policy)) := do
  match ← initWithReport dir policy with
  | .error e => return .error e
  | .ok (eng, _) => return .ok eng

/-- Retrieves and verifies object bytes + entryMetadata, using the bounded segment cache or sequential offset read. -/
def getObject {policy : StoragePolicy} (e : BucketEngine policy) (key : ObjectKey) :
    IO (Except String (ByteArray × BucketEntryMeta policy.segmentSize × BucketEngine policy)) := do
  match e.objects[key]? with
  | none => return .error s!"object not found"
  | some entryMeta =>
    let segId := entryMeta.location.segment
    let segPath := packPath e.dir segId
    let (frameBytesRes, nextCache) ←
      if policy.segmentCacheCapacity == 0 then
        let res ← readAtOffset segPath entryMeta.location.offset entryMeta.location.length
        pure (res, e.cache)
      else
        match e.cache.lookup segId.val with
        | some segBytes =>
          let slice := segBytes.extract entryMeta.location.offset (entryMeta.location.offset + entryMeta.location.length)
          pure (.ok slice, e.cache)
        | none =>
          try
            let segBytes ← IO.FS.readBinFile segPath
            let c' := e.cache.insert segId.val segBytes
            let slice := segBytes.extract entryMeta.location.offset (entryMeta.location.offset + entryMeta.location.length)
            pure (.ok slice, c')
          catch err =>
            pure (.error s!"read segment {segPath} failed: {err}", e.cache)
    match frameBytesRes with
    | .error err => return .error err
    | .ok frameBytes =>
      match decodeFrameAt policy .segment frameBytes 0 with
      | .error err => return .error s!"corrupt segment frame: {repr err}"
      | .ok (frame, _) =>
        match decodeBucketSegmentRecordAt frame.payload 0 with
        | .error err => return .error s!"corrupt segment record: {repr err}"
        | .ok (rec, _) =>
          if rec.key != key then
            return .error "segment record key mismatch"
          if sha256 rec.payload != key.digest then
            return .error "SHA-256 integrity verification failed"
          return .ok (rec.payload, entryMeta, { e with cache := nextCache })

/-- Stores or deduplicates an object with explicit byte-equality verification against hash collisions. -/
def putObject {policy : StoragePolicy} (e : BucketEngine policy)
    (data : ByteArray) (mime : MimeType) :
    IO (Except String (ObjectKey × BucketEntryMeta policy.segmentSize × Bool × BucketEngine policy)) := do
  if data.size > policy.maxImageBytes then
    return .error s!"object size {data.size} exceeds maxImageBytes {policy.maxImageBytes}"
  let digest := sha256 data
  let candidates := (e.byDigest[digest]?).getD #[]
  let mut cur := e
  for candKey in candidates do
    match ← cur.getObject candKey with
    | .ok (existingBytes, existingMeta, cur') =>
      cur := cur'
      if existingBytes == data then
        return .ok (candKey, existingMeta, false, cur)
    | .error _ => pure ()
  -- Either new digest or explicit SHA-256 collision: allocate new ObjectKey
  let newKey : ObjectKey := { digest := digest, tag := ⟨candidates.size.toUInt64⟩ }
  let segRec : BucketSegmentRecord := { key := newKey, mime := mime, payload := data }
  let recPayload := encodeBucketSegmentRecord segRec
  let frameSize := frameOverhead + recPayload.size
  if frameSize > policy.segmentSize then
    return .error s!"object frame size {frameSize} exceeds segmentSize {policy.segmentSize}"
  else
    let curSegUsed := (cur.segments[cur.activeSeg]?.map (·.used)).getD 0
    let (targetSegId, targetUsed, nextSegId') :=
      if curSegUsed + frameSize ≤ policy.segmentSize then
        (cur.activeSeg, curSegUsed, cur.nextSegId)
      else
        (cur.nextSegId, 0, ⟨cur.nextSegId.val + 1⟩)
    let p := packPath cur.dir targetSegId
    match ← appendFrame p targetUsed policy .segment 1 ⟨0⟩ ⟨0⟩ recPayload with
    | .error err => return .error err
    | .ok (off, written) =>
      if hBound : off + written ≤ policy.segmentSize ∧ 0 < written then
        let loc : ObjectLocation policy.segmentSize :=
          { segment := targetSegId, offset := off, length := written
            validBounds := hBound.1, nonEmpty := hBound.2 }
        let entryMeta : BucketEntryMeta policy.segmentSize :=
          { key := newKey
            location := loc
            mime := mime
            crc32 := crc32 data
            byteSize := data.size
            refCount := 0 }
        let prevSeg := (cur.segments[targetSegId]?).getD
          { id := targetSegId, used := 0, used_le := Nat.zero_le _, live := #[] }
        let updatedSeg : SegmentMeta policy.segmentSize :=
          { id := targetSegId, used := off + written, used_le := hBound.1, live := prevSeg.live.push loc }
        let cur' : BucketEngine policy :=
          { cur with
            objects := cur.objects.insert newKey entryMeta
            byDigest := cur.byDigest.insert digest (candidates.push newKey)
            segments := cur.segments.insert targetSegId updatedSeg
            activeSeg := targetSegId
            nextSegId := nextSegId'
            cache := cur.cache.invalidate targetSegId.val }
        match ← writeManifest cur' with
        | .error err => return .error err
        | .ok () => return .ok (newKey, entryMeta, true, cur')
      else
        return .error "written frame exceeded segmentSize"

def setRefCount {policy : StoragePolicy} (e : BucketEngine policy) (key : ObjectKey) (n : Nat) :
    BucketEngine policy :=
  match e.objects[key]? with
  | none => e
  | some entryMeta => { e with objects := e.objects.insert key { entryMeta with refCount := n } }

def incRef {policy : StoragePolicy} (e : BucketEngine policy) (key : ObjectKey) : BucketEngine policy :=
  match e.objects[key]? with
  | none => e
  | some entryMeta => { e with objects := e.objects.insert key { entryMeta with refCount := entryMeta.refCount + 1 } }

def decRef {policy : StoragePolicy} (e : BucketEngine policy) (key : ObjectKey) : BucketEngine policy :=
  match e.objects[key]? with
  | none => e
  | some entryMeta =>
    let nextRc := if entryMeta.refCount > 0 then entryMeta.refCount - 1 else 0
    { e with objects := e.objects.insert key { entryMeta with refCount := nextRc } }

/-- Reclaims unreferenced (`refCount == 0`) objects that are not pinned by active readers. -/
def gcStep {policy : StoragePolicy} (e : BucketEngine policy)
    (pinned : ObjectKey → Bool := fun _ => false) : BucketEngine policy × Nat :=
  let (liveObjs, liveByD, removed) := e.objects.foldl
    (fun (acc : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize) ×
                 Std.ExtTreeMap Sha256Digest (Array ObjectKey) × Nat) k entryMeta =>
      if shouldKeepObject pinned k entryMeta then
        let arr := (acc.2.1[k.digest]?).getD #[]
        (acc.1.insert k entryMeta, acc.2.1.insert k.digest (arr.push k), acc.2.2)
      else
        (acc.1, acc.2.1, acc.2.2 + 1))
    (∅, ∅, 0)
  ({ e with objects := liveObjs, byDigest := liveByD }, removed)

/-- Compacts live or pinned objects into fresh segment(s), updates manifest atomically,
    and deletes old pack files. -/
def compact {policy : StoragePolicy} (e : BucketEngine policy)
    (pinned : ObjectKey → Bool := fun _ => false) : IO (Except String (BucketEngine policy)) := do
  let oldSegIds := e.segments.foldl (fun acc sid _ => acc.push sid) #[]
  let mut curSegId := e.nextSegId
  let mut nextId : SegmentId := ⟨e.nextSegId.val + 1⟩
  let mut curUsed : Nat := 0
  let mut newObjs : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize) := ∅
  let mut newByD : Std.ExtTreeMap Sha256Digest (Array ObjectKey) := ∅
  let mut newSegs : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize) :=
    (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert curSegId
      { id := curSegId, used := 0, used_le := Nat.zero_le _, live := #[] }
  let mut eng := e
  let liveList := e.objects.foldl (fun acc _ entryMeta => acc.push entryMeta) #[]
  for entryMeta in liveList do
    if shouldKeepObject pinned entryMeta.key entryMeta then
      match ← eng.getObject entryMeta.key with
      | .error err => return .error err
      | .ok (bytes, _, eng') =>
        eng := eng'
        let segRec : BucketSegmentRecord := { key := entryMeta.key, mime := entryMeta.mime, payload := bytes }
        let recPayload := encodeBucketSegmentRecord segRec
        let frameSize := frameOverhead + recPayload.size
        if curUsed + frameSize > policy.segmentSize then
          curSegId := nextId
          nextId := ⟨nextId.val + 1⟩
          curUsed := 0
          newSegs := newSegs.insert curSegId
            { id := curSegId, used := 0, used_le := Nat.zero_le _, live := #[] }
        match ← appendFrame (packPath eng.dir curSegId) curUsed policy .segment 1 ⟨0⟩ ⟨0⟩ recPayload with
        | .error err => return .error err
        | .ok (off, written) =>
          if hBound : off + written ≤ policy.segmentSize ∧ 0 < written then
            let loc : ObjectLocation policy.segmentSize :=
              { segment := curSegId, offset := off, length := written
                validBounds := hBound.1, nonEmpty := hBound.2 }
            let newMeta : BucketEntryMeta policy.segmentSize :=
              { entryMeta with location := loc }
            newObjs := newObjs.insert entryMeta.key newMeta
            let arr := (newByD[entryMeta.key.digest]?).getD #[]
            newByD := newByD.insert entryMeta.key.digest (arr.push entryMeta.key)
            let prevSeg := (newSegs[curSegId]?).getD
              { id := curSegId, used := 0, used_le := Nat.zero_le _, live := #[] }
            newSegs := newSegs.insert curSegId
              { id := curSegId, used := off + written, used_le := hBound.1, live := prevSeg.live.push loc }
            curUsed := off + written
          else
            return .error "compaction frame exceeded segmentSize"
  let eng' : BucketEngine policy :=
    { eng with
      objects := newObjs
      byDigest := newByD
      segments := newSegs
      activeSeg := curSegId
      nextSegId := nextId
      cache := BoundedCache.empty policy.segmentCacheCapacity }
  match ← writeManifest eng' with
  | .error err => return .error err
  | .ok () =>
    for oldId in oldSegIds do
      if oldId != curSegId then
        try IO.FS.removeFile (packPath eng.dir oldId) catch _ => pure ()
    return .ok eng'

end BucketEngine

end Leaf.Storage
