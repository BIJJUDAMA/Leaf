import Leaf.Storage.StoreEngine

open Leaf.Core
open Leaf.Storage

private def check (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"Assertion failed: {msg}"

private def rmTree (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then
    IO.FS.removeDirAll p

def main : IO Unit := do
  let testRoot : System.FilePath := ".lake/tmp_storage_tests"
  rmTree testRoot

  let pol : StoragePolicy :=
    { segmentSize := 512
      maxImageBytes := 350
      segmentCacheCapacity := 2
      imageFitsSegment := by decide
      frameFitsUInt32 := by decide }

  -- 1. Open store, create two posts with deduplicated image, verify persistence across reopen
  let img1 := ByteArray.mk (Array.replicate 180 0x41)
  let img2 := ByteArray.mk (Array.replicate 180 0x42)
  let .ok d1 := validateDraft pol { author := "alice", title := some "First", caption := "hello" }
    | throw <| IO.userError "d1"
  let .ok d2 := validateDraft pol { author := "bob", title := some "Second", caption := "world" }
    | throw <| IO.userError "d2"
  let .ok d3 := validateDraft pol { author := "carol", title := some "Third", caption := "dedup" }
    | throw <| IO.userError "d3"

  let mut p1Id : PostId := ⟨0⟩
  let mut p2Id : PostId := ⟨0⟩
  let mut p3Id : PostId := ⟨0⟩
  let mut k1? : Option ObjectKey := none
  let mut k2? : Option ObjectKey := none

  do
    let .ok store ← StoreEngine.openStore testRoot pol | throw <| IO.userError "openStore 1"
    let .ok p1 ← store.createPostWithImage d1 (some (img1, .png)) 100
      | throw <| IO.userError "create p1"
    let .ok p2 ← store.createPostWithImage d2 (some (img2, .jpeg)) 200
      | throw <| IO.userError "create p2"
    let .ok p3 ← store.createPostWithImage d3 (some (img1, .png)) 300
      | throw <| IO.userError "create p3 (dedup)"
    p1Id := p1.id; p2Id := p2.id; p3Id := p3.id
    k1? := p1.image.map (·.key)
    k2? := p2.image.map (·.key)
    check (k1? == p3.image.map (·.key)) "Identical image bytes deduplicated to same ObjectKey"
    let some k1 := k1? | throw <| IO.userError "missing k1"
    let some m1 ← store.getImageMeta k1 | throw <| IO.userError "missing meta 1"
    check (m1.refCount == 2) "Deduplicated object has refCount 2"
    -- Segment rolling: 180-byte images + overhead > 256 -> pack-000001.bin and pack-000002.bin exist
    check (← (testRoot / "bucket" / "segments" / "pack-000001.bin").pathExists) "pack-000001.bin exists"
    check (← (testRoot / "bucket" / "segments" / "pack-000002.bin").pathExists) "pack-000002.bin exists"

  -- 2. Reopen from disk and verify WAL replay + object reads + cursor pagination
  do
    let .ok store ← StoreEngine.openStore testRoot pol | throw <| IO.userError "openStore 2"
    let some p1 ← store.getPost p1Id | throw <| IO.userError "reopen p1"
    let some p2 ← store.getPost p2Id | throw <| IO.userError "reopen p2"
    let some p3 ← store.getPost p3Id | throw <| IO.userError "reopen p3"
    check (p1.caption == "hello" && p2.caption == "world" && p3.caption == "dedup") "Posts survived reopen"
    let page1 ← store.queryFeed none 2
    check (page1.size == 2 && page1[0]!.id == p3Id && page1[1]!.id == p2Id) "Feed page 1 ordered desc"
    let page2 ← store.queryFeed (some (FeedKey.ofPost page1[1]!)) 2
    check (page2.size == 1 && page2[0]!.id == p1Id) "Feed page 2 cursor pagination"
    let some k1 := k1? | throw <| IO.userError "k1"
    let some k2 := k2? | throw <| IO.userError "k2"
    let .ok (got1, mime1) ← store.getImage k1 | throw <| IO.userError "getImage k1"
    let .ok (got2, mime2) ← store.getImage k2 | throw <| IO.userError "getImage k2"
    check (got1 == img1 && mime1 == .png) "Image 1 bytes + mime intact"
    check (got2 == img2 && mime2 == .jpeg) "Image 2 bytes + mime intact"

    -- 3. Aborted transaction leaves post invisible and orphan image collectible by GC
    let orphanBytes := ByteArray.mk (Array.replicate 90 0x4F)
    let .ok orphanKey ← store.stageAndAbort orphanBytes .webp | throw <| IO.userError "stageAndAbort"
    let some orphanMeta ← store.getImageMeta orphanKey | throw <| IO.userError "orphan meta"
    check (orphanMeta.refCount == 0) "Orphan image has refCount 0"
    let removed1 ← store.runGC
    check (removed1 == 1) "GC reclaimed 1 orphan image"

    -- 4. Update & Delete + Checkpoint + Compact
    let .ok patch1 := validatePostPatch pol p1 { caption? := some "hello-v2", imagePatch := .keep }
      | throw <| IO.userError "patch1"
    let .ok p1' ← store.updatePostWithImage p1Id patch1 none 400 | throw <| IO.userError "update p1"
    check (p1'.caption == "hello-v2") "updatePostWithImage updated caption"
    let .ok () ← store.deletePost p2Id | throw <| IO.userError "delete p2"
    check ((← store.getPost p2Id) == none) "Deleted post excluded"
    let .ok () ← store.checkpoint | throw <| IO.userError "checkpoint"
    let .ok () ← store.compact | throw <| IO.userError "compact"

  -- 3. Reopen after checkpoint + compaction
  do
    let .ok store ← StoreEngine.openStore testRoot pol | throw <| IO.userError "openStore 3"
    let some p1 ← store.getPost p1Id | throw <| IO.userError "post-compact p1"
    check (p1.caption == "hello-v2") "Updated post persisted across compact"
    check ((← store.getPost p2Id) == none) "Deleted post still excluded after compact"
    let some k1 := k1? | throw <| IO.userError "k1"
    let .ok (got1, _) ← store.getImage k1 | throw <| IO.userError "post-compact getImage k1"
    check (got1 == img1) "Live image survived bucket compaction"
    let some k2 := k2? | throw <| IO.userError "k2"
    let res2 ← store.getImage k2
    check (match res2 with | .error _ => true | .ok _ => false) "Unreferenced image 2 reclaimed by GC+compact"

  rmTree testRoot
  IO.println "StorageTests: all persistent DB/Bucket/Tx tests passed"
