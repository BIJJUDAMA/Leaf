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
  let testRoot : System.FilePath := ".lake/tmp_recovery_tests"
  rmTree testRoot

  let pol : StoragePolicy :=
    { segmentSize := 512
      maxImageBytes := 350
      segmentCacheCapacity := 2
      imageFitsSegment := by decide
      frameFitsUInt32 := by decide }

  let img1 := ByteArray.mk (Array.replicate 140 0x31)
  let imgOrphan := ByteArray.mk (Array.replicate 100 0x7E)
  let .ok d1 := validateDraft pol { author := "alice", title := some "Survives", caption := "committed" }
    | throw <| IO.userError "d1"
  let .ok d2 := validateDraft pol { author := "bob", title := some "AfterCrash", caption := "appended" }
    | throw <| IO.userError "d2"
  let .ok dUncommitted := validateDraft pol { author := "eve", title := some "Ghost", caption := "uncommitted" }
    | throw <| IO.userError "dUncommitted"

  let mut p1Id : PostId := ⟨0⟩
  let mut k1? : Option ObjectKey := none

  -- 1. Commit p1, then inject:
  --    (a) an uncommitted transaction (beginTx + allocObject + putPost WITHOUT commitTx)
  --    (b) truncated/corrupt trailing bytes in wal-000001.bin
  --    (c) truncated/corrupt trailing bytes in pack-000001.bin
  do
    let .ok store ← StoreEngine.openStore testRoot pol | throw <| IO.userError "openStore 1"
    let .ok p1 ← store.createPostWithImage d1 (some (img1, .png)) 100 | throw <| IO.userError "p1"
    p1Id := p1.id
    k1? := p1.image.map (·.key)

    -- Inject uncommitted tx + orphan blob directly into WAL & Bucket
    store.mutex.atomically do
      let inner ← get
      let txId : TxId := ⟨99⟩
      let seq1 : SeqNo := ⟨inner.db.state.lastSeq.val + 1⟩
      let .ok db1 ← inner.db.appendWalFrame txId seq1 .beginTx | throw <| IO.userError "inj begin"
      let .ok (orphanKey, _, _, b1) ← inner.bucket.putObject imgOrphan .jpeg | throw <| IO.userError "inj put"
      let ghostPost : Post :=
        { id := ⟨999⟩, author := dUncommitted.author, title := dUncommitted.title
          caption := dUncommitted.caption, tags := #[], createdAt := 500
          updatedAt := none, version := ⟨seq1.val + 1⟩
          image := some { key := orphanKey, mime := .jpeg, byteSize := imgOrphan.size.toUInt32 } }
      let .ok db2 ← db1.appendWalFrame txId ⟨seq1.val + 1⟩ (.putPost ghostPost) | throw <| IO.userError "inj putPost"
      -- Intentionally NO commitTx!
      set ({ inner with db := db2, bucket := b1 } : StoreInner pol)

    -- Inject corrupt trailing bytes into WAL and pack segment
    let walFile := testRoot / "database" / "wal" / "wal-000001.bin"
    let hWal ← IO.FS.Handle.mk walFile .append
    hWal.write (ByteArray.mk #[0x4C, 0x46, 0x57, 0x31, 0xFF, 0x00, 0x13])
    hWal.flush

    let segFile := testRoot / "bucket" / "segments" / "pack-000001.bin"
    let hSeg ← IO.FS.Handle.mk segFile .append
    hSeg.write (ByteArray.mk #[0x4C, 0x46, 0x53, 0x31, 0xDE, 0xAD])
    hSeg.flush

  -- 2. Recover and verify: committed post intact, uncommitted post absent, tails repaired, orphan reclaimed
  do
    let .ok (store, report) ← StoreEngine.recoverStore testRoot pol | throw <| IO.userError "recoverStore"
    check (report.recoveredPosts == 1) s!"Expected 1 recovered post, got {report.recoveredPosts}"
    check (report.discardedWalTailBytes == 7) s!"Expected 7 discarded WAL bytes, got {report.discardedWalTailBytes}"
    check (report.repairedSegmentBytes == 6) s!"Expected 6 repaired segment bytes, got {report.repairedSegmentBytes}"
    check (report.reclaimedOrphans == 1) s!"Expected 1 reclaimed orphan, got {report.reclaimedOrphans}"
    check ((← store.getPost ⟨999⟩) == none) "Uncommitted post must not be visible"
    let some p1 ← store.getPost p1Id | throw <| IO.userError "missing p1 after recovery"
    check (p1.caption == "committed") "Committed post intact after recovery"

    -- Append another post after tail repair and verify it survives reopen
    let .ok p2 ← store.createPostWithImage d2 none 200 | throw <| IO.userError "p2 after recovery"
    let .ok (store2, _) ← StoreEngine.recoverStore testRoot pol | throw <| IO.userError "reopen after repair"
    check ((← store2.getPost p2.id).isSome) "Post appended after WAL tail repair persisted"

    -- 3. Snapshot isolation & active-reader GC pinning
    let snap ← store2.beginSnapshot
    let some k1 := k1? | throw <| IO.userError "k1"
    -- Delete p1 and run GC + compact while snapshot `snap` is active
    let .ok () ← store2.deletePost p1Id | throw <| IO.userError "delete p1"
    let removedWhilePinned ← store2.runGC
    check (removedWhilePinned == 0) "Pinned image must not be collected while snapshot is active"
    let .ok () ← store2.compact | throw <| IO.userError "compact while pinned"
    check (snap.db.getPost p1Id == some p1) "Snapshot still sees p1 after concurrent delete"
    let .ok (gotBytes, _) ← store2.getImage k1 | throw <| IO.userError "getImage still succeeds while pinned"
    check (gotBytes == img1) "Pinned image bytes intact"
    -- Release snapshot, then GC must reclaim the now-unpinned image
    store2.endSnapshot snap
    let removedAfterRelease ← store2.runGC
    check (removedAfterRelease == 1) "Unpinned image reclaimed after endSnapshot"

    -- 4. Multi-task concurrent readers + writer
    let writerTask ← IO.asTask (prio := .default) do
      for i in [0 : 6] do
        let .ok d ← pure (validateDraft pol { author := "worker", title := some s!"T{i}", caption := s!"msg-{i}" })
          | throw <| IO.userError "draft"
        let .ok _ ← store2.createPostWithImage d none (1000 + i).toInt64 | throw <| IO.userError "concurrent create"
      pure ()
    let mut readerTasks : Array (Task (Except IO.Error Unit)) := #[]
    for _ in [0 : 4] do
      let t ← IO.asTask (prio := .default) do
        for _ in [0 : 10] do
          store2.withSnapshot fun s => do
            let feed := s.db.queryFeed none 20
            -- Every post returned in feed must exist in snapshot
            for p in feed do
              if s.db.getPost p.id != some p then
                throw <| IO.userError "snapshot feed/getPost inconsistency"
      readerTasks := readerTasks.push t
    IO.ofExcept (← IO.wait writerTask)
    for t in readerTasks do
      IO.ofExcept (← IO.wait t)
    let finalFeed ← store2.queryFeed none 20
    check (finalFeed.size == 7) s!"Expected 7 posts after concurrent writes (1 + 6), got {finalFeed.size}"

  rmTree testRoot
  IO.println "RecoveryTests: all crash recovery, pinning & concurrency tests passed"
