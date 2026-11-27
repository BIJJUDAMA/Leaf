import Leaf.View
import Leaf.Upload
import Leaf.Storage.Migration

open Leaf
open Leaf.Core
open Leaf.Storage

private def check (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"Assertion failed: {msg}"

private def rmTree (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then
    IO.FS.removeDirAll p

def main : IO Unit := do
  -- 1. Cursor & digest hex roundtrip + View rendering
  let fk : FeedKey := ⟨1795762959, ⟨42⟩⟩
  check (decodeCursor? (encodeCursor fk) == some fk) "Cursor roundtrip"
  let d := sha256 "leaf".toUTF8
  check (hexToDigest? (digestToHex d) == some d) "Digest hex roundtrip"

  -- 2. Legacy migration test against copy of data/posts.db and data/images/2
  let migRoot : System.FilePath := ".lake/tmp_app_mig"
  rmTree migRoot
  IO.FS.createDirAll (migRoot / "images")
  if ← (System.FilePath.mk "data/posts.db").pathExists then
    let postsJson ← IO.FS.readBinFile "data/posts.db"
    IO.FS.writeBinFile (migRoot / "posts.db") postsJson
    if ← (System.FilePath.mk "data/images/2").pathExists then
      let img2 ← IO.FS.readBinFile "data/images/2"
      IO.FS.writeBinFile (migRoot / "images/2") img2
    let pol : StoragePolicy := {}
    let .ok (store, _, migrated) ← openAndMigrate migRoot pol
      | throw <| IO.userError "openAndMigrate failed"
    check (migrated == 2) s!"Expected 2 migrated posts, got {migrated}"
    let feed ← store.queryFeed none 10
    check (feed.size == 2) "Migrated 2 posts visible in feed"
    let some p2 := feed.find? (fun p => p.caption.isEmpty) | throw <| IO.userError "missing migrated image post"
    let some ref2 := p2.image | throw <| IO.userError "migrated post 2 missing image"
    let .ok (gotImg, _) ← store.getImage ref2.key | throw <| IO.userError "getImage on migrated image"
    let origImg ← IO.FS.readBinFile "data/images/2"
    check (gotImg == origImg) "Migrated image bytes match data/images/2"
    -- Reopen: should NOT re-migrate
    let .ok (store2, report2, migrated2) ← openAndMigrate migRoot pol
      | throw <| IO.userError "second openAndMigrate failed"
    check (migrated2 == 0 && report2.recoveredPosts == 2) "Second open skips migration and recovers 2 posts"
    let html := page (← store2.queryFeed none 10) none 10 "ok"
    check ((html.splitOn "/objects/").length > 1) "Rendered HTML includes /objects/ image URL"
  rmTree migRoot

  -- 3. Benchmark: 50 transactional creates (with 1 KiB images) + feed query + compact
  let benchRoot : System.FilePath := ".lake/tmp_app_bench"
  rmTree benchRoot
  let pol : StoragePolicy := {}
  let .ok (bStore, _, _) ← openAndMigrate benchRoot pol | throw <| IO.userError "bench open"
  let payload := ByteArray.mk (Array.replicate 1024 0x5A)
  let t0 ← IO.monoMsNow
  for i in [0 : 50] do
    let .ok d ← pure (validateDraft pol { author := "bench", title := some s!"Post {i}", caption := s!"body {i}" })
      | throw <| IO.userError "bench draft"
    let .ok _ ← bStore.createPostWithImage d (some (payload, .png)) (1000 + i).toInt64
      | throw <| IO.userError "bench create"
  let t1 ← IO.monoMsNow
  let page1 ← bStore.queryFeed none 20
  check (page1.size == 20) "Bench feed page size 20"
  let .ok () ← bStore.compact | throw <| IO.userError "bench compact"
  let t2 ← IO.monoMsNow
  rmTree benchRoot
  IO.println s!"AppTests: passed (50 tx+dedup-image writes: {t1 - t0}ms, query+compact: {t2 - t1}ms)"
