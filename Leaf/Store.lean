import Leaf.Upload
import Leaf.Database
import Leaf.Bucket
import Std.Sync.Mutex
import Std.Time

namespace Leaf
open System Lean

structure Store where
  path : FilePath
  bucket : Bucket
  database : Std.Mutex Database
  writerLock : IO.FS.Handle

private def importLegacy (root : FilePath) (bucket : Bucket) : IO Database := do
  let mut posts := #[]
  for entry in ← root.readDir do
    if let some id := entry.fileName.toNat? then
      let json ← IO.FS.readFile (entry.path / "post.json")
      let post : Post ← IO.ofExcept (Json.parse json >>= fromJson?)
      unless post.id == id && entry.fileName == toString id do
        throw <| IO.userError "Invalid legacy post directory"
      if post.mime.isSome then
        bucket.put id (← IO.FS.readBinFile (entry.path / "image"))
      posts := posts.push post
  return ⟨1, posts.qsort (fun a b => a.id < b.id)⟩

def openStore (root : FilePath) : IO Store := do
  IO.FS.createDirAll root
  let lock ← IO.FS.Handle.mk (root / "writer.lock") .append
  unless ← lock.tryLock do throw <| IO.userError "Leaf database is already open"
  let path := root / "posts.db"
  let bucket ← Bucket.openAt (root / "images")
  let db ← if ← path.pathExists then Database.read path else do
    let imported ← importLegacy root bucket
    imported.commit path
    pure imported
  return ⟨path, bucket, ← Std.Mutex.new db, lock⟩

def Store.publish (store : Store) (draft : Draft) : IO Unit := store.database.atomically do
  let db ← get
  let id := db.nextId
  let mime := imageType draft.image
  if mime.isSome then store.bucket.put id draft.image
  else
    -- Reclaim an image left by an interrupted insert that used this key.
    let orphan := store.bucket.directory / toString id
    if ← orphan.pathExists then IO.FS.removeFile orphan
  let post := Post.mk id draft.caption (toString (← Std.Time.Timestamp.now)) mime
  let updated := { db with posts := db.posts.push post }
  updated.commit store.path
  set updated

def Store.snapshot (store : Store) : IO (Array Post) :=
  store.database.atomically do return (← get).posts

def Store.image (store : Store) (id : Nat) : IO (Option (String × ByteArray)) := do
  let post ← store.database.atomically do return (← get).lookup id
  let some mime := post.bind (·.mime) | return none
  return some (mime, ← store.bucket.get id)

end Leaf
