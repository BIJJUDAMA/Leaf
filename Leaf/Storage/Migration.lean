import Leaf.Database
import Leaf.Storage.StoreEngine

namespace Leaf.Storage

open Leaf.Core

private def parseLegacyMime (m? : Option String) (bytes : ByteArray) : Option MimeType :=
  match detectMimeType bytes with
  | some m => some m
  | none =>
    match m? with
    | some "image/jpeg" => some .jpeg
    | some "image/png"  => some .png
    | some "image/webp" => some .webp
    | some "image/gif"  => some .gif
    | _ => none

/-- Opens and recovers the store at `rootDir`, automatically migrating legacy `posts.db` + `images/`
    if `database/manifest.bin` did not previously exist. Legacy files are preserved untouched. -/
def openAndMigrate (rootDir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (StoreEngine policy × RecoveryReport × Nat)) := do
  let manifestFile := rootDir / "database" / "manifest.bin"
  let legacyDbFile := rootDir / "posts.db"
  let hadManifest ← manifestFile.pathExists
  match ← StoreEngine.recoverStore rootDir policy with
  | .error e => return .error e
  | .ok (store, report) =>
    if hadManifest || !(← legacyDbFile.pathExists) then
      return .ok (store, report, 0)
    try
      let legacy ← Leaf.Database.read legacyDbFile
      let mut imported := 0
      for lp in legacy.posts do
        let mut img? : Option (ByteArray × MimeType) := none
        let mut imgRaw? : Option ByteArray := none
        if lp.mime.isSome then
          let imgPath := rootDir / "images" / toString lp.id
          if ← imgPath.pathExists then
            let bytes ← IO.FS.readBinFile imgPath
            if let some mime := parseLegacyMime lp.mime bytes then
              img? := some (bytes, mime)
              imgRaw? := some bytes
        let createdSec : Int64 := (lp.created.toInt?.getD 0).toInt64
        let rawDraft : PostDraft :=
          { author := "journal"
            title := none
            caption := lp.caption
            tags := #[]
            imageBytes := imgRaw? }
        match validateDraft policy rawDraft with
        | .error e => return .error s!"legacy migration validation failed for post {lp.id}: {repr e}"
        | .ok validDraft =>
          match ← store.createPostWithImage validDraft img? createdSec with
          | .error e => return .error s!"legacy migration commit failed for post {lp.id}: {e}"
          | .ok _ => imported := imported + 1
      let _ ← store.checkpoint
      return .ok (store, report, imported)
    catch e =>
      return .error s!"legacy migration failed: {e}"

end Leaf.Storage
