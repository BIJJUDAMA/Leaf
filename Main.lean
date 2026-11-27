import Std.Http
import Lean
import Leaf.Core.Schema
import Leaf.View
import Leaf.Upload
import Leaf.Storage.Migration

open Std Async
open Std Http Server
open Lean
open Leaf
open Leaf.Core
open Leaf.Storage

private def queryParam? (uri : String) (name : String) : Option String :=
  match uri.splitOn "?" with
  | [_, qs] =>
    (qs.splitOn "&").findSome? fun kv =>
      match kv.splitOn "=" with
      | [k, v] => if k == name then some v else none
      | _ => none
  | _ => none

private def pathOnly (uri : String) : String :=
  (uri.splitOn "?").head?.getD uri

private def formatBytes (n : Nat) : String :=
  if n < 1024 then s!"{n} B"
  else if n < 1024 * 1024 then s!"{n / 1024} KiB"
  else s!"{n / (1024 * 1024)} MiB"

private def formatStats (s : StoreStats) : String :=
  s!"Posts: {s.postCount} · Tombstones: {s.tombstoneCount} · WAL #{s.walId} ({formatBytes s.walBytes}) · Checkpoint #{s.ckptId} · Images: {s.objectCount} ({s.unreferencedObjects} unreferenced) · Segments: {s.segmentCount} ({formatBytes s.segmentBytes})"

private def parseMaintNotice (uri : String) : Option String :=
  match queryParam? uri "maint" with
  | some "checkpoint" =>
    let wb := (queryParam? uri "wb").bind String.toNat? |>.getD 0
    let wa := (queryParam? uri "wa").bind String.toNat? |>.getD 0
    let wid1 := queryParam? uri "w1" |>.getD "?"
    let wid2 := queryParam? uri "w2" |>.getD "?"
    let c1 := queryParam? uri "c1" |>.getD "?"
    let c2 := queryParam? uri "c2" |>.getD "?"
    some s!"Checkpoint complete: WAL #{wid1} ({formatBytes wb}) → WAL #{wid2} ({formatBytes wa}) · Checkpoint #{c1} → #{c2}"
  | some "gc" =>
    let rem := (queryParam? uri "rem").bind String.toNat? |>.getD 0
    let ob := (queryParam? uri "ob").bind String.toNat? |>.getD 0
    let oa := (queryParam? uri "oa").bind String.toNat? |>.getD 0
    some s!"GC complete: Stored images {ob} → {oa} ({rem} reclaimed)"
  | some "compact" =>
    let tb := (queryParam? uri "tb").bind String.toNat? |>.getD 0
    let ta := (queryParam? uri "ta").bind String.toNat? |>.getD 0
    let sb := (queryParam? uri "sb").bind String.toNat? |>.getD 0
    let sa := (queryParam? uri "sa").bind String.toNat? |>.getD 0
    let bb := (queryParam? uri "bb").bind String.toNat? |>.getD 0
    let ba := (queryParam? uri "ba").bind String.toNat? |>.getD 0
    some s!"Compaction complete: Tombstones {tb} → {ta} · Segments {sb} ({formatBytes bb}) → {sa} ({formatBytes ba})"
  | _ => none

private def postToJson (p : Leaf.Core.Post) : Json :=
  let imgJson : Json := match p.image with
    | none => Json.null
    | some ref => Json.mkObj
      [ ("url", Json.str s!"/objects/{digestToHex ref.key.digest}/{ref.key.tag.val}")
      , ("mime", Json.str ref.mime.toString)
      , ("byteSize", Json.num ref.byteSize.toNat) ]
  Json.mkObj
    [ ("id", Json.num p.id.val.toNat)
    , ("author", Json.str p.author)
    , ("title", match p.title with | some t => Json.str t | none => Json.null)
    , ("caption", Json.str p.caption)
    , ("createdAt", Json.num p.createdAt.toInt)
    , ("updatedAt", match p.updatedAt with | some u => Json.num u.toInt | none => Json.null)
    , ("version", Json.num p.version.val.toNat)
    , ("image", imgJson) ]

structure App where
  policy : StoragePolicy
  store  : StoreEngine policy

instance : Handler App where
  onRequest app req := do
    let uri := toString req.line.uri
    let path := pathOnly uri
    let nowSec : Int64 := (← IO.monoMsNow).toInt64 / 1000
    match req.line.method with
    | .get =>
      if path == "/healthz" then
        Response.ok |>.text "ok"
      else if path == "/" then
        let cursor? := (queryParam? uri "cursor").bind decodeCursor?
        let limit := ((queryParam? uri "limit").bind String.toNat?).getD 10
        let limit := if limit == 0 then 10 else min limit 100
        let (rows, nextCursor?) ← app.store.withSnapshot fun snap => do
          let fetched := snap.db.queryFeed cursor? (limit + 1)
          let hasMore := fetched.size > limit
          let pageRows := if hasMore then fetched.extract 0 limit else fetched
          let nextC := if hasMore then pageRows.back?.map FeedKey.ofPost else none
          return (pageRows, nextC)
        let stats ← app.store.getStats
        let notice? := parseMaintNotice uri
        Response.ok |>.html (page rows nextCursor? limit (formatStats stats) notice?)
      else if path == "/docs" then
        Response.ok |>.html docsPage
      else if path == "/api/posts" then
        let cursor? := (queryParam? uri "cursor").bind decodeCursor?
        let limit := ((queryParam? uri "limit").bind String.toNat?).getD 20
        let limit := if limit == 0 then 20 else min limit 100
        let bodyJson ← app.store.withSnapshot fun snap => do
          let fetched := snap.db.queryFeed cursor? (limit + 1)
          let hasMore := fetched.size > limit
          let pageRows := if hasMore then fetched.extract 0 limit else fetched
          let nextC := if hasMore then (pageRows.back?.map FeedKey.ofPost).map encodeCursor else none
          return Json.mkObj
            [ ("posts", Json.arr (pageRows.map postToJson))
            , ("nextCursor", match nextC with | some c => Json.str c | none => Json.null) ]
        Response.ok |>.header! "Content-Type" "application/json" |>.text bodyJson.compress
      else if let ["", "api", "posts", idStr] := path.splitOn "/" then
        let some id := idStr.toNat? | return ← Response.badRequest |>.text "Invalid post ID."
        let post? ← app.store.withSnapshot fun snap => pure (snap.db.getPost ⟨id.toUInt64⟩)
        match post? with
        | none => Response.notFound |>.text "Post not found."
        | some p =>
          Response.ok |>.header! "Content-Type" "application/json" |>.text (postToJson p).compress
      else if let ["", "objects", hexStr, tagStr] := path.splitOn "/" then
        match hexToDigest? hexStr, tagStr.toNat? with
        | some digest, some tag =>
          let key : ObjectKey := { digest := digest, tag := ⟨tag.toUInt64⟩ }
          match ← app.store.getImage key with
          | .ok (bytes, mime) =>
            Response.ok |>.header! "Content-Type" mime.toString
              |>.header! "X-Content-Type-Options" "nosniff"
              |>.fromBytes bytes
          | .error _ => Response.notFound |>.text "Object unavailable."
        | _, _ => Response.badRequest |>.text "Invalid object key."
      else if let ["", "images", key] := path.splitOn "/" then
        let some id := key.toNat? | return ← Response.notFound |>.text "Image unavailable."
        let imgRef? ← app.store.withSnapshot fun snap =>
          pure ((snap.db.getPost ⟨id.toUInt64⟩).bind (·.image))
        match imgRef? with
        | none => Response.notFound |>.text "Image unavailable."
        | some ref =>
          match ← app.store.getImage ref.key with
          | .ok (bytes, mime) =>
            Response.ok |>.header! "Content-Type" mime.toString
              |>.header! "X-Content-Type-Options" "nosniff"
              |>.fromBytes bytes
          | .error _ => Response.notFound |>.text "Image unavailable."
      else
        Response.notFound |>.text "Page unavailable."
    | .post =>
      if path == "/posts" then
        let ct := ((req.line.headers.get? .contentType).map (·.value)).getD ""
        let payload : Option ByteArray ←
          try pure (some (← req.body.readAll (maximumSize := some (app.policy.maxImageBytes + 65536).toUInt64)))
          catch _ => pure none
        let some bytes := payload
          | return ← Response.badRequest |>.text "Upload incomplete or too large."
        match parseForm ct bytes app.policy.maxImageBytes with
        | .error msg => Response.badRequest |>.text msg
        | .ok draft =>
          let imgRaw? := if draft.image.isEmpty then none else some draft.image
          let imgTyped? := imgRaw?.bind fun b => (detectMimeType b).map (b, ·)
          let rawDraft : PostDraft :=
            { author := draft.author
              title := draft.title
              caption := draft.caption
              tags := #[]
              imageBytes := imgRaw? }
          match validateDraft app.policy rawDraft with
          | .error err => Response.badRequest |>.text s!"Invalid draft: {repr err}"
          | .ok validDraft =>
            match ← app.store.createPostWithImage validDraft imgTyped? nowSec with
            | .error err => Response.internalServerError |>.text err
            | .ok _ => Response.withStatus .seeOther |>.header! "Location" "/" |>.text ""
      else if let ["", "posts", idStr, "edit"] := path.splitOn "/" then
        let some id := idStr.toNat? | return ← Response.badRequest |>.text "Invalid post ID."
        let postId : PostId := ⟨id.toUInt64⟩
        let some existing ← app.store.getPost postId | return ← Response.notFound |>.text "Post not found."
        let ct := ((req.line.headers.get? .contentType).map (·.value)).getD ""
        let payload : Option ByteArray ←
          try pure (some (← req.body.readAll (maximumSize := some (app.policy.maxImageBytes + 65536).toUInt64)))
          catch _ => pure none
        let some bytes := payload
          | return ← Response.badRequest |>.text "Upload incomplete or too large."
        match parseEditForm ct bytes app.policy.maxImageBytes with
        | .error msg => Response.badRequest |>.text msg
        | .ok edit =>
          let imgPatch : ImagePatch :=
            if edit.removeImage then .remove
            else match edit.image? with
              | some b => .replace b
              | none => .keep
          let rawPatch : Leaf.Core.PostUpdate :=
            { author? := edit.author?
              title? := edit.title?
              caption? := edit.caption?
              tags? := none
              imagePatch := imgPatch }
          match validatePostPatch app.policy existing rawPatch with
          | .error err => Response.badRequest |>.text s!"Invalid update: {repr err}"
          | .ok validPatch =>
            let newImgTyped? := edit.image?.bind fun b => (detectMimeType b).map (b, ·)
            match ← app.store.updatePostWithImage postId validPatch newImgTyped? nowSec with
            | .error err => Response.internalServerError |>.text err
            | .ok _ => Response.withStatus .seeOther |>.header! "Location" "/" |>.text ""
      else if let ["", "posts", idStr, "delete"] := path.splitOn "/" then
        let some id := idStr.toNat? | return ← Response.badRequest |>.text "Invalid post ID."
        match ← app.store.deletePost ⟨id.toUInt64⟩ with
        | .error msg => Response.notFound |>.text msg
        | .ok () => Response.withStatus .seeOther |>.header! "Location" "/" |>.text ""
      else if path == "/admin/checkpoint" then
        let before ← app.store.getStats
        match ← app.store.checkpoint with
        | .error err => Response.internalServerError |>.text err
        | .ok () =>
          let after ← app.store.getStats
          let loc := s!"/?maint=checkpoint&wb={before.walBytes}&wa={after.walBytes}&w1={before.walId}&w2={after.walId}&c1={before.ckptId}&c2={after.ckptId}"
          Response.withStatus .seeOther |>.header! "Location" loc |>.text ""
      else if path == "/admin/gc" then
        let before ← app.store.getStats
        let removed ← app.store.runGC
        let after ← app.store.getStats
        let loc := s!"/?maint=gc&rem={removed}&ob={before.objectCount}&oa={after.objectCount}"
        Response.withStatus .seeOther |>.header! "Location" loc |>.text ""
      else if path == "/admin/compact" then
        let before ← app.store.getStats
        match ← app.store.compact with
        | .error err => Response.internalServerError |>.text err
        | .ok () =>
          let after ← app.store.getStats
          let loc := s!"/?maint=compact&tb={before.tombstoneCount}&ta={after.tombstoneCount}&sb={before.segmentCount}&sa={after.segmentCount}&bb={before.segmentBytes}&ba={after.segmentBytes}"
          Response.withStatus .seeOther |>.header! "Location" loc |>.text ""
      else
        Response.notFound |>.text "Page unavailable."
    | .delete =>
      if let ["", "api", "posts", idStr] := path.splitOn "/" then
        let some id := idStr.toNat? | return ← Response.badRequest |>.text "Invalid post ID."
        match ← app.store.deletePost ⟨id.toUInt64⟩ with
        | .error msg => Response.notFound |>.text msg
        | .ok () => Response.ok |>.header! "Content-Type" "application/json" |>.text "{\"deleted\":true}"
      else
        Response.notFound |>.text "Page unavailable."
    | _ => Response.withStatus .methodNotAllowed |>.text "Unsupported method."

def main : IO Unit := do
  let configuredPort ← IO.getEnv "PORT"
  let port : UInt16 ← match configuredPort with
    | none => pure 8080
    | some value => do
      let some port := value.toNat? | throw <| IO.userError "PORT must be an integer from 1 to 65535"
      unless 0 < port && port ≤ 65535 do
        throw <| IO.userError "PORT must be an integer from 1 to 65535"
      pure port.toUInt16
  let pol : StoragePolicy := {}
  match ← openAndMigrate "data" pol with
  | .error e => throw <| IO.userError s!"Failed to open Leaf store: {e}"
  | .ok (store, report, migrated) =>
    IO.println s!"Leaf store ready: {report.recoveredPosts} posts recovered (migrated={migrated}, walTrim={report.discardedWalTailBytes}B, segTrim={report.repairedSegmentBytes}B, orphans={report.reclaimedOrphans})"
    Async.block do
      let host := if configuredPort.isSome then Net.IPv4Addr.ofParts 0 0 0 0 else Net.IPv4Addr.ofParts 127 0 0 1
      let addr : Net.SocketAddress := .v4 ⟨host, port⟩
      let server ← Server.serve addr (App.mk pol store)
      IO.println s!"Leaf is listening on {addr}"
      server.waitShutdown
