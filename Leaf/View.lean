import Leaf.Core.Types
import Leaf.Core.Schema

namespace Leaf

open Leaf.Core

def escape (s : String) : String :=
  (((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;"

private def hexByte (b : UInt8) : String :=
  let digits := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let hi := digits[(b.toNat >>> 4) &&& 0xF]!
  let lo := digits[b.toNat &&& 0xF]!
  String.ofList [hi, lo]

def digestToHex (d : Sha256Digest) : String := Id.run do
  let mut out := ""
  for i in [0 : d.bytes.size] do
    out := out ++ hexByte (d.bytes.get! i)
  return out

private def hexVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat).toUInt8
  else none

def hexToDigest? (s : String) : Option Sha256Digest := Id.run do
  let chars := s.toList
  if chars.length != 64 then return none
  let mut arr : Array UInt8 := Array.mkEmpty 32
  let mut rest := chars
  while !rest.isEmpty do
    match rest with
    | c1 :: c2 :: tl =>
      let some hi := hexVal? c1 | return none
      let some lo := hexVal? c2 | return none
      arr := arr.push ((hi <<< 4) ||| lo)
      rest := tl
    | _ => return none
  let bytes := ByteArray.mk arr
  if h : bytes.size = 32 then
    return some ⟨bytes, h⟩
  else
    return none

def encodeCursor (fk : FeedKey) : String :=
  s!"{fk.createdAt.toInt}:{fk.id.val}"

def decodeCursor? (s : String) : Option FeedKey :=
  match s.splitOn ":" with
  | [tsStr, idStr] =>
    match tsStr.toInt?, idStr.toNat? with
    | some ts, some id => some ⟨ts.toInt64, ⟨id.toUInt64⟩⟩
    | _, _ => none
  | _ => none

private def styles : String := r#"
:root { color-scheme: light; }
* { box-sizing: border-box; }
body { margin: 0; background: white; color: black; font: 1rem/1.5 system-ui, sans-serif; }
main { width: min(42rem, 100% - 2.5rem); margin: clamp(2rem, 6vw, 4rem) auto; }
h1 { margin: 0 0 1.5rem; font: 500 clamp(3rem, 7vw, 4.2rem)/1 Georgia, serif; letter-spacing: -.05em; }
input[type=text], textarea { display: block; width: 100%; padding: .75rem 1rem; border: 1px solid #999; border-radius: .25rem; font: inherit; margin-bottom: .6rem; }
textarea { min-height: 6rem; resize: vertical; }
.row { display: flex; gap: .6rem; flex-wrap: wrap; }
.row input[type=text] { flex: 1 1 12rem; }
.tools { display: flex; align-items: start; flex-wrap: wrap; gap: .75rem; margin-top: .5rem; }
.attachment { flex: 1 1 13rem; min-width: 0; }
input[type=file] { display: block; width: 100%; font: inherit; font-size: .875rem; }
button, input::file-selector-button, .btn { min-height: 40px; border: 1px solid black; border-radius: .25rem; padding: .45rem .9rem; font: inherit; cursor: pointer; text-decoration: none; display: inline-flex; align-items: center; }
input::file-selector-button, .btn-secondary { margin-right: .5rem; background: white; color: black; }
button.primary { background: black; color: white; font-weight: 600; }
button.danger { background: white; color: #900; border-color: #900; font-size: .85rem; min-height: 32px; padding: .25rem .65rem; }
button:disabled { opacity: .65; cursor: wait; }
:focus-visible { outline: 2px solid black; outline-offset: 3px; }
small, time, .empty, .meta { color: #555; font-size: .875rem; }
small { display: block; margin-top: .35rem; }
section { margin-top: 2.25rem; }
h2 { margin: 0; padding-bottom: .7rem; border-bottom: 1px solid black; font-size: 1.125rem; }
article { padding: 1.25rem 0; border-bottom: 1px solid #ccc; }
article h3 { margin: .25rem 0 .35rem; font-size: 1.15rem; }
article img { display: block; max-width: 100%; max-height: 38rem; margin-top: .75rem; }
article p { margin: .5rem 0 0; white-space: pre-wrap; overflow-wrap: anywhere; }
.actions { display: flex; gap: .5rem; align-items: center; margin-top: .75rem; flex-wrap: wrap; }
details summary { cursor: pointer; font-size: .85rem; color: #333; }
details form { margin-top: .75rem; padding: .75rem; border: 1px solid #ddd; border-radius: .25rem; }
nav.pager { display: flex; justify-content: space-between; margin-top: 1.5rem; }
footer { margin-top: 3rem; padding-top: 1.25rem; border-top: 1px solid #ccc; }
.footer-head { display: flex; justify-content: space-between; align-items: baseline; flex-wrap: wrap; gap: .5rem; margin-bottom: .5rem; }
.footer-head h2 { border: 0; padding: 0; font-size: 1rem; }
.stats-line { margin: 0 0 .25rem; color: #333; font-size: .825rem; }
.stats-help { margin: 0 0 .85rem; color: #666; font-size: .78rem; line-height: 1.4; }
.maint-notice { margin: 0 0 .85rem; padding: .6rem .85rem; border: 1px solid #333; border-radius: .25rem; background: #f8f8f8; font-size: .85rem; }
.docs-link { color: black; font-size: .875rem; text-underline-offset: 3px; }
.maint-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(11.5rem, 1fr)); gap: .75rem; }
.maint-card { border: 1px solid #ddd; border-radius: .25rem; padding: .75rem; display: flex; flex-direction: column; gap: .4rem; }
.maint-card p { margin: 0; color: #555; font-size: .825rem; line-height: 1.4; flex: 1; }
.maint-card a { color: #333; font-size: .8rem; text-underline-offset: 2px; }
.header-bar { display: flex; justify-content: space-between; align-items: baseline; margin-bottom: 1.5rem; }
.header-bar h1 { margin: 0; }
.doc-nav { display: flex; flex-wrap: wrap; gap: .5rem 1rem; margin: 1rem 0 2rem; padding: .75rem 1rem; border: 1px solid #ddd; border-radius: .25rem; font-size: .875rem; }
.doc-nav a { color: black; text-underline-offset: 3px; }
.doc-section { margin-top: 2rem; padding-top: .5rem; }
.doc-section h2 { margin-bottom: .75rem; }
.doc-section p, .doc-section li { color: #222; }
.doc-section code { background: #f4f4f4; padding: .1rem .35rem; border-radius: .2rem; font-size: .88em; }
.doc-section pre { background: #f7f7f7; border: 1px solid #e0e0e0; border-radius: .25rem; padding: .85rem 1rem; overflow-x: auto; font-size: .85rem; line-height: 1.45; }
table.doc-table { width: 100%; border-collapse: collapse; margin-top: .75rem; font-size: .875rem; }
table.doc-table th, table.doc-table td { text-align: left; padding: .5rem .6rem; border-bottom: 1px solid #ddd; vertical-align: top; }
table.doc-table th { border-bottom: 1px solid black; }
"#

private def composer : String := r#"
<main><div class="header-bar"><h1>Leaf</h1><a class="docs-link" href="/docs">Documentation →</a></div>
<form id="composer" action="/posts" method="post" enctype="multipart/form-data">
<div class="row">
<input type="text" name="author" maxlength="80" placeholder="Author (default: journal)" aria-label="Author">
<input type="text" name="title" maxlength="160" placeholder="Optional title" aria-label="Title">
</div>
<textarea name="caption" rows="3" maxlength="500" aria-label="Caption" placeholder="Write an entry…"></textarea>
<div class="tools"><div class="attachment">
<input type="file" name="image" accept="image/jpeg,image/png,image/webp,image/gif" aria-label="Attach a photo" aria-describedby="formats">
<small id="formats">JPEG, PNG, WebP or GIF · 10 MiB max</small></div><button class="primary" type="submit">Publish</button></div>
<p class="error" role="alert"></p></form>
"#

private def enhance : String := r#"
const dateFormat = new Intl.DateTimeFormat(undefined, { dateStyle: 'medium', timeStyle: 'short' });
for (const stamp of document.querySelectorAll('time[data-seconds]')) {
  const date = new Date(Number(stamp.dataset.seconds) * 1000);
  if (Number.isFinite(date.valueOf())) {
    stamp.dateTime = date.toISOString();
    stamp.textContent = dateFormat.format(date);
  }
}
"#

def page (rows : Array Post) (nextCursor? : Option FeedKey) (limit : Nat)
    (statusSummary : String := "") (maintNotice? : Option String := none) : String := Id.run do
  let mut out := "<!doctype html><html lang=en><head><meta charset=utf-8><meta name=viewport content='width=device-width, initial-scale=1'><title>Leaf</title><style>" ++
    styles ++ "</style></head><body>" ++ composer ++ "<section id=entries aria-labelledby=recent><h2 id=recent>Entries</h2>"
  if rows.isEmpty then out := out ++ "<p class=empty>No entries yet.</p>"
  for post in rows do
    let id := toString post.id.val
    out := out ++ "<article>"
    out := out ++ "<div class=meta><strong>" ++ escape post.author ++ "</strong> · <time data-seconds='" ++
      toString post.createdAt.toInt ++ "'></time> · #" ++ id ++ "</div>"
    if let some title := post.title then
      out := out ++ "<h3>" ++ escape title ++ "</h3>"
    if let some ref := post.image then
      let hex := digestToHex ref.key.digest
      out := out ++ "<img loading=lazy alt='Photo for entry " ++ id ++ "' src='/objects/" ++ hex ++ "/" ++ toString ref.key.tag.val ++ "'>"
    unless post.caption.isEmpty do
      out := out ++ "<p>" ++ escape post.caption ++ "</p>"
    out := out ++ "<div class=actions>"
    out := out ++ "<details><summary>Edit</summary><form action='/posts/" ++ id ++ "/edit' method='post' enctype='multipart/form-data'>"
    out := out ++ "<input type=text name=title value='" ++ escape (post.title.getD "") ++ "' placeholder='Title'>"
    out := out ++ "<textarea name=caption rows=2 maxlength=500>" ++ escape post.caption ++ "</textarea>"
    out := out ++ "<input type=file name=image accept='image/jpeg,image/png,image/webp,image/gif'>"
    if post.image.isSome then
      out := out ++ "<label><input type=checkbox name=remove_image value=1> Remove image</label> "
    out := out ++ "<button class=primary type=submit>Save</button></form></details>"
    out := out ++ "<form action='/posts/" ++ id ++ "/delete' method='post'><button class=danger type=submit>Delete</button></form>"
    out := out ++ "</div></article>"
  out := out ++ "</section>"
  out := out ++ "<nav class=pager><a class='btn btn-secondary' href='/'>Latest</a>"
  if let some nc := nextCursor? then
    out := out ++ "<a class='btn btn-secondary' href='/?cursor=" ++ escape (encodeCursor nc) ++ "&limit=" ++ toString limit ++ "'>Older entries →</a>"
  out := out ++ "</nav>"
  out := out ++ "<footer>"
  out := out ++ "<div class=footer-head><h2>Storage Maintenance</h2><a class=docs-link href='/docs'>Full architecture →</a></div>"
  unless statusSummary.isEmpty do
    out := out ++ "<p class=stats-line>" ++ escape statusSummary ++ "</p>"
    out := out ++ "<p class=stats-help>Tombstones: deleted post markers cleared by Compact · WAL: active log file &amp; size reset by Checkpoint · Checkpoint: latest saved snapshot · Images: stored photos (unused count cleared by GC) · Segments: image pack files &amp; total size reclaimed by Compact</p>"
  if let some notice := maintNotice? then
    out := out ++ "<div class=maint-notice role=status>" ++ escape notice ++ "</div>"
  out := out ++ "<div class=maint-grid>"
  out := out ++ "<div class=maint-card><form action='/admin/checkpoint' method='post'><button class=btn-secondary type=submit>Checkpoint</button></form>"
  out := out ++ "<p>Saves a binary snapshot of committed posts and rotates to a fresh WAL file.</p>"
  out := out ++ "<a href='/docs#checkpoint'>How Checkpoint works →</a></div>"
  out := out ++ "<div class=maint-card><form action='/admin/gc' method='post'><button class=btn-secondary type=submit>GC</button></form>"
  out := out ++ "<p>Reclaims unreferenced images while respecting active reader snapshot pins.</p>"
  out := out ++ "<a href='/docs#gc'>How GC works →</a></div>"
  out := out ++ "<div class=maint-card><form action='/admin/compact' method='post'><button class=btn-secondary type=submit>Compact</button></form>"
  out := out ++ "<p>Drops deleted tombstones and rewrites live images into clean pack segments.</p>"
  out := out ++ "<a href='/docs#compact'>How Compact works →</a></div>"
  out := out ++ "</div></footer>"
  return out ++ "</main><script>" ++ enhance ++ "</script></body></html>"

/-- Full in-app documentation page served at `GET /docs`. -/
def docsPage : String :=
  "<!doctype html><html lang=en><head><meta charset=utf-8><meta name=viewport content='width=device-width, initial-scale=1'><title>Leaf Documentation</title><style>" ++
  styles ++ "</style></head><body><main>" ++
  "<div class=header-bar><h1>Leaf Docs</h1><a class=docs-link href='/'>← Back to Journal</a></div>" ++
  "<nav class=doc-nav>" ++
  "<a href='#overview'>Overview</a>" ++
  "<a href='#database'>Database Engine</a>" ++
  "<a href='#bucket'>Object Storage</a>" ++
  "<a href='#transactions'>Transactions &amp; Snapshots</a>" ++
  "<a href='#checkpoint'>Checkpoint</a>" ++
  "<a href='#gc'>Garbage Collection</a>" ++
  "<a href='#compact'>Compaction</a>" ++
  "<a href='#recovery'>Crash Recovery</a>" ++
  "<a href='#verification'>Formal Proofs</a>" ++
  "<a href='#api'>HTTP &amp; JSON API</a>" ++
  "</nav>" ++

  "<section id=overview class=doc-section><h2>1. Overview</h2>" ++
  "<p>Leaf is a self-contained journal and image store written entirely in Lean 4. Instead of delegating storage to SQLite, PostgreSQL, or an external object service like S3, Leaf implements its own persistence layer, checksums, hashing, indexing, transactions, and recovery directly in Lean.</p>" ++
  "<p>Because Lean's standard file handles only support sequential reading and appending (not jumping to arbitrary byte offsets or forcing OS-level disk syncs), Leaf cannot use traditional in-place B-Trees. Instead, it stores everything as append-only logs— and swaps state files atomically using temporary files and renames.</p>" ++
  "<pre>data/\n├── database/\n│   ├── manifest.bin          # Tracks the latest checkpoint and active log file\n│   ├── wal/                  # Append-only transaction logs\n│   └── checkpoints/          # Full snapshots of committed posts\n└── bucket/\n    ├── manifest.bin          # Tracks the active image pack file and offset\n    └── segments/             # 16 MiB append-only image pack files</pre>" ++
  "</section>" ++

  "<section id=database class=doc-section><h2>2. Database Engine</h2>" ++
  "<p>Every record written to disk is wrapped in a binary frame with a header and a trailing CRC32 checksum. If a crash or disk error corrupts any byte, Leaf detects the mismatch when reading instead of silently loading bad data.</p>" ++
  "<p>Writes are appended to the write-ahead log (WAL) in order. To keep reads fast without scanning the entire log on every page load, Leaf maintains ordered in-memory indexes: one by post ID for direct lookups, one sorted newest-first for cursor-based feed pagination, and a set of deleted IDs (tombstones) so deleted posts stay hidden.</p>" ++
  "</section>" ++

  "<section id=bucket class=doc-section><h2>3. Object Storage</h2>" ++
  "<p>Uploaded images (JPEG, PNG, WebP, or GIF up to 10 MiB) are packed into 16 MiB binary segment files rather than stored as thousands of tiny individual files. Each image is hashed with SHA-256 so identical uploads are stored once and shared across posts.</p>" ++
  "<p>Leaf does not blindly assume two files with the same SHA-256 hash are identical. When a hash matches an existing image, Leaf reads the stored bytes and compares them byte-for-byte. If they match, it reuses the existing object; if they ever differ, it assigns a separate tag so distinct images never overwrite each other.</p>" ++
  "<p>Since Lean's file handles cannot seek directly to an image's offset inside a pack file, Leaf checks a small 4-segment memory cache first. On a cache miss, it opens the pack file, skips forward sequentially in chunks to the target offset, reads the frame, and verifies both its CRC32 checksum and SHA-256 hash before serving it.</p>" ++
  "</section>" ++

  "<section id=transactions class=doc-section><h2>4. Transactions &amp; Snapshots</h2>" ++
  "<p>Post metadata and image storage are coordinated under a single transaction manager so they never drift out of sync. Publishing a post with an image validates the input, starts a transaction in the log, stores or deduplicates the image, records the post and its image reference, writes a commit record, and flushes the log before making the post visible.</p>" ++
  "<p>If anything fails before the commit record is written, the transaction is aborted and the post never appears. Any image bytes already written to a pack file remain unreferenced and are cleaned up later.</p>" ++
  "<p>Readers do not block writers while pages or images are being sent over HTTP. Instead, a reader takes a lightweight snapshot of the committed posts and temporarily pins the images it needs, guaranteeing that background cleanup cannot delete an image while someone is still viewing it.</p>" ++
  "</section>" ++

  "<section id=checkpoint class=doc-section><h2>5. Checkpoint</h2>" ++
  "<p>Over time, appending every edit and deletion to the log makes startup replay slower. Clicking Checkpoint writes a clean snapshot of all current posts and tombstones to a temporary file, flushes it, renames it into place, and rotates to a fresh empty log file. Future restarts only need to load that checkpoint and replay whatever happened after it.</p>" ++
  "</section>" ++

  "<section id=gc class=doc-section><h2>6. Garbage Collection</h2>" ++
  "<p>Deleting a post, replacing its photo, or aborting an upload can leave stored images with zero posts pointing to them. Clicking GC scans the image index and removes any unreferenced entries, while skipping any image still pinned by an active reader snapshot.</p>" ++
  "</section>" ++

  "<section id=compact class=doc-section><h2>7. Compaction</h2>" ++
  "<p>Even after GC removes unreferenced images from the index, old deleted post markers (tombstones) and dead image bytes still occupy space on disk. Clicking Compact clears database tombstones into a fresh checkpoint, deletes superseded log files, and rewrites all remaining live images into clean pack files before removing the old fragmented ones.</p>" ++
  "</section>" ++

  "<section id=recovery class=doc-section><h2>8. Crash Recovery</h2>" ++
  "<p>When Leaf starts up, it loads the latest checkpoint and scans the active log and pack files from start to finish. If the process crashed mid-write and left a half-written or corrupted frame at the end of a file, Leaf trims that incomplete tail back to the last valid frame boundary.</p>" ++
  "<p>It then replays only transactions that have a matching commit record, ignoring any uncommitted work from a crash, recalculates image reference counts from the recovered posts, and clears any orphaned image entries.</p>" ++
  "<p class=meta>Because Lean's file flush only pushes user-space buffers to the operating system without forcing a hardware disk sync, Leaf recovers reliably from application crashes, though sudden power loss can still lose recently flushed writes.</p>" ++
  "</section>" ++

  "<section id=verification class=doc-section><h2>9. Formal Verification</h2>" ++
  "<p>Unit tests only check the specific cases someone thought to write. Alongside tests, Leaf uses Lean's type system and proof checker to mathematically prove that its core storage rules hold for every possible input, without relying on unproven assumptions or escape hatches.</p>" ++
  "<p>These proofs establish that binary encoding and decoding always roundtrip cleanly, corrupted or truncated frames are always rejected, deleted posts never appear in queries or feeds, feed pages stay ordered without duplicates or gaps, uncommitted transactions have no effect on recovery, images always fit within their segment bounds, and garbage collection never drops a live or reader-pinned image.</p>" ++
  "</section>" ++

  "<section id=api class=doc-section><h2>10. HTTP &amp; JSON API</h2>" ++
  "<table class=doc-table><thead><tr><th>Route</th><th>Purpose</th></tr></thead><tbody>" ++
  "<tr><td><code>GET /</code></td><td>Journal feed with cursor pagination (<code>?cursor=...&amp;limit=...</code>)</td></tr>" ++
  "<tr><td><code>GET /docs</code></td><td>This documentation page</td></tr>" ++
  "<tr><td><code>GET /api/posts</code></td><td>JSON paginated feed (<code>posts</code>, <code>nextCursor</code>)</td></tr>" ++
  "<tr><td><code>GET /api/posts/{id}</code></td><td>JSON single post lookup</td></tr>" ++
  "<tr><td><code>POST /posts</code></td><td>Create post + optional image (multipart)</td></tr>" ++
  "<tr><td><code>POST /posts/{id}/edit</code></td><td>Update post or replace/remove image</td></tr>" ++
  "<tr><td><code>POST /posts/{id}/delete</code></td><td>Delete post and decrement image refcount</td></tr>" ++
  "<tr><td><code>DELETE /api/posts/{id}</code></td><td>JSON delete post</td></tr>" ++
  "<tr><td><code>GET /objects/{hex}/{tag}</code></td><td>Stream CRC32 + SHA-256 verified image object</td></tr>" ++
  "<tr><td><code>GET /images/{id}</code></td><td>Legacy image route by post ID</td></tr>" ++
  "<tr><td><code>POST /admin/checkpoint</code></td><td>Write checkpoint &amp; rotate WAL</td></tr>" ++
  "<tr><td><code>POST /admin/gc</code></td><td>Run pin-aware object garbage collection</td></tr>" ++
  "<tr><td><code>POST /admin/compact</code></td><td>Compact DB tombstones &amp; bucket segments</td></tr>" ++
  "</tbody></table></section>" ++
  "</main></body></html>"

end Leaf
