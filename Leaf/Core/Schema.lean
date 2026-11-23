import Leaf.Core.Types
import Leaf.Core.Policy

namespace Leaf.Core

/-- Reference to a content-addressed object stored in the bucket. -/
structure ImageRef where
  key      : ObjectKey
  mime     : MimeType
  byteSize : UInt32
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Social media post record stored in the database engine. -/
structure Post where
  id        : PostId
  author    : String
  title     : Option String
  caption   : String
  tags      : Array String
  createdAt : Int64
  updatedAt : Option Int64
  version   : SeqNo
  image     : Option ImageRef
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Unvalidated input for creating a post. -/
structure PostDraft where
  author     : String
  title      : Option String := none
  caption    : String := ""
  tags       : Array String := #[]
  imageBytes : Option ByteArray := none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Validated and normalized post creation payload. -/
structure ValidPostDraft where
  author  : String
  title   : Option String
  caption : String
  tags    : Array String
  image   : Option (MimeType × ByteArray)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Image mutation intent during post updates. -/
inductive ImagePatch where
  | keep
  | remove
  | replace (bytes : ByteArray)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Validated image mutation intent. -/
inductive ValidImagePatch where
  | keep
  | remove
  | replace (mime : MimeType) (bytes : ByteArray)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Unvalidated input for updating an existing post. -/
structure PostUpdate where
  author?    : Option String := none
  title?     : Option (Option String) := none
  caption?   : Option String := none
  tags?      : Option (Array String) := none
  imagePatch : ImagePatch := .keep
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Validated and normalized post update payload. -/
structure ValidPostPatch where
  author     : String
  title      : Option String
  caption    : String
  tags       : Array String
  imagePatch : ValidImagePatch
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Wire-level object span before policy bounds validation. -/
structure RawObjectLocation where
  segment : SegmentId
  offset  : UInt64
  length  : UInt32
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Object metadata written in WAL records. -/
structure WalBucketEntry where
  key      : ObjectKey
  location : RawObjectLocation
  mime     : MimeType
  crc32    : UInt32
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Authoritative joint WAL operations across DB and Bucket. -/
inductive WalOp where
  | beginTx
  | putPost (post : Post)
  | updatePost (post : Post)
  | deletePost (id : PostId)
  | allocObject (entry : WalBucketEntry)
  | incRef (key : ObjectKey)
  | decRef (key : ObjectKey)
  | commitTx
  | abortTx
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Payload stored inside a pack segment frame. -/
structure BucketSegmentRecord where
  key     : ObjectKey
  mime    : MimeType
  payload : ByteArray
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Database manifest header written atomically to `database/manifest.bin`. -/
structure DbManifest where
  formatVersion      : UInt16
  latestCheckpointId : UInt64
  activeWalId        : UInt64
  nextPostId         : PostId
  nextTxId           : TxId
  lastSeq            : SeqNo
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Bucket manifest header written atomically to `bucket/manifest.bin`. -/
structure BucketManifest where
  formatVersion       : UInt16
  segmentSize         : UInt64
  activeSegmentId     : SegmentId
  activeSegmentOffset : UInt64
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Database checkpoint payload written to `database/checkpoints/checkpoint-XXXXXX.bin`. -/
structure DbCheckpoint where
  nextPostId : PostId
  lastSeq    : SeqNo
  posts      : Array Post
  tombstones : Array PostId
  deriving DecidableEq, BEq, Repr, Inhabited

private def trimText (s : String) : String :=
  s.trimAscii.toString

private def validateAuthor (policy : StoragePolicy) (raw : String) : Except CoreError String := do
  let author := trimText raw
  if author.isEmpty then throw .emptyAuthor
  if author.length > policy.maxAuthorChars then throw .authorTooLong
  return author

private def validateTitle (policy : StoragePolicy) (raw? : Option String) : Except CoreError (Option String) := do
  match raw? with
  | none => return none
  | some raw =>
    let t := trimText raw
    if t.isEmpty then throw .emptyTitle
    if t.length > policy.maxTitleChars then throw .titleTooLong
    return some t

private def validateCaption (policy : StoragePolicy) (raw : String) : Except CoreError String := do
  let caption := trimText raw
  if caption.length > policy.maxCaptionChars then throw .captionTooLong
  return caption

private def validateTags (policy : StoragePolicy) (rawTags : Array String) : Except CoreError (Array String) := do
  if rawTags.size > policy.maxTags then throw .tooManyTags
  let mut seen : Array String := #[]
  for raw in rawTags do
    let t := trimText raw
    if t.isEmpty then throw .emptyTag
    if t.length > policy.maxTagChars then throw .tagTooLong
    unless seen.contains t do
      seen := seen.push t
  return seen

private def validateImageBytes (policy : StoragePolicy) (bytes : ByteArray) :
    Except CoreError (MimeType × ByteArray) := do
  if bytes.size > policy.maxImageBytes then throw .imageTooLarge
  let some mime := detectMimeType bytes | throw .invalidImageSignature
  return (mime, bytes)

/-- Validates and normalizes a new post draft against `policy`. -/
def validateDraft (policy : StoragePolicy) (draft : PostDraft) : Except CoreError ValidPostDraft := do
  let author ← validateAuthor policy draft.author
  let title ← validateTitle policy draft.title
  let caption ← validateCaption policy draft.caption
  let tags ← validateTags policy draft.tags
  let image ← match draft.imageBytes with
    | none => pure none
    | some bytes => pure (some (← validateImageBytes policy bytes))
  if caption.isEmpty && image.isNone then throw .emptyContent
  return { author, title, caption, tags, image }

/-- Validates and normalizes an update patch against `existing` and `policy`. -/
def validatePostPatch (policy : StoragePolicy) (existing : Post) (upd : PostUpdate) :
    Except CoreError ValidPostPatch := do
  let author ← validateAuthor policy (upd.author?.getD existing.author)
  let title ← validateTitle policy (upd.title?.getD existing.title)
  let caption ← validateCaption policy (upd.caption?.getD existing.caption)
  let tags ← validateTags policy (upd.tags?.getD existing.tags)
  let (imagePatch, hasImageAfter) ← match upd.imagePatch with
    | .keep => pure (.keep, existing.image.isSome)
    | .remove => pure (.remove, false)
    | .replace bytes =>
      let (mime, validBytes) ← validateImageBytes policy bytes
      pure (.replace mime validBytes, true)
  if caption.isEmpty && !hasImageAfter then throw .emptyContent
  return { author, title, caption, tags, imagePatch }

end Leaf.Core
