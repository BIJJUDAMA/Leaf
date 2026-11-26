import Leaf.Core.Codec
import Leaf.Core.DbModel
import Leaf.Core.WalLog
import Leaf.Storage.SeqIO

namespace Leaf.Storage

open Leaf.Core

/-- Persistent log-structured database engine backed by sequential WAL + atomic checkpoints. -/
structure DbEngine where
  dir      : System.FilePath
  policy   : StoragePolicy
  state    : DbState
  walId    : UInt64
  walBytes : Nat
  ckptId   : UInt64
  nextTxId : TxId

namespace DbEngine

def manifestPath (dir : System.FilePath) : System.FilePath :=
  dir / "manifest.bin"

def manifestTmpPath (dir : System.FilePath) : System.FilePath :=
  dir / "manifest.bin.tmp"

def walDir (dir : System.FilePath) : System.FilePath :=
  dir / "wal"

def walPath (dir : System.FilePath) (walId : UInt64) : System.FilePath :=
  walDir dir / walFileName walId

def ckptDir (dir : System.FilePath) : System.FilePath :=
  dir / "checkpoints"

def ckptPath (dir : System.FilePath) (ckptId : UInt64) : System.FilePath :=
  ckptDir dir / checkpointFileName ckptId

def ckptTmpPath (dir : System.FilePath) (ckptId : UInt64) : System.FilePath :=
  ckptDir dir / s!"{checkpointFileName ckptId}.tmp"

private def writeManifest (e : DbEngine) : IO (Except String Unit) := do
  let m : DbManifest :=
    { formatVersion := frameFormatVersion
      latestCheckpointId := e.ckptId
      activeWalId := e.walId
      nextPostId := e.state.nextPostId
      nextTxId := e.nextTxId
      lastSeq := e.state.lastSeq }
  let payload := encodeDbManifest m
  writeFramedFileAtomic (manifestTmpPath e.dir) (manifestPath e.dir)
    e.policy .manifest 1 e.nextTxId e.state.lastSeq payload

private def dbStateFromCheckpoint (ckpt : DbCheckpoint) : DbState :=
  Id.run do
    let mut posts : Std.ExtTreeMap PostId Post := ∅
    let mut feed : Std.ExtTreeMap FeedKey PostId FeedKey.cmpDesc := ∅
    for p in ckpt.posts do
      posts := posts.insert p.id p
      feed := feed.insert (FeedKey.ofPost p) p.id
    let mut tombs : Std.ExtTreeSet PostId := ∅
    for tid in ckpt.tombstones do
      tombs := tombs.insert tid
    return { posts := posts, feedIndex := feed, tombstones := tombs
             nextPostId := ckpt.nextPostId, lastSeq := ckpt.lastSeq }

private def checkpointFromDbState (db : DbState) : DbCheckpoint :=
  let posts := db.posts.foldl (fun acc _ p => acc.push p) #[]
  let tombs := db.tombstones.foldl (fun acc id => acc.push id) #[]
  { nextPostId := db.nextPostId, lastSeq := db.lastSeq, posts := posts, tombstones := tombs }

private def decodeWalEntries (frames : Array Frame) : Except String (List (TxId × SeqNo × WalOp)) := do
  let mut acc : List (TxId × SeqNo × WalOp) := []
  for f in frames do
    match decodeWalOpAt f.payload 0 with
    | .error e => throw s!"decodeWalOpAt failed: {repr e}"
    | .ok (op, _) => acc := acc ++ [(f.header.txId, f.header.seqNo, op)]
  return acc

/-- Initializes or opens a `DbEngine` at `dir`, repairing any truncated WAL tail and returning
    `(engine, discardedWalTailBytes)`. -/
def initWithReport (dir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (DbEngine × Nat)) := do
  try
    IO.FS.createDirAll (walDir dir)
    IO.FS.createDirAll (ckptDir dir)
    let mPath := manifestPath dir
    if !(← mPath.pathExists) then
      let eng : DbEngine :=
        { dir := dir
          policy := policy
          state := DbState.empty
          walId := 1
          walBytes := 0
          ckptId := 0
          nextTxId := ⟨1⟩ }
      match ← writeManifest eng with
      | .error e => return .error e
      | .ok () => return .ok (eng, 0)
    else
      match ← readFramedFile mPath policy .manifest with
      | .error e => return .error e
      | .ok mFrame =>
        match decodeDbManifestAt mFrame.payload 0 with
        | .error e => return .error s!"decodeDbManifestAt failed: {repr e}"
        | .ok (m, _) =>
          let mut db := DbState.empty
          if m.latestCheckpointId > 0 then
            let cPath := ckptPath dir m.latestCheckpointId
            if ← cPath.pathExists then
              match ← readFramedFile cPath policy .checkpoint with
              | .error e => return .error e
              | .ok cFrame =>
                match decodeDbCheckpointAt cFrame.payload 0 with
                | .error e => return .error s!"decodeDbCheckpointAt failed: {repr e}"
                | .ok (ckpt, _) => db := dbStateFromCheckpoint ckpt
          let wPath := walPath dir m.activeWalId
          let mut wBytes := 0
          let mut discardedTail := 0
          if ← wPath.pathExists then
            let raw ← IO.FS.readBinFile wPath
            let (frames, validEnd) := scanFrames policy .wal raw
            wBytes := validEnd
            if validEnd < raw.size then
              discardedTail := raw.size - validEnd
              let tmpW := walDir dir / s!"{walFileName m.activeWalId}.tmp"
              match ← rewritePrefixAtomic tmpW wPath (raw.extract 0 validEnd) with
              | .error e => return .error e
              | .ok () => pure ()
            match decodeWalEntries frames with
            | .error e => return .error e
            | .ok entries => db := DbState.replayWalOps db entries
          return .ok
            ({ dir := dir
               policy := policy
               state := db
               walId := m.activeWalId
               walBytes := wBytes
               ckptId := m.latestCheckpointId
               nextTxId := m.nextTxId }, discardedTail)
  catch e =>
    return .error s!"DbEngine.init failed: {e}"

/-- Initializes or opens a `DbEngine` at `dir`. -/
def init (dir : System.FilePath) (policy : StoragePolicy := {}) : IO (Except String DbEngine) := do
  match ← initWithReport dir policy with
  | .error e => return .error e
  | .ok (eng, _) => return .ok eng

def getPost (e : DbEngine) (id : PostId) : Option Post :=
  e.state.getPost id

def queryFeed (e : DbEngine) (cursor? : Option FeedKey) (limit : Nat) : Array Post :=
  e.state.queryFeed cursor? limit

def appendWalFrame (e : DbEngine) (txId : TxId) (seqNo : SeqNo) (op : WalOp) :
    IO (Except String DbEngine) := do
  let payload := encodeWalOp op
  let path := walPath e.dir e.walId
  match ← appendFrame path e.walBytes e.policy .wal 1 txId seqNo payload with
  | .error err => return .error err
  | .ok (_, written) =>
    return .ok { e with walBytes := e.walBytes + written }

def applyCommitted (e : DbEngine) (seqNo : SeqNo) (op : WalOp) : DbEngine :=
  { e with state := DbState.applyCommittedWalOp e.state seqNo op }

/-- Writes an atomic checkpoint of the current committed `DbState`, updates `manifest.bin`,
    and rotates to a fresh WAL file. -/
def checkpoint (e : DbEngine) : IO (Except String DbEngine) := do
  let nextCkpt := e.ckptId + 1
  let nextWal := e.walId + 1
  let ckpt := checkpointFromDbState e.state
  let ckptPayload := encodeDbCheckpoint ckpt
  match ← writeFramedFileAtomic (ckptTmpPath e.dir nextCkpt) (ckptPath e.dir nextCkpt)
      e.policy .checkpoint 1 e.nextTxId e.state.lastSeq ckptPayload with
  | .error err => return .error err
  | .ok () =>
    let e' := { e with ckptId := nextCkpt, walId := nextWal, walBytes := 0 }
    match ← writeManifest e' with
    | .error err => return .error err
    | .ok () => return .ok e'

/-- Reclaims tombstones in-memory, checkpoints the compacted state, and deletes older WAL/checkpoint files. -/
def compact (e : DbEngine) : IO (Except String DbEngine) := do
  let oldCkpt := e.ckptId
  let oldWal := e.walId
  let eCompacted := { e with state := e.state.compactDb }
  match ← checkpoint eCompacted with
  | .error err => return .error err
  | .ok e' =>
    if oldCkpt > 0 then
      try IO.FS.removeFile (ckptPath e.dir oldCkpt) catch _ => pure ()
    if oldWal > 0 then
      try IO.FS.removeFile (walPath e.dir oldWal) catch _ => pure ()
    return .ok e'

end DbEngine

end Leaf.Storage
