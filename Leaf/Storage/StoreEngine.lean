import Std.Sync.Mutex
import Leaf.Storage.DbEngine
import Leaf.Storage.BucketEngine

namespace Leaf.Storage

open Leaf.Core

/-- Summary returned by `recoverStore` describing crash-recovery actions performed. -/
structure RecoveryReport where
  recoveredPosts        : Nat
  discardedWalTailBytes : Nat
  repairedSegmentBytes  : Nat
  reclaimedOrphans      : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Live storage metrics exposed to the UI and maintenance endpoints. -/
structure StoreStats where
  postCount           : Nat
  tombstoneCount      : Nat
  walId               : UInt64
  walBytes            : Nat
  ckptId              : UInt64
  objectCount         : Nat
  unreferencedObjects : Nat
  segmentCount        : Nat
  segmentBytes        : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Consistent committed read snapshot with active-reader GC pinning. -/
structure Snapshot where
  id         : UInt64
  db         : DbState
  pinnedKeys : Array ObjectKey

/-- Mutable inner state protected by `Std.Mutex`. -/
structure StoreInner (policy : StoragePolicy) where
  db              : DbEngine
  bucket          : BucketEngine policy
  nextSnapId      : UInt64 := 1
  activeSnapshots : Std.ExtTreeMap UInt64 (Array ObjectKey) := ∅

/-- Thread-safe shared Transaction Manager coordinating `DbEngine` and `BucketEngine`. -/
structure StoreEngine (policy : StoragePolicy) where
  rootDir : System.FilePath
  mutex   : Std.Mutex (StoreInner policy)

namespace StoreEngine

private def collectPinnedPredicate {policy : StoragePolicy} (inner : StoreInner policy) :
    ObjectKey → Bool :=
  let pinnedSet := inner.activeSnapshots.foldl
    (fun acc _ keys => keys.foldl (fun s k => s.insert k) acc)
    (∅ : Std.ExtTreeSet ObjectKey)
  fun k => pinnedSet.contains k

private def reconcileRefCounts {policy : StoragePolicy}
    (db : DbState) (b : BucketEngine policy) : BucketEngine policy :=
  let reset := b.objects.foldl (fun acc k _ => acc.setRefCount k 0) b
  db.posts.foldl (fun acc _ p =>
    match p.image with
    | some ref => acc.incRef ref.key
    | none => acc) reset

/-- Opens and recovers the joint database and bucket engines under `rootDir`,
    repairing truncated WAL/segment tails, discarding uncommitted transactions,
    reconciling reference counts, and reclaiming orphaned objects. -/
def recoverStore (rootDir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (StoreEngine policy × RecoveryReport)) := do
  match ← DbEngine.initWithReport (rootDir / "database") policy with
  | .error e => return .error e
  | .ok (db, walRepaired) =>
    match ← BucketEngine.initWithReport (rootDir / "bucket") policy with
    | .error e => return .error e
    | .ok (b, segRepaired) =>
      let bReconciled := reconcileRefCounts db.state b
      let (bClean, orphans) := bReconciled.gcStep
      let m ← Std.Mutex.new { db := db, bucket := bClean }
      let postCount := db.state.posts.foldl (fun acc _ _ => acc + 1) 0
      let report : RecoveryReport :=
        { recoveredPosts := postCount
          discardedWalTailBytes := walRepaired
          repairedSegmentBytes := segRepaired
          reclaimedOrphans := orphans }
      return .ok ({ rootDir := rootDir, mutex := m }, report)

/-- Opens or initializes the joint database and bucket engines under `rootDir`. -/
def openStore (rootDir : System.FilePath) (policy : StoragePolicy := {}) :
    IO (Except String (StoreEngine policy)) := do
  match ← recoverStore rootDir policy with
  | .error e => return .error e
  | .ok (store, _) => return .ok store

private def toWalBucketEntry {segSize : Nat} (m : BucketEntryMeta segSize) : WalBucketEntry :=
  { key := m.key
    location :=
      { segment := m.location.segment
        offset := m.location.offset.toUInt64
        length := m.location.length.toUInt32 }
    mime := m.mime
    crc32 := m.crc32 }

/-- Creates a post (optionally with an image) atomically under the shared transaction manager. -/
def createPostWithImage {policy : StoragePolicy} (store : StoreEngine policy)
    (draft : ValidPostDraft) (img? : Option (ByteArray × MimeType)) (now : Int64) :
    IO (Except String Post) :=
  store.mutex.atomically do
    let inner ← get
    let txId := inner.db.nextTxId
    let db0 := { inner.db with nextTxId := ⟨txId.val + 1⟩ }
    let seq0 : SeqNo := ⟨db0.state.lastSeq.val + 1⟩
    -- 1. WAL beginTx
    let db1 ← match ← db0.appendWalFrame txId seq0 .beginTx with
      | .error e => return .error e
      | .ok d => pure d
    -- 2. Stage / deduplicate image if present
    let mut bCur := inner.bucket
    let mut dbCur := db1
    let mut seqCur := seq0
    let mut imgRef? : Option ImageRef := none
    match img? with
    | none => pure ()
    | some (bytes, mime) =>
      match ← bCur.putObject bytes mime with
      | .error e =>
        let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
        set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
        return .error e
      | .ok (key, entryMeta, isNew, bNext) =>
        bCur := bNext
        if isNew then
          seqCur := ⟨seqCur.val + 1⟩
          match ← dbCur.appendWalFrame txId seqCur (.allocObject (toWalBucketEntry entryMeta)) with
          | .error e =>
            let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
            set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
            return .error e
          | .ok d => dbCur := d
        imgRef? := some { key := key, mime := mime, byteSize := entryMeta.byteSize.toUInt32 }
    -- 3. Build post via pure DbState.createPost (validates & increments IDs)
    match dbCur.state.createPost now draft imgRef? with
    | .error e =>
      let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
      set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
      return .error s!"createPost failed: {repr e}"
    | .ok (post, _) =>
      seqCur := ⟨seqCur.val + 1⟩
      let postOp := WalOp.putPost post
      match ← dbCur.appendWalFrame txId seqCur postOp with
      | .error e =>
        let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
        set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
        return .error e
      | .ok d => dbCur := d
      -- 4. Reference count update in WAL + commit
      match imgRef? with
      | some ref =>
        seqCur := ⟨seqCur.val + 1⟩
        match ← dbCur.appendWalFrame txId seqCur (.incRef ref.key) with
        | .error e =>
          let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
          set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
          return .error e
        | .ok d => dbCur := d
        bCur := bCur.incRef ref.key
      | none => pure ()
      seqCur := ⟨seqCur.val + 1⟩
      match ← dbCur.appendWalFrame txId seqCur .commitTx with
      | .error e =>
        let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
        return .error e
      | .ok d => dbCur := d
      -- 5. Publish committed state in memory
      dbCur := dbCur.applyCommitted post.version postOp
      set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
      return .ok post

/-- Updates an existing post (optionally replacing/removing its image) transactionally. -/
def updatePostWithImage {policy : StoragePolicy} (store : StoreEngine policy)
    (id : PostId) (patch : ValidPostPatch) (newImg? : Option (ByteArray × MimeType)) (now : Int64) :
    IO (Except String Post) :=
  store.mutex.atomically do
    let inner ← get
    let some existing := inner.db.getPost id
      | return .error s!"post {id.val} not found"
    let txId := inner.db.nextTxId
    let db0 := { inner.db with nextTxId := ⟨txId.val + 1⟩ }
    let seq0 : SeqNo := ⟨db0.state.lastSeq.val + 1⟩
    let db1 ← match ← db0.appendWalFrame txId seq0 .beginTx with
      | .error e => return .error e
      | .ok d => pure d
    let mut bCur := inner.bucket
    let mut dbCur := db1
    let mut seqCur := seq0
    let mut newRef? : Option ImageRef := none
    match patch.imagePatch with
    | .keep | .remove => pure ()
    | .replace _ _ =>
      let some (bytes, mime) := newImg?
        | do
          let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
          set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
          return .error "missing replacement image bytes"
      match ← bCur.putObject bytes mime with
      | .error e =>
        let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
        set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
        return .error e
      | .ok (key, entryMeta, isNew, bNext) =>
        bCur := bNext
        if isNew then
          seqCur := ⟨seqCur.val + 1⟩
          match ← dbCur.appendWalFrame txId seqCur (.allocObject (toWalBucketEntry entryMeta)) with
          | .error e =>
            let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
            set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
            return .error e
          | .ok d => dbCur := d
        newRef? := some { key := key, mime := mime, byteSize := entryMeta.byteSize.toUInt32 }
    match dbCur.state.updatePost id now patch newRef? with
    | .error e =>
      let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
      set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
      return .error s!"updatePost failed: {repr e}"
    | .ok (updated, _) =>
      seqCur := ⟨seqCur.val + 1⟩
      let op := WalOp.updatePost updated
      match ← dbCur.appendWalFrame txId seqCur op with
      | .error e =>
        let _ ← dbCur.appendWalFrame txId ⟨seqCur.val + 1⟩ .abortTx
        set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
        return .error e
      | .ok d => dbCur := d
      -- Update refcounts for old/new images
      match existing.image, updated.image with
      | some oldRef, some curRef =>
        if oldRef.key != curRef.key then
          seqCur := ⟨seqCur.val + 1⟩
          match ← dbCur.appendWalFrame txId seqCur (.decRef oldRef.key) with
          | .error e => return .error e
          | .ok d => dbCur := d
          seqCur := ⟨seqCur.val + 1⟩
          match ← dbCur.appendWalFrame txId seqCur (.incRef curRef.key) with
          | .error e => return .error e
          | .ok d => dbCur := d
          bCur := (bCur.decRef oldRef.key).incRef curRef.key
      | some oldRef, none =>
        seqCur := ⟨seqCur.val + 1⟩
        match ← dbCur.appendWalFrame txId seqCur (.decRef oldRef.key) with
        | .error e => return .error e
        | .ok d => dbCur := d
        bCur := bCur.decRef oldRef.key
      | none, some curRef =>
        seqCur := ⟨seqCur.val + 1⟩
        match ← dbCur.appendWalFrame txId seqCur (.incRef curRef.key) with
        | .error e => return .error e
        | .ok d => dbCur := d
        bCur := bCur.incRef curRef.key
      | none, none => pure ()
      seqCur := ⟨seqCur.val + 1⟩
      match ← dbCur.appendWalFrame txId seqCur .commitTx with
      | .error e => return .error e
      | .ok d => dbCur := d
      dbCur := dbCur.applyCommitted updated.version op
      set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
      return .ok updated

/-- Deletes a post transactionally, decrementing any attached image reference count. -/
def deletePost {policy : StoragePolicy} (store : StoreEngine policy) (id : PostId) :
    IO (Except String Unit) :=
  store.mutex.atomically do
    let inner ← get
    let some existing := inner.db.getPost id
      | return .error s!"post {id.val} not found"
    let txId := inner.db.nextTxId
    let db0 := { inner.db with nextTxId := ⟨txId.val + 1⟩ }
    let seq0 : SeqNo := ⟨db0.state.lastSeq.val + 1⟩
    let mut dbCur ← match ← db0.appendWalFrame txId seq0 .beginTx with
      | .error e => return .error e
      | .ok d => pure d
    let mut bCur := inner.bucket
    let mut seqCur : SeqNo := ⟨seq0.val + 1⟩
    let op := WalOp.deletePost id
    dbCur ← match ← dbCur.appendWalFrame txId seqCur op with
      | .error e => return .error e
      | .ok d => pure d
    match existing.image with
    | some ref =>
      seqCur := ⟨seqCur.val + 1⟩
      dbCur ← match ← dbCur.appendWalFrame txId seqCur (.decRef ref.key) with
        | .error e => return .error e
        | .ok d => pure d
      bCur := bCur.decRef ref.key
    | none => pure ()
    seqCur := ⟨seqCur.val + 1⟩
    dbCur ← match ← dbCur.appendWalFrame txId seqCur .commitTx with
      | .error e => return .error e
      | .ok d => pure d
    dbCur := dbCur.applyCommitted seqCur op
    set ({ inner with db := dbCur, bucket := bCur } : StoreInner policy)
    return .ok ()

/-- Stages an image and immediately aborts the transaction (useful for testing orphan handling). -/
def stageAndAbort {policy : StoragePolicy} (store : StoreEngine policy)
    (bytes : ByteArray) (mime : MimeType) : IO (Except String ObjectKey) :=
  store.mutex.atomically do
    let inner ← get
    let txId := inner.db.nextTxId
    let db0 := { inner.db with nextTxId := ⟨txId.val + 1⟩ }
    let seq0 : SeqNo := ⟨db0.state.lastSeq.val + 1⟩
    let db1 ← match ← db0.appendWalFrame txId seq0 .beginTx with
      | .error e => return .error e
      | .ok d => pure d
    match ← inner.bucket.putObject bytes mime with
    | .error e => return .error e
    | .ok (key, entryMeta, isNew, bNext) =>
      let mut dbCur := db1
      let mut seqCur := seq0
      if isNew then
        seqCur := ⟨seqCur.val + 1⟩
        match ← dbCur.appendWalFrame txId seqCur (.allocObject (toWalBucketEntry entryMeta)) with
        | .error e => return .error e
        | .ok d => dbCur := d
      seqCur := ⟨seqCur.val + 1⟩
      match ← dbCur.appendWalFrame txId seqCur .abortTx with
      | .error e => return .error e
      | .ok d => dbCur := d
      set ({ inner with db := dbCur, bucket := bNext } : StoreInner policy)
      return .ok key

def getPost {policy : StoragePolicy} (store : StoreEngine policy) (id : PostId) : IO (Option Post) :=
  store.mutex.atomically do
    return (← get).db.getPost id

def queryFeed {policy : StoragePolicy} (store : StoreEngine policy)
    (cursor? : Option FeedKey) (limit : Nat) : IO (Array Post) :=
  store.mutex.atomically do
    return (← get).db.queryFeed cursor? limit

def getImage {policy : StoragePolicy} (store : StoreEngine policy) (key : ObjectKey) :
    IO (Except String (ByteArray × MimeType)) :=
  store.mutex.atomically do
    let inner ← get
    match ← inner.bucket.getObject key with
    | .error e => return .error e
    | .ok (bytes, entryMeta, b') =>
      set ({ inner with bucket := b' } : StoreInner policy)
      return .ok (bytes, entryMeta.mime)

def getImageMeta {policy : StoragePolicy} (store : StoreEngine policy) (key : ObjectKey) :
    IO (Option (BucketEntryMeta policy.segmentSize)) :=
  store.mutex.atomically do
    return (← get).bucket.objects[key]?

def getStats {policy : StoragePolicy} (store : StoreEngine policy) : IO StoreStats :=
  store.mutex.atomically do
    let inner ← get
    let posts := inner.db.state.posts.foldl (fun acc _ _ => acc + 1) 0
    let tombs := inner.db.state.tombstones.foldl (fun acc _ => acc + 1) 0
    let (objs, unref) := inner.bucket.objects.foldl
      (fun (acc : Nat × Nat) _ m =>
        (acc.1 + 1, if m.refCount == 0 then acc.2 + 1 else acc.2))
      (0, 0)
    let (segs, segBytes) := inner.bucket.segments.foldl
      (fun (acc : Nat × Nat) _ s => (acc.1 + 1, acc.2 + s.used))
      (0, 0)
    return
      { postCount := posts
        tombstoneCount := tombs
        walId := inner.db.walId
        walBytes := inner.db.walBytes
        ckptId := inner.db.ckptId
        objectCount := objs
        unreferencedObjects := unref
        segmentCount := segs
        segmentBytes := segBytes }

/-- Acquires a consistent committed snapshot and pins all referenced `ObjectKey`s against GC/compaction. -/
def beginSnapshot {policy : StoragePolicy} (store : StoreEngine policy) : IO Snapshot :=
  store.mutex.atomically do
    let inner ← get
    let sid := inner.nextSnapId
    let keys := inner.db.state.posts.foldl (fun acc _ p =>
      match p.image with
      | some ref => acc.push ref.key
      | none => acc) #[]
    set ({ inner with
      nextSnapId := sid + 1
      activeSnapshots := inner.activeSnapshots.insert sid keys } : StoreInner policy)
    return { id := sid, db := inner.db.state, pinnedKeys := keys }

/-- Releases a snapshot and its active-reader object pins. -/
def endSnapshot {policy : StoragePolicy} (store : StoreEngine policy) (snap : Snapshot) : IO Unit :=
  store.mutex.atomically do
    let inner ← get
    set ({ inner with activeSnapshots := inner.activeSnapshots.erase snap.id } : StoreInner policy)

/-- Runs `k` against a consistent snapshot, guaranteeing pin release via `try ... finally`. -/
def withSnapshot {policy : StoragePolicy} {α : Type} (store : StoreEngine policy)
    (k : Snapshot → IO α) : IO α := do
  let snap ← store.beginSnapshot
  try
    k snap
  finally
    store.endSnapshot snap

def runGC {policy : StoragePolicy} (store : StoreEngine policy) : IO Nat :=
  store.mutex.atomically do
    let inner ← get
    let pinned := collectPinnedPredicate inner
    let (b', removed) := inner.bucket.gcStep pinned
    set ({ inner with bucket := b' } : StoreInner policy)
    return removed

def checkpoint {policy : StoragePolicy} (store : StoreEngine policy) : IO (Except String Unit) :=
  store.mutex.atomically do
    let inner ← get
    match ← inner.db.checkpoint with
    | .error e => return .error e
    | .ok db' =>
      set ({ inner with db := db' } : StoreInner policy)
      return .ok ()

def compact {policy : StoragePolicy} (store : StoreEngine policy) : IO (Except String Unit) :=
  store.mutex.atomically do
    let inner ← get
    let pinned := collectPinnedPredicate inner
    match ← inner.db.compact with
    | .error e => return .error e
    | .ok db' =>
      let (bGc, _) := inner.bucket.gcStep pinned
      match ← bGc.compact pinned with
      | .error e => return .error e
      | .ok b' =>
        set ({ inner with db := db', bucket := b' } : StoreInner policy)
        return .ok ()

end StoreEngine

end Leaf.Storage
