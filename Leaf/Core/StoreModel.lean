import Leaf.Core.DbModel
import Leaf.Core.BucketModel

namespace Leaf.Core

/-- Active transaction staging buffer prior to atomic commit or abort. -/
structure PendingTx where
  txId       : TxId
  stagedKeys : Array ObjectKey
  pendingOps : Array WalOp
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Joint transactional state combining database, object bucket, and transaction manager. -/
structure StoreState (policy : StoragePolicy) where
  db       : DbState
  bucket   : BucketState policy
  nextTxId : TxId
  nextSeq  : SeqNo
  activeTx : Option PendingTx

namespace StoreState

/-- Empty initial store with `nextTxId = 1` and `nextSeq = 1`. -/
def empty (policy : StoragePolicy := {}) : StoreState policy where
  db       := DbState.empty
  bucket   := BucketState.empty policy
  nextTxId := ⟨1⟩
  nextSeq  := ⟨1⟩
  activeTx := none

instance {policy : StoragePolicy} : Inhabited (StoreState policy) := ⟨empty policy⟩

/-- Counts live posts referencing object `k`. -/
def countPostRefs (db : DbState) (k : ObjectKey) : Nat :=
  db.posts.foldl
    (fun acc _ p =>
      match p.image with
      | some ref => if ref.key = k then acc + 1 else acc
      | none => acc)
    0

/-- Cross-engine consistency invariant tying DB posts and bucket reference counts. -/
structure Invariant {policy : StoragePolicy} (s : StoreState policy) : Prop where
  db_inv        : DbInvariant s.db
  bucket_inv    : BucketInvariant s.bucket
  nextTxId_pos  : 1 ≤ s.nextTxId.val.toNat
  nextSeq_gt    : s.db.lastSeq.val.toNat < s.nextSeq.val.toNat
  ref_integrity : ∀ (id : PostId) (p : Post) (ref : ImageRef),
    s.db.posts[id]? = some p → p.image = some ref →
      ∃ (bm : BucketEntryMeta policy.segmentSize),
        s.bucket.objects[ref.key]? = some bm ∧
        bm.mime = ref.mime ∧
        bm.byteSize = ref.byteSize.toNat ∧
        1 ≤ bm.refCount
  refcount_exact : ∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
    s.bucket.objects[k]? = some bm → bm.refCount = countPostRefs s.db k

/-- Opens a serialized write transaction if none is currently active. -/
def beginTx {policy : StoragePolicy} (s : StoreState policy) :
    Except CoreError (TxId × StoreState policy) :=
  if s.activeTx.isSome then
    .error .txAlreadyActive
  else if s.nextTxId.val.toNat + 1 ≥ 2 ^ 64 then
    .error (.invariantViolated "TxId overflow")
  else
    let txId := s.nextTxId
    let pending : PendingTx := { txId := txId, stagedKeys := #[], pendingOps := #[.beginTx] }
    .ok (txId, { s with nextTxId := ⟨s.nextTxId.val + 1⟩, activeTx := some pending })

/-- Stages an image into the bucket during an active transaction (leaving `refCount = 0`). -/
def stageImage {policy : StoragePolicy} (s : StoreState policy)
    (mime : MimeType) (bytes : ByteArray) :
    Except CoreError (ImageRef × StoreState policy) :=
  match s.activeTx with
  | none => .error .txNotActive
  | some pending =>
    match s.bucket.putObject mime bytes with
    | .error e => .error e
    | .ok (key, bucket') =>
      let ref : ImageRef := { key := key, mime := mime, byteSize := bytes.size.toUInt32 }
      let pending' : PendingTx := { pending with stagedKeys := pending.stagedKeys.push key }
      .ok (ref, { s with bucket := bucket', activeTx := some pending' })

private def checkAndIncRef {policy : StoragePolicy} (b : BucketState policy)
    (ref? : Option ImageRef) : Except CoreError (BucketState policy) :=
  match ref? with
  | none => .ok b
  | some ref =>
    match b.objects[ref.key]? with
    | none => .error (.objectNotFound ref.key)
    | some bm =>
      if bm.mime != ref.mime || bm.byteSize != ref.byteSize.toNat then
        .error (.invariantViolated "ImageRef metadata mismatch")
      else
        b.incRef ref.key

private def applyImageRefDelta {policy : StoragePolicy} (b : BucketState policy)
    (oldRef? newRef? : Option ImageRef) : Except CoreError (BucketState policy) :=
  match oldRef?, newRef? with
  | none, none => .ok b
  | some oldRef, none => b.decRef oldRef.key
  | none, some newRef => checkAndIncRef b (some newRef)
  | some oldRef, some newRef =>
    if oldRef.key = newRef.key then
      match b.objects[newRef.key]? with
      | none => .error (.objectNotFound newRef.key)
      | some bm =>
        if bm.mime != newRef.mime || bm.byteSize != newRef.byteSize.toNat then
          .error (.invariantViolated "ImageRef metadata mismatch")
        else
          .ok b
    else
      match b.decRef oldRef.key with
      | .error e => .error e
      | .ok bDec => checkAndIncRef bDec (some newRef)

/-- Atomically commits a new post and increments any referenced object's refcount. -/
def commitCreate {policy : StoragePolicy} (s : StoreState policy) (now : Int64)
    (draft : ValidPostDraft) (imgRef? : Option ImageRef) :
    Except CoreError (Post × StoreState policy) :=
  match s.activeTx with
  | none => .error .txNotActive
  | some _ =>
    match checkAndIncRef s.bucket imgRef? with
    | .error e => .error e
    | .ok bucket' =>
      match s.db.createPost now draft imgRef? with
      | .error e => .error e
      | .ok (post, db') =>
        if db'.lastSeq.val.toNat + 1 ≥ 2 ^ 64 then
          .error (.invariantViolated "SeqNo overflow")
        else
          .ok (post,
            { s with
              db := db'
              bucket := bucket'
              nextSeq := ⟨db'.lastSeq.val + 1⟩
              activeTx := none })

/-- Atomically commits a post update and applies net image reference-count deltas. -/
def commitUpdate {policy : StoragePolicy} (s : StoreState policy) (id : PostId)
    (now : Int64) (patch : ValidPostPatch) (newImgRef? : Option ImageRef) :
    Except CoreError (Post × StoreState policy) :=
  match s.activeTx with
  | none => .error .txNotActive
  | some _ =>
    match s.db.getPost id with
    | none => .error (.postNotFound id)
    | some oldPost =>
      match s.db.updatePost id now patch newImgRef? with
      | .error e => .error e
      | .ok (post, db') =>
        if db'.lastSeq.val.toNat + 1 ≥ 2 ^ 64 then
          .error (.invariantViolated "SeqNo overflow")
        else
          match applyImageRefDelta s.bucket oldPost.image post.image with
          | .error e => .error e
          | .ok bucket' =>
            .ok (post,
              { s with
                db := db'
                bucket := bucket'
                nextSeq := ⟨db'.lastSeq.val + 1⟩
                activeTx := none })

/-- Atomically commits a post deletion and decrements any released image's refcount. -/
def commitDelete {policy : StoragePolicy} (s : StoreState policy) (id : PostId) :
    Except CoreError (Option ImageRef × StoreState policy) :=
  match s.activeTx with
  | none => .error .txNotActive
  | some _ =>
    match s.db.deletePost id with
    | .error e => .error e
    | .ok (rel?, db') =>
      let bucketRes : Except CoreError (BucketState policy) := match rel? with
        | none => .ok s.bucket
        | some ref => s.bucket.decRef ref.key
      match bucketRes with
      | .error e => .error e
      | .ok bucket' =>
        .ok (rel?, { s with db := db', bucket := bucket', activeTx := none })

/-- Aborts the active transaction, leaving committed DB state and live refcounts unchanged. -/
def abortTx {policy : StoragePolicy} (s : StoreState policy) :
    Except CoreError (StoreState policy) :=
  match s.activeTx with
  | none => .error .txNotActive
  | some _ => .ok { s with activeTx := none }

/-- Runs bucket garbage collection when no transaction is active. -/
def runGC {policy : StoragePolicy} (s : StoreState policy) :
    Except CoreError (StoreState policy) :=
  if s.activeTx.isSome then
    .error .txAlreadyActive
  else
    .ok { s with bucket := s.bucket.gcStep }

/-- Runs DB and bucket compaction when no transaction is active. -/
def runCompact {policy : StoragePolicy} (s : StoreState policy) :
    Except CoreError (StoreState policy) :=
  if s.activeTx.isSome then
    .error .txAlreadyActive
  else
    match s.bucket.compactBucket with
    | .error e => .error e
    | .ok bucket' => .ok { s with db := s.db.compactDb, bucket := bucket' }

end StoreState

abbrev CrossInvariant {policy : StoragePolicy} (s : StoreState policy) : Prop :=
  StoreState.Invariant s

namespace StoreState

private def postRefDelta (p : Post) (k : ObjectKey) : Nat :=
  match p.image with
  | some ref => if ref.key = k then 1 else 0
  | none => 0

@[instance_reducible]
private def decBEq (α : Type) [DecidableEq α] : BEq α :=
  ⟨fun a b => decide (a = b)⟩

private theorem decBEq_lawful (α : Type) [DecidableEq α] : @LawfulBEq α (decBEq α) :=
  @LawfulBEq.mk α (decBEq α) ⟨fun {a} => by simp⟩
    (fun {a b} h => by simpa using h)

private theorem uint64_succ_toNat {x : UInt64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  exact Nat.mod_eq_of_lt h

private theorem compare_eq_iff_eq {α : Type} [Ord α] [Std.LawfulEqOrd α] {a b : α} :
    compare a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqOrd.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self (cmp := compare)⟩

private theorem foldl_add_perm {α : Type} (f : α → Nat) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (init : Nat) :
    l₁.foldl (fun acc x => acc + f x) init = l₂.foldl (fun acc x => acc + f x) init := by
  induction h generalizing init with
  | nil => rfl
  | cons _ _ ih => exact ih _
  | swap x y l => dsimp only [List.foldl]; simp only [Nat.add_right_comm]
  | trans _ _ ih₁ ih₂ => exact (ih₁ init).trans (ih₂ init)

private theorem foldl_add_init {α : Type} (f : α → Nat) (l : List α) (a b : Nat) :
    l.foldl (fun acc x => acc + f x) (a + b) = a + l.foldl (fun acc x => acc + f x) b := by
  induction l generalizing a b with
  | nil => simp
  | cons x xs ih =>
    dsimp only [List.foldl]
    rw [Nat.add_assoc, ih]

private theorem nodup_perm_of_mem_iff {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hMem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.Perm l₂ := by
  letI : BEq α := decBEq α
  haveI : LawfulBEq α := decBEq_lawful α
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact .nil
    | cons y ys => exact absurd ((hMem y).mpr List.mem_cons_self) List.not_mem_nil
  | cons x xs ih =>
    have hxIn : x ∈ l₂ := (hMem x).mp List.mem_cons_self
    have hPerm₂ : l₂.Perm (x :: l₂.erase x) := List.perm_cons_erase hxIn
    have hNodup₂ : (x :: l₂.erase x).Nodup := (hPerm₂.nodup_iff).mp h₂
    have hxNotInXs : x ∉ xs := (List.nodup_cons.mp h₁).1
    have hxNotInErase : x ∉ l₂.erase x := (List.nodup_cons.mp hNodup₂).1
    refine .trans (.cons x (ih (List.nodup_cons.mp h₁).2 (List.nodup_cons.mp hNodup₂).2 ?_)) hPerm₂.symm
    intro z
    constructor
    · intro hz
      have hNe : z ≠ x := fun hzx => hxNotInXs (hzx ▸ hz)
      have hzL₂ : z ∈ l₂ := (hMem z).mp (List.mem_cons_of_mem x hz)
      have hzPerm : z ∈ x :: l₂.erase x := hPerm₂.subset hzL₂
      rcases List.mem_cons.mp hzPerm with rfl | hzE
      · exact absurd rfl hNe
      · exact hzE
    · intro hz
      have hNe : z ≠ x := fun hzx => hxNotInErase (hzx ▸ hz)
      have hzL₂ : z ∈ l₂ := hPerm₂.symm.subset (List.mem_cons_of_mem x hz)
      have hzL₁ : z ∈ x :: xs := (hMem z).mpr hzL₂
      rcases List.mem_cons.mp hzL₁ with rfl | hzXs
      · exact absurd rfl hNe
      · exact hzXs

private theorem nodup_toList_map {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (m : Std.ExtTreeMap α β) : m.toList.Nodup := by
  have hDist := Std.ExtTreeMap.distinct_keys_toList (t := m)
  exact hDist.imp fun {a b} hcmp heq =>
    hcmp (by rw [heq, Std.ReflCmp.compare_self (cmp := compare)])

private theorem countPostRefs_eq_foldl (db : DbState) (k : ObjectKey) :
    countPostRefs db k =
      db.posts.toList.foldl (fun acc kv => acc + postRefDelta kv.2 k) 0 := by
  unfold countPostRefs
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  congr 1
  funext acc kv
  unfold postRefDelta
  cases kv.2.image with
  | none => simp
  | some ref => by_cases h : ref.key = k <;> simp [h]

private theorem countPostRefs_pos_of_mem {db : DbState} {id : PostId} {p : Post} {ref : ImageRef}
    (hGet : db.posts[id]? = some p) (hImg : p.image = some ref) :
    1 ≤ countPostRefs db ref.key := by
  rw [countPostRefs_eq_foldl]
  have hMem : (id, p) ∈ db.posts.toList := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hGet
  letI : BEq (PostId × Post) := decBEq (PostId × Post)
  haveI : LawfulBEq (PostId × Post) := decBEq_lawful (PostId × Post)
  have hPerm := List.perm_cons_erase hMem
  rw [foldl_add_perm (fun kv => postRefDelta kv.2 ref.key) hPerm 0]
  dsimp only [List.foldl]
  have hDelta : postRefDelta p ref.key = 1 := by simp [postRefDelta, hImg]
  rw [Nat.zero_add, hDelta, ← Nat.add_zero 1,
    foldl_add_init (fun kv : PostId × Post => postRefDelta kv.2 ref.key) _ 1 0]
  omega

private theorem countPostRefs_insert_none {db : DbState} {id : PostId} {p : Post}
    (hNone : db.posts[id]? = none) (k : ObjectKey) :
    countPostRefs { db with posts := db.posts.insert id p } k =
      countPostRefs db k + postRefDelta p k := by
  rw [countPostRefs_eq_foldl, countPostRefs_eq_foldl]
  dsimp only
  have hNotMem : (id, p) ∉ db.posts.toList := by
    intro hm
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, hNone] at hm
    simp at hm
  have hNodupIns : (db.posts.insert id p).toList.Nodup := nodup_toList_map _
  have hNodupCons : ((id, p) :: db.posts.toList).Nodup :=
    List.nodup_cons.mpr ⟨hNotMem, nodup_toList_map _⟩
  have hPerm : (db.posts.insert id p).toList.Perm ((id, p) :: db.posts.toList) := by
    apply nodup_perm_of_mem_iff hNodupIns hNodupCons
    intro ⟨a, b⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, List.mem_cons,
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
    by_cases hEq : id = a
    · subst hEq
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · intro hb; exact .inl hb.symm
      · rintro (hpb | hOld)
        · exact hpb.symm
        · rw [hNone] at hOld; simp at hOld
    · have hNe : ¬ (a = id) := fun h => hEq h.symm
      simp only [hEq, ↓reduceIte, Prod.mk.injEq, hNe, false_and, false_or]
  rw [foldl_add_perm (fun kv => postRefDelta kv.2 k) hPerm 0]
  dsimp only [List.foldl]
  rw [Nat.zero_add, ← Nat.add_zero (postRefDelta p k),
    foldl_add_init (fun kv : PostId × Post => postRefDelta kv.2 k) db.posts.toList (postRefDelta p k) 0,
    Nat.add_comm]
  simp only [Nat.add_zero]

private theorem countPostRefs_erase_some {db : DbState} {id : PostId} {old : Post}
    (hSome : db.posts[id]? = some old) (k : ObjectKey) :
    countPostRefs db k =
      countPostRefs { db with posts := db.posts.erase id } k + postRefDelta old k := by
  rw [countPostRefs_eq_foldl, countPostRefs_eq_foldl]
  dsimp only
  have hNotMem : (id, old) ∉ (db.posts.erase id).toList := by
    intro hm
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, Std.ExtTreeMap.getElem?_erase_self] at hm
    simp at hm
  have hNodupOld : db.posts.toList.Nodup := nodup_toList_map _
  have hNodupCons : ((id, old) :: (db.posts.erase id).toList).Nodup :=
    List.nodup_cons.mpr ⟨hNotMem, nodup_toList_map _⟩
  have hPerm : db.posts.toList.Perm ((id, old) :: (db.posts.erase id).toList) := by
    apply nodup_perm_of_mem_iff hNodupOld hNodupCons
    intro ⟨a, b⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, List.mem_cons,
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq]
    by_cases hEq : id = a
    · subst hEq
      simp only [↓reduceIte, Prod.mk.injEq, true_and, hSome, Option.some.injEq]
      constructor
      · intro hb; exact .inl hb.symm
      · rintro (hpb | hNone)
        · exact hpb.symm
        · simp at hNone
    · have hNe : ¬ (a = id) := fun h => hEq h.symm
      simp only [hEq, ↓reduceIte, Prod.mk.injEq, hNe, false_and, false_or]
  rw [foldl_add_perm (fun kv => postRefDelta kv.2 k) hPerm 0]
  dsimp only [List.foldl]
  rw [Nat.zero_add, ← Nat.add_zero (postRefDelta old k),
    foldl_add_init (fun kv : PostId × Post => postRefDelta kv.2 k) _ (postRefDelta old k) 0,
    Nat.add_comm]
  simp only [Nat.add_zero]

private theorem countPostRefs_insert_some {db : DbState} {id : PostId} {old new : Post}
    (hSome : db.posts[id]? = some old) (k : ObjectKey) :
    countPostRefs { db with posts := db.posts.insert id new } k + postRefDelta old k =
      countPostRefs db k + postRefDelta new k := by
  have hErased : (db.posts.erase id).insert id new = db.posts.insert id new := by
    apply Std.ExtTreeMap.ext_getElem?
    intro a
    simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq]
    split <;> rfl
  have hErasedNone : (db.posts.erase id)[id]? = none := Std.ExtTreeMap.getElem?_erase_self
  have h1 := countPostRefs_insert_none (db := { db with posts := db.posts.erase id }) (id := id) (p := new) hErasedNone k
  dsimp only at h1
  rw [hErased] at h1
  have h2 := countPostRefs_erase_some hSome k
  omega

theorem empty_invariant (policy : StoragePolicy) : Invariant (empty policy) where
  db_inv := DbState.empty_invariant
  bucket_inv := BucketState.empty_invariant policy
  nextTxId_pos := by change 1 ≤ 1; exact Nat.le_refl _
  nextSeq_gt := by change 0 < 1; exact Nat.lt_succ_self 0
  ref_integrity := by intro id p ref h; simp [empty, DbState.empty] at h
  refcount_exact := by intro k bm h; simp [empty, BucketState.empty] at h

theorem beginTx_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy} {txId : TxId}
    (hInv : Invariant s) (hOk : s.beginTx = .ok (txId, s')) :
    Invariant s' := by
  unfold beginTx at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · next hNoOv =>
      simp only [Nat.not_le] at hNoOv
      simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, rfl⟩
      have hSucc : (s.nextTxId.val + 1).toNat = s.nextTxId.val.toNat + 1 := uint64_succ_toNat hNoOv
      refine ⟨hInv.db_inv, hInv.bucket_inv, ?_, hInv.nextSeq_gt, hInv.ref_integrity, hInv.refcount_exact⟩
      dsimp only; rw [hSucc]; omega

private theorem foldl_add_pos {α : Type} (f : α → Nat) (xs : List α) (init : Nat)
    (h : 0 < xs.foldl (fun acc x => acc + f x) init) :
    0 < init ∨ ∃ x ∈ xs, 0 < f x := by
  induction xs generalizing init with
  | nil => exact .inl h
  | cons x xs ih =>
    dsimp only [List.foldl] at h
    rcases ih (init + f x) h with hPos | ⟨y, hy, hfy⟩
    · by_cases hi : 0 < init
      · exact .inl hi
      · exact .inr ⟨x, List.mem_cons_self, by omega⟩
    · exact .inr ⟨y, List.mem_cons_of_mem x hy, hfy⟩

private theorem exists_post_of_countPostRefs_pos {db : DbState} {k : ObjectKey}
    (hPos : 0 < countPostRefs db k) :
    ∃ (id : PostId) (p : Post) (ref : ImageRef),
      db.posts[id]? = some p ∧ p.image = some ref ∧ ref.key = k := by
  rw [countPostRefs_eq_foldl] at hPos
  rcases foldl_add_pos (fun kv : PostId × Post => postRefDelta kv.2 k) db.posts.toList 0 hPos with h0 | ⟨⟨id, p⟩, hmem, hdelta⟩
  · omega
  · unfold postRefDelta at hdelta
    cases himg : p.image with
    | none => rw [himg] at hdelta; simp at hdelta
    | some ref =>
      rw [himg] at hdelta
      dsimp only at hdelta
      by_cases hk : ref.key = k
      · exact ⟨id, p, ref, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem, himg, hk⟩
      · simp [hk] at hdelta

theorem stageImage_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    {mime : MimeType} {bytes : ByteArray} {ref : ImageRef}
    (hInv : Invariant s) (hOk : s.stageImage mime bytes = .ok (ref, s')) :
    Invariant s' := by
  unfold stageImage at hOk
  cases hTx : s.activeTx with
  | none => rw [hTx] at hOk; simp at hOk
  | some pending =>
    rw [hTx] at hOk; dsimp only at hOk
    cases hPut : s.bucket.putObject mime bytes with
    | error e => rw [hPut] at hOk; simp at hOk
    | ok res =>
      rw [hPut] at hOk
      rcases res with ⟨key, bucket'⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, rfl⟩
      have hBInv := BucketState.putObject_preserves_invariant hInv.bucket_inv hPut
      have ⟨hPresObj, hNewObj⟩ := BucketState.putObject_objects_spec hInv.bucket_inv hPut
      refine ⟨hInv.db_inv, hBInv, hInv.nextTxId_pos, hInv.nextSeq_gt, ?_, ?_⟩
      · intro id p r hp hr
        rcases hInv.ref_integrity id p r hp hr with ⟨bm, hbm, hMime, hSz, hPos⟩
        exact ⟨bm, hPresObj r.key bm hbm, hMime, hSz, hPos⟩
      · intro k bm hbm
        rcases hNewObj k bm hbm with hOld | ⟨hEqK, hZero, hNone⟩
        · exact hInv.refcount_exact k bm hOld
        · subst hEqK
          rw [hZero]
          by_cases hC : countPostRefs s.db k = 0
          · exact hC.symm
          · exfalso
            rcases exists_post_of_countPostRefs_pos (Nat.pos_of_ne_zero hC) with
              ⟨pid, p, r, hp, hr, rfl⟩
            rcases hInv.ref_integrity pid p r hp hr with ⟨bm0, hbm0, _⟩
            rw [hNone] at hbm0
            simp at hbm0

private theorem incRef_objects_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {key : ObjectKey}
    (hOk : b.incRef key = .ok b') :
    (∃ (bm0 : BucketEntryMeta policy.segmentSize),
      b.objects[key]? = some bm0 ∧
      b'.objects[key]? = some { bm0 with refCount := bm0.refCount + 1 }) ∧
    (∀ (k : ObjectKey), k ≠ key → b'.objects[k]? = b.objects[k]?) := by
  unfold BucketState.incRef at hOk
  cases hk : b.objects[key]? with
  | none => rw [hk] at hOk; simp at hOk
  | some bm0 =>
    rw [hk] at hOk
    simp only [Except.ok.injEq] at hOk
    subst hOk
    refine ⟨⟨bm0, rfl, by simp⟩, ?_⟩
    intro k hNe
    have hNe' : ¬ (key = k) := fun h => hNe h.symm
    dsimp only
    simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe', ↓reduceIte]

private theorem decRef_objects_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {key : ObjectKey}
    (hOk : b.decRef key = .ok b') :
    (∃ (bm0 : BucketEntryMeta policy.segmentSize),
      b.objects[key]? = some bm0 ∧ 1 ≤ bm0.refCount ∧
      b'.objects[key]? = some { bm0 with refCount := bm0.refCount - 1 }) ∧
    (∀ (k : ObjectKey), k ≠ key → b'.objects[k]? = b.objects[k]?) := by
  unfold BucketState.decRef at hOk
  cases hk : b.objects[key]? with
  | none => rw [hk] at hOk; simp at hOk
  | some bm0 =>
    rw [hk] at hOk
    dsimp only at hOk
    by_cases hz : bm0.refCount == 0
    · simp [hz] at hOk
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hOk
      subst hOk
      have hPos : 1 ≤ bm0.refCount := by
        have hnz : bm0.refCount ≠ 0 := by simpa [beq_iff_eq] using hz
        omega
      refine ⟨⟨bm0, rfl, hPos, by simp⟩, ?_⟩
      intro k hNe
      have hNe' : ¬ (key = k) := fun h => hNe h.symm
      dsimp only
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe', ↓reduceIte]

private def refKeyDelta (ref? : Option ImageRef) (k : ObjectKey) : Nat :=
  match ref? with
  | some ref => if ref.key = k then 1 else 0
  | none => 0

private theorem mime_eq_of_beq {a b : MimeType} (h : (a == b) = true) : a = b := by
  revert h; cases a <;> cases b <;> decide

private theorem mime_ne_of_beq_false {a b : MimeType} (h : (a != b) = false) : a = b := by
  revert h; cases a <;> cases b <;> decide

private theorem postRefDelta_eq_refKeyDelta (p : Post) (k : ObjectKey) :
    postRefDelta p k = refKeyDelta p.image k := rfl

private theorem checkAndIncRef_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {ref? : Option ImageRef}
    (hInv : BucketInvariant b)
    (hOk : checkAndIncRef b ref? = .ok b') :
    BucketInvariant b' ∧
    (∀ (k : ObjectKey) (bm' : BucketEntryMeta policy.segmentSize),
      b'.objects[k]? = some bm' →
      ∃ (bm : BucketEntryMeta policy.segmentSize),
        b.objects[k]? = some bm ∧ bm'.mime = bm.mime ∧ bm'.byteSize = bm.byteSize ∧
        bm'.refCount = bm.refCount + refKeyDelta ref? k) ∧
    (∀ (ref : ImageRef), ref? = some ref →
      ∃ (bm' : BucketEntryMeta policy.segmentSize),
        b'.objects[ref.key]? = some bm' ∧ bm'.mime = ref.mime ∧
        bm'.byteSize = ref.byteSize.toNat ∧ 1 ≤ bm'.refCount) := by
  unfold checkAndIncRef at hOk
  cases ref? with
  | none =>
    simp only [Except.ok.injEq] at hOk
    subst hOk
    refine ⟨hInv, ?_, fun _ h => by cases h⟩
    intro k bm hbm
    exact ⟨bm, hbm, rfl, rfl, by simp [refKeyDelta]⟩
  | some ref =>
    dsimp only at hOk
    cases hk : b.objects[ref.key]? with
    | none => rw [hk] at hOk; simp at hOk
    | some bm0 =>
      rw [hk] at hOk
      dsimp only at hOk
      by_cases hBad : (bm0.mime != ref.mime || bm0.byteSize != ref.byteSize.toNat) = true
      · simp [hBad] at hOk
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hOk
        have hBInv' := BucketState.incRef_preserves_invariant hInv hOk
        have ⟨⟨bmInc, hIncOld, hIncNew⟩, hIncOther⟩ := incRef_objects_spec hOk
        rw [hk] at hIncOld
        injection hIncOld with hBmEq
        subst hBmEq
        have hMeta : bm0.mime = ref.mime ∧ bm0.byteSize = ref.byteSize.toNat := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hBad
          have h1 : (bm0.mime != ref.mime) = false := by
            by_cases hm : (bm0.mime != ref.mime) = true
            · exact absurd (.inl hm) hBad
            · cases hb : (bm0.mime != ref.mime) <;> simp_all
          have h2 : bm0.byteSize = ref.byteSize.toNat := by
            by_cases hs : bm0.byteSize ≠ ref.byteSize.toNat
            · exact absurd (.inr hs) hBad
            · omega
          exact ⟨mime_ne_of_beq_false h1, h2⟩
        refine ⟨hBInv', ?_, ?_⟩
        · intro k bm' hbm'
          by_cases hEq : k = ref.key
          · subst hEq
            rw [hIncNew] at hbm'
            injection hbm' with hmEq
            subst hmEq
            exact ⟨bm0, hk, rfl, rfl, by simp [refKeyDelta]⟩
          · rw [hIncOther k hEq] at hbm'
            have hNe' : ref.key ≠ k := fun h => hEq h.symm
            exact ⟨bm', hbm', rfl, rfl, by simp [refKeyDelta, hNe']⟩
        · intro r hr
          injection hr with hrEq
          subst hrEq
          exact ⟨{ bm0 with refCount := bm0.refCount + 1 }, hIncNew, hMeta.1, hMeta.2, by dsimp only; omega⟩

private theorem applyImageRefDelta_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {oldRef? newRef? : Option ImageRef}
    (hInv : BucketInvariant b)
    (hOldPos : ∀ oldRef, oldRef? = some oldRef →
      ∃ (bm : BucketEntryMeta policy.segmentSize), b.objects[oldRef.key]? = some bm ∧ 1 ≤ bm.refCount)
    (hOk : applyImageRefDelta b oldRef? newRef? = .ok b') :
    BucketInvariant b' ∧
    (∀ (k : ObjectKey) (bm' : BucketEntryMeta policy.segmentSize),
      b'.objects[k]? = some bm' →
      ∃ (bm : BucketEntryMeta policy.segmentSize),
        b.objects[k]? = some bm ∧ bm'.mime = bm.mime ∧ bm'.byteSize = bm.byteSize ∧
        bm'.refCount + refKeyDelta oldRef? k = bm.refCount + refKeyDelta newRef? k) ∧
    (∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
      b.objects[k]? = some bm → ∃ bm', b'.objects[k]? = some bm') ∧
    (∀ (nr : ImageRef), newRef? = some nr →
      ∃ (bm' : BucketEntryMeta policy.segmentSize),
        b'.objects[nr.key]? = some bm' ∧ bm'.mime = nr.mime ∧
        bm'.byteSize = nr.byteSize.toNat ∧ 1 ≤ bm'.refCount) := by
  unfold applyImageRefDelta at hOk
  cases oldRef? with
  | none =>
    cases newRef? with
    | none =>
      simp only [Except.ok.injEq] at hOk; subst hOk
      exact ⟨hInv, fun k bm h => ⟨bm, h, rfl, rfl, rfl⟩, fun k bm h => ⟨bm, h⟩, fun _ h => by cases h⟩
    | some nr =>
      have ⟨hBInv', hObj', hNew⟩ := checkAndIncRef_spec hInv hOk
      refine ⟨hBInv', ?_, ?_, hNew⟩
      · intro k bm' hbm'
        rcases hObj' k bm' hbm' with ⟨bm, hbm, h1, h2, h3⟩
        exact ⟨bm, hbm, h1, h2, by simp [refKeyDelta, h3]⟩
      · intro k bm hbm
        unfold checkAndIncRef at hOk
        dsimp only at hOk
        cases hnr : b.objects[nr.key]? with
        | none => rw [hnr] at hOk; simp at hOk
        | some bm0 =>
          rw [hnr] at hOk; dsimp only at hOk
          split at hOk
          · simp at hOk
          · have ⟨⟨bmInc, _, hIncNew⟩, hIncOther⟩ := incRef_objects_spec hOk
            by_cases hEq : k = nr.key
            · subst hEq; exact ⟨_, hIncNew⟩
            · exact ⟨bm, by rw [hIncOther k hEq]; exact hbm⟩
  | some oldRef =>
    cases newRef? with
    | none =>
      dsimp only at hOk
      have hBInv' := BucketState.decRef_preserves_invariant hInv hOk
      have ⟨⟨bm0, hOld, hPos, hNew⟩, hOther⟩ := decRef_objects_spec hOk
      refine ⟨hBInv', ?_, ?_, fun _ h => by cases h⟩
      · intro k bm' hbm'
        by_cases hEq : k = oldRef.key
        · subst hEq
          rw [hNew] at hbm'
          injection hbm' with hmEq; subst hmEq
          refine ⟨bm0, hOld, rfl, rfl, ?_⟩
          simp only [refKeyDelta, ↓reduceIte]
          omega
        · rw [hOther k hEq] at hbm'
          have hNe' : oldRef.key ≠ k := fun h => hEq h.symm
          exact ⟨bm', hbm', rfl, rfl, by simp [refKeyDelta, hNe']⟩
      · intro k bm hbm
        by_cases hEq : k = oldRef.key
        · subst hEq; exact ⟨_, hNew⟩
        · exact ⟨bm, by rw [hOther k hEq]; exact hbm⟩
    | some nr =>
      dsimp only at hOk
      by_cases hSame : oldRef.key = nr.key
      · simp only [hSame, ↓reduceIte] at hOk
        cases hk : b.objects[nr.key]? with
        | none => rw [hk] at hOk; simp at hOk
        | some bm0 =>
          rw [hk] at hOk; dsimp only at hOk
          by_cases hBad : (bm0.mime != nr.mime || bm0.byteSize != nr.byteSize.toNat) = true
          · simp [hBad] at hOk
          · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hOk
            subst hOk
            have hMeta : bm0.mime = nr.mime ∧ bm0.byteSize = nr.byteSize.toNat := by
              simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hBad
              have h1 : (bm0.mime != nr.mime) = false := by
                by_cases hm : (bm0.mime != nr.mime) = true
                · exact absurd (.inl hm) hBad
                · cases hb : (bm0.mime != nr.mime) <;> simp_all
              have h2 : bm0.byteSize = nr.byteSize.toNat := by
                by_cases hs : bm0.byteSize ≠ nr.byteSize.toNat
                · exact absurd (.inr hs) hBad
                · omega
              exact ⟨mime_ne_of_beq_false h1, h2⟩
            rcases hOldPos oldRef rfl with ⟨bmOld, hbmOld, hPos⟩
            rw [hSame, hk] at hbmOld
            injection hbmOld with hBmEq; subst hBmEq
            refine ⟨hInv, ?_, fun k bm h => ⟨bm, h⟩, ?_⟩
            · intro k bm' hbm'
              exact ⟨bm', hbm', rfl, rfl, by simp [refKeyDelta, hSame]⟩
            · intro r hr; injection hr with hrEq; subst hrEq
              exact ⟨bm0, hk, hMeta.1, hMeta.2, hPos⟩
      · simp only [hSame, ↓reduceIte] at hOk
        cases hDec : b.decRef oldRef.key with
        | error e => rw [hDec] at hOk; simp at hOk
        | ok bDec =>
          rw [hDec] at hOk; dsimp only at hOk
          have hBDec := BucketState.decRef_preserves_invariant hInv hDec
          have ⟨⟨bm0, hOld, hPos, hNew⟩, hOther⟩ := decRef_objects_spec hDec
          have ⟨hBInv', hIncObj, hIncNew⟩ := checkAndIncRef_spec hBDec hOk
          refine ⟨hBInv', ?_, ?_, hIncNew⟩
          · intro k bm' hbm'
            rcases hIncObj k bm' hbm' with ⟨bmDec, hbmDec, hm1, hm2, hm3⟩
            by_cases hEqOld : k = oldRef.key
            · subst hEqOld
              rw [hNew] at hbmDec
              injection hbmDec with hDecEq; subst hDecEq
              have hNe' : nr.key ≠ oldRef.key := fun h => hSame h.symm
              refine ⟨bm0, hOld, hm1, hm2, ?_⟩
              simp only [refKeyDelta, ↓reduceIte, hNe'] at hm3 ⊢
              omega
            · rw [hOther k hEqOld] at hbmDec
              refine ⟨bmDec, hbmDec, hm1, hm2, ?_⟩
              have hNeOld' : oldRef.key ≠ k := fun h => hEqOld h.symm
              simp only [refKeyDelta, hNeOld', ↓reduceIte] at hm3 ⊢
              exact hm3
          · intro k bm hbm
            have hInDec : ∃ bmDec, bDec.objects[k]? = some bmDec := by
              by_cases hEq : k = oldRef.key
              · subst hEq; exact ⟨_, hNew⟩
              · exact ⟨bm, by rw [hOther k hEq]; exact hbm⟩
            rcases hInDec with ⟨bmDec, hbmDec⟩
            unfold checkAndIncRef at hOk; dsimp only at hOk
            cases hnr : bDec.objects[nr.key]? with
            | none => rw [hnr] at hOk; simp at hOk
            | some bmn =>
              rw [hnr] at hOk; dsimp only at hOk
              split at hOk
              · simp at hOk
              · have ⟨⟨_, _, hIncSelf⟩, hIncOther⟩ := incRef_objects_spec hOk
                by_cases hEq : k = nr.key
                · subst hEq; exact ⟨_, hIncSelf⟩
                · exact ⟨bmDec, by rw [hIncOther k hEq]; exact hbmDec⟩

theorem commitCreate_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    {now : Int64} {draft : ValidPostDraft} {imgRef? : Option ImageRef} {post : Post}
    (hInv : Invariant s) (hOk : s.commitCreate now draft imgRef? = .ok (post, s')) :
    Invariant s' := by
  unfold commitCreate at hOk
  cases hTx : s.activeTx with
  | none => rw [hTx] at hOk; simp at hOk
  | some pending =>
    rw [hTx] at hOk; dsimp only at hOk
    cases hInc : checkAndIncRef s.bucket imgRef? with
    | error e => rw [hInc] at hOk; simp at hOk
    | ok bucket' =>
      rw [hInc] at hOk; dsimp only at hOk
      cases hDb : s.db.createPost now draft imgRef? with
      | error e => rw [hDb] at hOk; simp at hOk
      | ok res =>
        rw [hDb] at hOk; dsimp only at hOk
        rcases res with ⟨post, db'⟩
        split at hOk
        · simp at hOk
        · next hSeqOv =>
          simp only [Nat.not_le] at hSeqOv
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          have hDbInv' := DbState.createPost_preserves_invariant hInv.db_inv hDb
          have ⟨hBInv', hIncObj, hIncNew⟩ := checkAndIncRef_spec hInv.bucket_inv hInc
          have hSucc : (db'.lastSeq.val + 1).toNat = db'.lastSeq.val.toNat + 1 :=
            uint64_succ_toNat hSeqOv
          have hNoneOld : s.db.posts[s.db.nextPostId]? = none :=
            DbState.getPost_eq_none_of_ge_next hInv.db_inv (Nat.le_refl _)
          have hDbEq : ∃ seq, db' = {
              posts := s.db.posts.insert s.db.nextPostId post
              feedIndex := s.db.feedIndex.insert (FeedKey.ofPost post) s.db.nextPostId
              tombstones := s.db.tombstones
              nextPostId := ⟨s.db.nextPostId.val + 1⟩
              lastSeq := seq } ∧ post.id = s.db.nextPostId ∧ post.image = imgRef? := by
            unfold DbState.createPost at hDb
            split at hDb
            · simp at hDb
            · simp only [Except.ok.injEq, Prod.mk.injEq] at hDb
              rcases hDb with ⟨rfl, rfl⟩
              exact ⟨_, rfl, rfl, rfl⟩
          rcases hDbEq with ⟨seq, hDbStruct, hPostId, hPostImg⟩
          have hCountEq : ∀ k, countPostRefs db' k = countPostRefs s.db k + refKeyDelta imgRef? k := by
            intro k
            have hIns := countPostRefs_insert_none (db := s.db) (id := s.db.nextPostId) (p := post) hNoneOld k
            have hPostsEq : db'.posts = s.db.posts.insert s.db.nextPostId post := by
              rw [hDbStruct]
            have hSameC : countPostRefs db' k =
                countPostRefs { s.db with posts := s.db.posts.insert s.db.nextPostId post } k := by
              simp only [countPostRefs, hPostsEq]
            rw [hSameC, hIns, postRefDelta_eq_refKeyDelta, hPostImg]
          refine ⟨hDbInv', hBInv', hInv.nextTxId_pos, ?_, ?_, ?_⟩
          · dsimp only; rw [hSucc]; omega
          · intro id p0 r hp0 hr0
            rw [hDbStruct] at hp0
            dsimp only at hp0
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hp0
            split at hp0
            · next hEq =>
              injection hp0 with hpEq; subst hpEq; subst hEq
              rw [hPostImg] at hr0
              exact hIncNew r hr0
            · rcases hInv.ref_integrity id p0 r hp0 hr0 with ⟨bmOld, hbmOld, hMime, hSz, hPos⟩
              unfold checkAndIncRef at hInc
              cases imgRef? with
              | none =>
                simp only [Except.ok.injEq] at hInc; subst hInc
                exact ⟨bmOld, hbmOld, hMime, hSz, hPos⟩
              | some ir =>
                dsimp only at hInc
                cases hir : s.bucket.objects[ir.key]? with
                | none => rw [hir] at hInc; simp at hInc
                | some bmir =>
                  rw [hir] at hInc; dsimp only at hInc
                  split at hInc
                  · simp at hInc
                  · have ⟨⟨bmInc, hIncOld, hIncSelf⟩, hIncOther⟩ := incRef_objects_spec hInc
                    by_cases hKey : r.key = ir.key
                    · rw [hKey] at hbmOld ⊢
                      rw [hbmOld] at hIncOld; injection hIncOld with hEq; subst hEq
                      exact ⟨_, hIncSelf, hMime, hSz, by dsimp only; omega⟩
                    · rw [hIncOther r.key hKey]
                      exact ⟨bmOld, hbmOld, hMime, hSz, hPos⟩
          · intro k bm' hbm'
            rcases hIncObj k bm' hbm' with ⟨bm, hbm, _, _, hRefEq⟩
            rw [hCountEq k, hRefEq, hInv.refcount_exact k bm hbm]

theorem commitUpdate_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    {id : PostId} {now : Int64} {patch : ValidPostPatch} {newImgRef? : Option ImageRef} {post : Post}
    (hInv : Invariant s) (hOk : s.commitUpdate id now patch newImgRef? = .ok (post, s')) :
    Invariant s' := by
  unfold commitUpdate at hOk
  cases hTx : s.activeTx with
  | none => rw [hTx] at hOk; simp at hOk
  | some pending =>
    rw [hTx] at hOk; dsimp only at hOk
    cases hOld : s.db.getPost id with
    | none => rw [hOld] at hOk; simp at hOk
    | some oldPost =>
      rw [hOld] at hOk; dsimp only at hOk
      cases hDb : s.db.updatePost id now patch newImgRef? with
      | error e => rw [hDb] at hOk; simp at hOk
      | ok res =>
        rw [hDb] at hOk; dsimp only at hOk
        rcases res with ⟨post, db'⟩
        split at hOk
        · simp at hOk
        · next hSeqOv =>
          simp only [Nat.not_le] at hSeqOv
          cases hDelta : applyImageRefDelta s.bucket oldPost.image post.image with
          | error e => rw [hDelta] at hOk; simp at hOk
          | ok bucket' =>
            rw [hDelta] at hOk
            simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
            rcases hOk with ⟨rfl, rfl⟩
            have hDbInv' := DbState.updatePost_preserves_invariant hInv.db_inv hDb
            have hOldPos : ∀ oldRef, oldPost.image = some oldRef →
                ∃ bm, s.bucket.objects[oldRef.key]? = some bm ∧ 1 ≤ bm.refCount := by
              intro oldRef hImg
              rcases hInv.ref_integrity id oldPost oldRef hOld hImg with ⟨bm, hbm, _, _, hPos⟩
              exact ⟨bm, hbm, hPos⟩
            have ⟨hBInv', hDeltaObj, hDeltaKeep, hDeltaNew⟩ :=
              applyImageRefDelta_spec hInv.bucket_inv hOldPos hDelta
            have hSucc : (db'.lastSeq.val + 1).toNat = db'.lastSeq.val.toNat + 1 :=
              uint64_succ_toNat hSeqOv
            have hDbPosts : db'.posts = s.db.posts.insert id post := by
              unfold DbState.updatePost at hDb
              change s.db.posts[id]? = some oldPost at hOld
              rw [hOld] at hDb; dsimp only at hDb
              split at hDb
              · simp at hDb
              · cases hImg : DbState.resolveUpdatedImage oldPost.image patch.imagePatch newImgRef? with
                | error _ => rw [hImg] at hDb; simp at hDb
                | ok img? =>
                  rw [hImg] at hDb
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hDb
                  rcases hDb with ⟨rfl, rfl⟩
                  rfl
            have hCountEq : ∀ k, countPostRefs db' k + refKeyDelta oldPost.image k =
                countPostRefs s.db k + refKeyDelta post.image k := by
              intro k
              have hIns := countPostRefs_insert_some (db := s.db) (id := id) (old := oldPost) (new := post) hOld k
              have hSameC : countPostRefs db' k =
                  countPostRefs { s.db with posts := s.db.posts.insert id post } k := by
                simp only [countPostRefs, hDbPosts]
              rw [hSameC]
              simpa only [postRefDelta_eq_refKeyDelta] using hIns
            have hRefExact' : ∀ (k : ObjectKey) (bm' : BucketEntryMeta policy.segmentSize),
                bucket'.objects[k]? = some bm' → bm'.refCount = countPostRefs db' k := by
              intro k bm' hbm'
              rcases hDeltaObj k bm' hbm' with ⟨bm, hbm, _, _, hRefEq⟩
              have hOldExact := hInv.refcount_exact k bm hbm
              have hC := hCountEq k
              omega
            refine ⟨hDbInv', hBInv', hInv.nextTxId_pos, ?_, ?_, hRefExact'⟩
            · dsimp only; rw [hSucc]; omega
            · intro pid p0 r hp0 hr0
              rw [hDbPosts] at hp0
              simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hp0
              split at hp0
              · next hEq =>
                injection hp0 with hpEq; subst hpEq; subst hEq
                exact hDeltaNew r hr0
              · next hNe =>
                rcases hInv.ref_integrity pid p0 r hp0 hr0 with ⟨bmOld, hbmOld, hMime, hSz, _⟩
                rcases hDeltaKeep r.key bmOld hbmOld with ⟨bm', hbm'⟩
                rcases hDeltaObj r.key bm' hbm' with ⟨bmOld2, hbmOld2, hm1, hm2, _⟩
                rw [hbmOld] at hbmOld2; injection hbmOld2 with hEqBm; subst hEqBm
                have hPosCount : 1 ≤ countPostRefs db' r.key := by
                  apply countPostRefs_pos_of_mem (id := pid) (p := p0)
                  · rw [hDbPosts]; simp [Std.ExtTreeMap.getElem?_insert, hNe, hp0]
                  · exact hr0
                have hRefEq := hRefExact' r.key bm' hbm'
                exact ⟨bm', hbm', hm1.trans hMime, hm2.trans hSz, by omega⟩

theorem commitDelete_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    {id : PostId} {rel : Option ImageRef}
    (hInv : Invariant s) (hOk : s.commitDelete id = .ok (rel, s')) :
    Invariant s' := by
  unfold commitDelete at hOk
  cases hTx : s.activeTx with
  | none => rw [hTx] at hOk; simp at hOk
  | some pending =>
    rw [hTx] at hOk; dsimp only at hOk
    cases hDb : s.db.deletePost id with
    | error e => rw [hDb] at hOk; simp at hOk
    | ok res =>
      rw [hDb] at hOk; dsimp only at hOk
      rcases res with ⟨rel?, db'⟩
      have hOldPost : ∃ oldPost, s.db.posts[id]? = some oldPost ∧ oldPost.image = rel? ∧
          db'.posts = s.db.posts.erase id := by
        unfold DbState.deletePost at hDb
        cases hGet : s.db.posts[id]? with
        | none => rw [hGet] at hDb; simp at hDb
        | some oldPost =>
          rw [hGet] at hDb
          simp only [Except.ok.injEq, Prod.mk.injEq] at hDb
          rcases hDb with ⟨rfl, rfl⟩
          exact ⟨oldPost, rfl, rfl, rfl⟩
      rcases hOldPost with ⟨oldPost, hGetOld, rfl, hDbPosts⟩
      have hDbInv' := DbState.deletePost_preserves_invariant hInv.db_inv hDb
      have hSeqSame : db'.lastSeq = s.db.lastSeq := by
        unfold DbState.deletePost at hDb
        rw [hGetOld] at hDb
        simp only [Except.ok.injEq, Prod.mk.injEq] at hDb
        rcases hDb with ⟨_, rfl⟩; rfl
      have hOldPos : ∀ r, oldPost.image = some r →
          ∃ bm, s.bucket.objects[r.key]? = some bm ∧ 1 ≤ bm.refCount := by
        intro r hr
        rcases hInv.ref_integrity id oldPost r hGetOld hr with ⟨bm, hbm, _, _, hPos⟩
        exact ⟨bm, hbm, hPos⟩
      have hDelta : applyImageRefDelta s.bucket oldPost.image none =
          (match oldPost.image with
          | none => Except.ok s.bucket
          | some ref => s.bucket.decRef ref.key) := by
        cases oldPost.image <;> rfl
      cases hBRes : (match oldPost.image with | none => Except.ok s.bucket | some ref => s.bucket.decRef ref.key) with
      | error e => rw [hBRes] at hOk; simp at hOk
      | ok bucket' =>
        rw [hBRes] at hOk
        simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
        rcases hOk with ⟨rfl, rfl⟩
        rw [← hDelta] at hBRes
        have ⟨hBInv', hDeltaObj, hDeltaKeep, _⟩ := applyImageRefDelta_spec hInv.bucket_inv hOldPos hBRes
        have hCountEq : ∀ k, countPostRefs s.db k = countPostRefs db' k + refKeyDelta oldPost.image k := by
          intro k
          have hEr := countPostRefs_erase_some hGetOld k
          have hSameC : countPostRefs db' k =
              countPostRefs { s.db with posts := s.db.posts.erase id } k := by
            simp only [countPostRefs, hDbPosts]
          rw [hSameC]
          simpa only [postRefDelta_eq_refKeyDelta] using hEr
        have hRefExact' : ∀ (k : ObjectKey) (bm' : BucketEntryMeta policy.segmentSize),
            bucket'.objects[k]? = some bm' → bm'.refCount = countPostRefs db' k := by
          intro k bm' hbm'
          rcases hDeltaObj k bm' hbm' with ⟨bm, hbm, _, _, hRefEq⟩
          have hOldExact := hInv.refcount_exact k bm hbm
          have hC := hCountEq k
          have hZero : refKeyDelta none k = 0 := rfl
          rw [hZero] at hRefEq
          omega
        refine ⟨hDbInv', hBInv', hInv.nextTxId_pos, ?_, ?_, hRefExact'⟩
        · dsimp only; rw [hSeqSame]; exact hInv.nextSeq_gt
        · intro pid p0 r hp0 hr0
          rw [hDbPosts] at hp0
          simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq] at hp0
          split at hp0
          · simp at hp0
          · next hNe =>
            rcases hInv.ref_integrity pid p0 r hp0 hr0 with ⟨bmOld, hbmOld, hMime, hSz, _⟩
            rcases hDeltaKeep r.key bmOld hbmOld with ⟨bm', hbm'⟩
            rcases hDeltaObj r.key bm' hbm' with ⟨bmOld2, hbmOld2, hm1, hm2, _⟩
            rw [hbmOld] at hbmOld2; injection hbmOld2 with hEqBm; subst hEqBm
            have hPosCount : 1 ≤ countPostRefs db' r.key := by
              apply countPostRefs_pos_of_mem (id := pid) (p := p0)
              · rw [hDbPosts]; simp [Std.ExtTreeMap.getElem?_erase, hNe, hp0]
              · exact hr0
            have hRefEq := hRefExact' r.key bm' hbm'
            exact ⟨bm', hbm', hm1.trans hMime, hm2.trans hSz, by omega⟩

theorem abortTx_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    (hInv : Invariant s) (hOk : s.abortTx = .ok s') :
    Invariant s' := by
  unfold abortTx at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq] at hOk; subst hOk
    exact ⟨hInv.db_inv, hInv.bucket_inv, hInv.nextTxId_pos, hInv.nextSeq_gt,
      hInv.ref_integrity, hInv.refcount_exact⟩

/-- Atomicity: `abortTx` leaves committed DB and bucket state completely unchanged. -/
theorem abortTx_preserves_committed {policy : StoragePolicy} {s s' : StoreState policy}
    (hOk : s.abortTx = .ok s') :
    s'.db = s.db ∧ s'.bucket = s.bucket ∧ s'.activeTx = none := by
  unfold abortTx at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq] at hOk; subst hOk; exact ⟨rfl, rfl, rfl⟩

theorem runGC_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    (hInv : Invariant s) (hOk : s.runGC = .ok s') :
    Invariant s' := by
  unfold runGC at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq] at hOk; subst hOk
    have hBInv' := BucketState.gcStep_preserves_invariant hInv.bucket_inv
    refine ⟨hInv.db_inv, hBInv', hInv.nextTxId_pos, hInv.nextSeq_gt, ?_, ?_⟩
    · intro id p ref hp hr
      rcases hInv.ref_integrity id p ref hp hr with ⟨bm, hbm, hMime, hSz, hPos⟩
      have hLive := (BucketState.gcStep_preserves_live s.bucket hbm hPos).1
      exact ⟨bm, hLive, hMime, hSz, hPos⟩
    · intro k bm hbm
      dsimp only [BucketState.gcStep] at hbm
      rw [Std.ExtTreeMap.getElem?_filter'] at hbm
      cases hk : s.bucket.objects[k]? with
      | none => rw [hk] at hbm; simp at hbm
      | some bm0 =>
        rw [hk] at hbm
        by_cases hPos : bm0.refCount > 0
        · simp only [hPos, decide_true, Option.filter_some, ↓reduceIte, Option.some.injEq] at hbm
          subst hbm
          exact hInv.refcount_exact k bm0 hk
        · simp only [hPos, decide_false, Option.filter_some, Bool.false_eq_true, ↓reduceIte] at hbm
          cases hbm

theorem runCompact_preserves_invariant {policy : StoragePolicy} {s s' : StoreState policy}
    (hInv : Invariant s) (hOk : s.runCompact = .ok s') :
    Invariant s' := by
  unfold runCompact at hOk
  split at hOk
  · simp at hOk
  · cases hComp : s.bucket.compactBucket with
    | error e => rw [hComp] at hOk; simp at hOk
    | ok bucket' =>
      rw [hComp] at hOk
      simp only [Except.ok.injEq] at hOk; subst hOk
      have hDbInv' := DbState.compactDb_preserves_invariant hInv.db_inv
      have hBInv' := BucketState.compactBucket_preserves_invariant hInv.bucket_inv hComp
      have ⟨_, _, hObjEquiv⟩ := BucketState.compactBucket_equiv hInv.bucket_inv hComp
      have hCountSame : ∀ k, countPostRefs s.db.compactDb k = countPostRefs s.db k := fun _ => rfl
      refine ⟨hDbInv', hBInv', hInv.nextTxId_pos, hInv.nextSeq_gt, ?_, ?_⟩
      · intro id p ref hp hr
        rcases hInv.ref_integrity id p ref hp hr with ⟨bm, hbm, hMime, hSz, hPos⟩
        rcases hObjEquiv ref.key bm hbm with ⟨bm', hbm', _, hMime', _, hSz', hRef'⟩
        exact ⟨bm', hbm', hMime'.trans hMime, hSz'.trans hSz, hRef'.symm ▸ hPos⟩
      · intro k bm' hbm'
        -- Find original entry via `hBInv'` / `hComp`? Even simpler: `compactBucket` preserves `objects` keys!
        -- Wait: `hObjEquiv` gives forward direction, let's check backward or `hComp`!
        have hMem : k ∈ bucket'.objects := by
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hbm']; rfl
        have hMemBlob : k ∈ bucket'.blobs := (hBInv'.blobs_wf k).mpr hMem
        have hBlobsEq : bucket'.blobs = s.bucket.blobs :=
          (BucketState.compactBucket_equiv hInv.bucket_inv hComp).1
        rw [hBlobsEq, hInv.bucket_inv.blobs_wf, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hMemBlob
        cases hOrig : s.bucket.objects[k]? with
        | none => rw [hOrig] at hMemBlob; simp at hMemBlob
        | some bm0 =>
          rcases hObjEquiv k bm0 hOrig with ⟨bm'', hbm'', _, _, _, _, hRef''⟩
          rw [hbm'] at hbm''; injection hbm'' with hEq; subst hEq
          rw [hCountSame, hRef'', hInv.refcount_exact k bm0 hOrig]

end StoreState

end Leaf.Core