import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.ExtTreeSet
import Std.Data.ExtTreeSet.Lemmas
import Leaf.Core.Schema

namespace Leaf.Core

/-- Constructs the descending feed index key for a post. -/
def FeedKey.ofPost (p : Post) : FeedKey :=
  ⟨p.createdAt, p.id⟩

/-- In-memory verified database model mirroring persistent checkpoint + WAL state. -/
structure DbState where
  posts      : Std.ExtTreeMap PostId Post
  feedIndex  : Std.ExtTreeMap FeedKey PostId FeedKey.cmpDesc
  tombstones : Std.ExtTreeSet PostId
  nextPostId : PostId
  lastSeq    : SeqNo

namespace DbState

/-- Initial empty database starting IDs at `1` and sequences at `0`. -/
def empty : DbState where
  posts      := ∅
  feedIndex  := ∅
  tombstones := ∅
  nextPostId := ⟨1⟩
  lastSeq    := ⟨0⟩

instance : Inhabited DbState := ⟨empty⟩

/-- Well-formedness and index consistency invariant on `DbState`. -/
structure Invariant (db : DbState) : Prop where
  nextPostId_pos     : 1 ≤ db.nextPostId.val.toNat
  posts_wf           : ∀ (k : PostId) (p : Post), db.posts[k]? = some p →
    p.id = k ∧ 1 ≤ k.val.toNat ∧ k.val.toNat < db.nextPostId.val.toNat ∧ p.version.val.toNat ≤ db.lastSeq.val.toNat
  feed_bijection     : ∀ (fk : FeedKey) (id : PostId), db.feedIndex[fk]? = some id ↔
    ∃ p, db.posts[id]? = some p ∧ fk = FeedKey.ofPost p
  tombstone_disjoint : ∀ (id : PostId), id ∈ db.posts → id ∉ db.tombstones
  tombstones_wf      : ∀ (id : PostId), id ∈ db.tombstones → 1 ≤ id.val.toNat ∧ id.val.toNat < db.nextPostId.val.toNat

/-- Primary key lookup returning the live post if present. -/
def getPost (db : DbState) (id : PostId) : Option Post :=
  db.posts[id]?

/-- Inserts a newly created post and updates primary and feed indexes. -/
def createPost (db : DbState) (now : Int64) (draft : ValidPostDraft)
    (imageRef : Option ImageRef) : Except CoreError (Post × DbState) :=
  if db.nextPostId.val.toNat + 1 ≥ 2 ^ 64 || db.lastSeq.val.toNat + 1 ≥ 2 ^ 64 then
    .error (.invariantViolated "PostId or SeqNo counter overflow")
  else
    let id : PostId := db.nextPostId
    let seq : SeqNo := ⟨db.lastSeq.val + 1⟩
    let post : Post :=
      { id        := id
        author    := draft.author
        title     := draft.title
        caption   := draft.caption
        tags      := draft.tags
        createdAt := now
        updatedAt := none
        version   := seq
        image     := imageRef }
    let nextState : DbState :=
      { posts      := db.posts.insert id post
        feedIndex  := db.feedIndex.insert (FeedKey.ofPost post) id
        tombstones := db.tombstones
        nextPostId := ⟨db.nextPostId.val + 1⟩
        lastSeq    := seq }
    .ok (post, nextState)

/-- Resolves the post's next `ImageRef` under an update patch. -/
def resolveUpdatedImage (existing : Option ImageRef) (patch : ValidImagePatch)
    (newImg : Option ImageRef) : Except CoreError (Option ImageRef) :=
  match patch with
  | .keep => .ok existing
  | .remove => .ok none
  | .replace _ _ =>
    match newImg with
    | some ref => .ok (some ref)
    | none => .error (.invariantViolated "missing replacement ImageRef")

/-- Updates an existing live post while preserving `id` and `createdAt`. -/
def updatePost (db : DbState) (id : PostId) (now : Int64) (patch : ValidPostPatch)
    (newImg : Option ImageRef) : Except CoreError (Post × DbState) :=
  match db.posts[id]? with
  | none => .error (.postNotFound id)
  | some existing =>
    if db.lastSeq.val.toNat + 1 ≥ 2 ^ 64 then
      .error (.invariantViolated "SeqNo counter overflow")
    else
      match resolveUpdatedImage existing.image patch.imagePatch newImg with
      | .error e => .error e
      | .ok img? =>
        let seq : SeqNo := ⟨db.lastSeq.val + 1⟩
        let updated : Post :=
          { existing with
            author    := patch.author
            title     := patch.title
            caption   := patch.caption
            tags      := patch.tags
            updatedAt := some now
            version   := seq
            image     := img? }
        let oldKey := FeedKey.ofPost existing
        let newKey := FeedKey.ofPost updated
        let feedIndex' :=
          if oldKey = newKey then db.feedIndex
          else (db.feedIndex.erase oldKey).insert newKey id
        let nextState : DbState :=
          { db with
            posts     := db.posts.insert id updated
            feedIndex := feedIndex'
            lastSeq   := seq }
        .ok (updated, nextState)

/-- Deletes a live post, removes it from indexes, and records a tombstone. -/
def deletePost (db : DbState) (id : PostId) : Except CoreError (Option ImageRef × DbState) :=
  match db.posts[id]? with
  | none => .error (.postNotFound id)
  | some existing =>
    let nextState : DbState :=
      { db with
        posts      := db.posts.erase id
        feedIndex  := db.feedIndex.erase (FeedKey.ofPost existing)
        tombstones := db.tombstones.insert id }
    .ok (existing.image, nextState)

/-- Cursor predicate accepting feed keys strictly after `cursor?` in descending feed order. -/
def feedAfter (cursor? : Option FeedKey) (k : FeedKey) : Bool :=
  match cursor? with
  | none => true
  | some cur => FeedKey.cmpDesc cur k == .lt

/-- Scans descending feed posts strictly after `cursor?` up to `limit` items. -/
def queryFeed (db : DbState) (cursor? : Option FeedKey) (limit : Nat) : Array Post :=
  db.feedIndex.foldl
    (fun acc k id =>
      if acc.size < limit && feedAfter cursor? k then
        match db.posts[id]? with
        | some p => acc.push p
        | none => acc
      else
        acc)
    #[]

/-- Clears tombstones without altering live posts, feed ordering, or counters. -/
def compactDb (db : DbState) : DbState :=
  { db with tombstones := ∅ }

end DbState

abbrev DbInvariant := DbState.Invariant

namespace DbState

private theorem uint64_succ_toNat {x : UInt64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  exact Nat.mod_eq_of_lt h

private theorem compare_eq_iff_eq {α : Type} [Ord α] [Std.LawfulEqOrd α] {a b : α} :
    compare a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqOrd.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self (cmp := compare)⟩

private theorem cmpDesc_eq_iff_eq {a b : FeedKey} :
    FeedKey.cmpDesc a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqCmp.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self (cmp := FeedKey.cmpDesc)⟩

theorem empty_invariant : Invariant empty where
  nextPostId_pos := by decide
  posts_wf := by
    intro k p hp
    simp [empty] at hp
  feed_bijection := by
    intro fk id
    simp [empty]
  tombstone_disjoint := by
    intro id hid hmem
    simp [empty] at hmem
  tombstones_wf := by
    intro id hmem
    simp [empty] at hmem

theorem getPost_eq_none_of_ge_next {db : DbState} (hInv : Invariant db) {k : PostId}
    (hk : db.nextPostId.val.toNat ≤ k.val.toNat) : db.posts[k]? = none := by
  by_cases hnone : db.posts[k]? = none
  · exact hnone
  · cases hget : db.posts[k]? with
    | none => rfl
    | some p =>
      have ⟨_, _, hlt, _⟩ := hInv.posts_wf k p hget
      omega

theorem not_mem_tombstones_of_ge_next {db : DbState} (hInv : Invariant db) {k : PostId}
    (hk : db.nextPostId.val.toNat ≤ k.val.toNat) : k ∉ db.tombstones := by
  intro hmem
  have ⟨_, hlt⟩ := hInv.tombstones_wf k hmem
  omega

theorem createPost_preserves_invariant {db db' : DbState} {now : Int64}
    {draft : ValidPostDraft} {imageRef : Option ImageRef} {p : Post}
    (hInv : Invariant db)
    (hOk : db.createPost now draft imageRef = .ok (p, db')) :
    Invariant db' := by
  unfold createPost at hOk
  split at hOk
  · simp at hOk
  · next hNoOv =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hNoOv
    rcases hNoOv with ⟨hIdOv, hSeqOv⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    have hNextIdToNat : (db.nextPostId.val + 1).toNat = db.nextPostId.val.toNat + 1 :=
      uint64_succ_toNat hIdOv
    have hNextSeqToNat : (db.lastSeq.val + 1).toNat = db.lastSeq.val.toNat + 1 :=
      uint64_succ_toNat hSeqOv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [hNextIdToNat]
      omega
    · intro k q hq
      dsimp only at hq ⊢
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hq
      split at hq
      · next hEq =>
        injection hq with hPostEq
        subst hPostEq
        subst hEq
        refine ⟨rfl, hInv.nextPostId_pos, ?_, ?_⟩
        · rw [hNextIdToNat]
          omega
        · exact Nat.le_refl _
      · have ⟨hid, hge, hlt, hseq⟩ := hInv.posts_wf k q hq
        refine ⟨hid, hge, ?_, ?_⟩
        · rw [hNextIdToNat]
          omega
        · rw [hNextSeqToNat]
          omega
    · intro fk pid
      dsimp only
      simp only [Std.ExtTreeMap.getElem?_insert, cmpDesc_eq_iff_eq]
      split
      · next hfk =>
        constructor
        · intro hid
          injection hid with hidEq
          subst hidEq
          refine ⟨_, ?_, hfk.symm⟩
          simp
        · rintro ⟨q, hq, hqk⟩
          simp only [compare_eq_iff_eq] at hq
          split at hq
          · next hpid => rw [hpid]
          · exfalso
            have ⟨hqid, _, hlt, _⟩ := hInv.posts_wf pid q hq
            have hIdEq : q.id = db.nextPostId := (congrArg FeedKey.id (hfk.trans hqk)).symm
            rw [hqid] at hIdEq
            rw [hIdEq] at hlt
            exact Nat.lt_irrefl _ hlt
      · next hfk =>
        rw [hInv.feed_bijection fk pid]
        constructor
        · rintro ⟨q, hq, hqk⟩
          refine ⟨q, ?_, hqk⟩
          simp only [compare_eq_iff_eq]
          split
          · next hpid =>
            exfalso
            have ⟨hqid, _, hlt, _⟩ := hInv.posts_wf pid q hq
            rw [hpid] at hlt
            exact Nat.lt_irrefl _ hlt
          · exact hq
        · rintro ⟨q, hq, hqk⟩
          simp only [compare_eq_iff_eq] at hq
          split at hq
          · next hpid =>
            injection hq with hqEq
            subst hqEq
            subst hpid
            exfalso
            exact hfk hqk.symm
          · exact ⟨q, hq, hqk⟩
    · intro pid hmem htom
      dsimp only at hmem htom
      simp only [Std.ExtTreeMap.mem_iff_isSome_getElem?, Std.ExtTreeMap.getElem?_insert,
        compare_eq_iff_eq] at hmem
      split at hmem
      · next heq =>
        subst heq
        exact (not_mem_tombstones_of_ge_next hInv (Nat.le_refl _)) htom
      · rw [← Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
        exact hInv.tombstone_disjoint pid hmem htom
    · intro pid htom
      dsimp only at htom ⊢
      have ⟨hge, hlt⟩ := hInv.tombstones_wf pid htom
      rw [hNextIdToNat]
      exact ⟨hge, Nat.lt_succ_of_lt hlt⟩

theorem updatePost_preserves_invariant {db db' : DbState} {id : PostId} {now : Int64}
    {patch : ValidPostPatch} {newImg : Option ImageRef} {p : Post}
    (hInv : Invariant db)
    (hOk : db.updatePost id now patch newImg = .ok (p, db')) :
    Invariant db' := by
  unfold updatePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk
    dsimp only at hOk
    split at hOk
    · simp at hOk
    · next hSeqOv =>
      simp only [Nat.not_le] at hSeqOv
      cases hImg : resolveUpdatedImage existing.image patch.imagePatch newImg with
      | error e => rw [hImg] at hOk; simp at hOk
      | ok img? =>
        rw [hImg] at hOk
        dsimp only at hOk
        simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
        rcases hOk with ⟨rfl, rfl⟩
        have hOldWf := hInv.posts_wf id existing hOld
        have hSeqToNat : (db.lastSeq.val + 1).toNat = db.lastSeq.val.toNat + 1 :=
          uint64_succ_toNat hSeqOv
        have hSameKey : FeedKey.ofPost existing = FeedKey.ofPost
            { existing with
              author := patch.author, title := patch.title, caption := patch.caption,
              tags := patch.tags, updatedAt := some now,
              version := { val := db.lastSeq.val + 1 }, image := img? } := rfl
        simp only [← hSameKey, ↓reduceIte]
        refine ⟨hInv.nextPostId_pos, ?_, ?_, ?_, hInv.tombstones_wf⟩
        · intro k q hq
          dsimp only at hq
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hq
          split at hq
          · next hEq =>
            injection hq with hqEq
            subst hqEq
            subst hEq
            refine ⟨hOldWf.1, hOldWf.2.1, hOldWf.2.2.1, ?_⟩
            rw [hSeqToNat]
            exact Nat.le_refl _
          · have hqWf := hInv.posts_wf k q hq
            refine ⟨hqWf.1, hqWf.2.1, hqWf.2.2.1, ?_⟩
            rw [hSeqToNat]
            omega
        · intro fk pid
          dsimp only
          rw [hInv.feed_bijection fk pid]
          constructor
          · rintro ⟨q, hq, hfk⟩
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
            split
            · next hEq =>
              subst hEq
              rw [hOld] at hq
              injection hq with hqEq
              subst hqEq
              exact ⟨_, rfl, hfk⟩
            · exact ⟨q, hq, hfk⟩
          · rintro ⟨q, hq, hfk⟩
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hq
            split at hq
            · next hEq =>
              subst hEq
              injection hq with hqEq
              subst hqEq
              exact ⟨existing, hOld, hfk⟩
            · exact ⟨q, hq, hfk⟩
        · intro pid hmem htom
          dsimp only at hmem htom
          simp only [Std.ExtTreeMap.mem_iff_isSome_getElem?, Std.ExtTreeMap.getElem?_insert,
            compare_eq_iff_eq] at hmem
          split at hmem
          · next hEq =>
            subst hEq
            have hExMem : id ∈ db.posts := by
              rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hOld]; rfl
            exact hInv.tombstone_disjoint id hExMem htom
          · rw [← Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
            exact hInv.tombstone_disjoint pid hmem htom

theorem deletePost_preserves_invariant {db db' : DbState} {id : PostId} {rel : Option ImageRef}
    (hInv : Invariant db)
    (hOk : db.deletePost id = .ok (rel, db')) :
    Invariant db' := by
  unfold deletePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    have hOldWf := hInv.posts_wf id existing hOld
    refine ⟨hInv.nextPostId_pos, ?_, ?_, ?_, ?_⟩
    · intro k q hq
      dsimp only at hq
      simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq] at hq
      split at hq
      · simp at hq
      · exact hInv.posts_wf k q hq
    · intro fk pid
      dsimp only
      simp only [Std.ExtTreeMap.getElem?_erase, cmpDesc_eq_iff_eq]
      split
      · next hfk =>
        subst hfk
        constructor
        · intro hNone; simp at hNone
        · rintro ⟨q, hq, hqk⟩
          simp only [compare_eq_iff_eq] at hq
          split at hq
          · simp at hq
          · next hNe =>
            exfalso
            have hqWf := hInv.posts_wf pid q hq
            have hIdEq : q.id = existing.id := congrArg FeedKey.id hqk.symm
            rw [hqWf.1, hOldWf.1] at hIdEq
            exact hNe hIdEq.symm
      · next hfk =>
        rw [hInv.feed_bijection fk pid]
        constructor
        · rintro ⟨q, hq, hqk⟩
          simp only [compare_eq_iff_eq]
          split
          · next hEq =>
            subst hEq
            rw [hOld] at hq
            injection hq with hqEq
            subst hqEq
            exfalso
            exact hfk hqk.symm
          · exact ⟨q, hq, hqk⟩
        · rintro ⟨q, hq, hqk⟩
          simp only [compare_eq_iff_eq] at hq
          split at hq
          · simp at hq
          · exact ⟨q, hq, hqk⟩
    · intro pid hmem htom
      dsimp only at hmem htom
      simp only [Std.ExtTreeMap.mem_iff_isSome_getElem?, Std.ExtTreeMap.getElem?_erase,
        compare_eq_iff_eq] at hmem
      split at hmem
      · simp at hmem
      · next hNe =>
        simp only [Std.ExtTreeSet.mem_insert, compare_eq_iff_eq] at htom
        rcases htom with hEq | hOldTom
        · exact hNe hEq
        · rw [← Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
          exact hInv.tombstone_disjoint pid hmem hOldTom
    · intro pid htom
      dsimp only at htom
      simp only [Std.ExtTreeSet.mem_insert, compare_eq_iff_eq] at htom
      rcases htom with hEq | hOldTom
      · subst hEq
        exact ⟨hOldWf.2.1, hOldWf.2.2.1⟩
      · exact hInv.tombstones_wf pid hOldTom

theorem compactDb_preserves_invariant {db : DbState} (hInv : Invariant db) :
    Invariant db.compactDb where
  nextPostId_pos     := hInv.nextPostId_pos
  posts_wf           := hInv.posts_wf
  feed_bijection     := hInv.feed_bijection
  tombstone_disjoint := by intro id _ hmem; simp [compactDb] at hmem
  tombstones_wf      := by intro id hmem; simp [compactDb] at hmem

/-- Read-after-write after `createPost`. -/
theorem createPost_getPost_self {db db' : DbState} {now : Int64}
    {draft : ValidPostDraft} {img : Option ImageRef} {p : Post}
    (hOk : db.createPost now draft img = .ok (p, db')) :
    db'.getPost p.id = some p := by
  unfold createPost at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    unfold getPost
    exact Std.ExtTreeMap.getElem?_insert_self

/-- Non-interference of `createPost` on other primary keys. -/
theorem createPost_getPost_other {db db' : DbState} {now : Int64}
    {draft : ValidPostDraft} {img : Option ImageRef} {p : Post} {other : PostId}
    (hOk : db.createPost now draft img = .ok (p, db'))
    (hNe : other ≠ p.id) :
    db'.getPost other = db.getPost other := by
  unfold createPost at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    unfold getPost
    dsimp only
    have hNe' : ¬ (db.nextPostId = other) := fun h => hNe h.symm
    simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe', ↓reduceIte]

/-- Read-after-write after `updatePost` (including metadata preservation). -/
theorem updatePost_getPost_self {db db' : DbState} {id : PostId} {now : Int64}
    {patch : ValidPostPatch} {newImg : Option ImageRef} {p : Post}
    (hInv : Invariant db)
    (hOk : db.updatePost id now patch newImg = .ok (p, db')) :
    db'.getPost id = some p ∧ p.id = id ∧ p.updatedAt = some now := by
  unfold updatePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk; dsimp only at hOk
    split at hOk
    · simp at hOk
    · cases hImg : resolveUpdatedImage existing.image patch.imagePatch newImg with
      | error e => rw [hImg] at hOk; simp at hOk
      | ok img? =>
        rw [hImg] at hOk; dsimp only at hOk
        simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
        rcases hOk with ⟨rfl, rfl⟩
        have hOldWf := hInv.posts_wf id existing hOld
        refine ⟨?_, hOldWf.1, rfl⟩
        unfold getPost
        exact Std.ExtTreeMap.getElem?_insert_self

/-- Non-interference of `updatePost` on other primary keys. -/
theorem updatePost_getPost_other {db db' : DbState} {id other : PostId} {now : Int64}
    {patch : ValidPostPatch} {newImg : Option ImageRef} {p : Post}
    (hOk : db.updatePost id now patch newImg = .ok (p, db'))
    (hNe : other ≠ id) :
    db'.getPost other = db.getPost other := by
  unfold updatePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk; dsimp only at hOk
    split at hOk
    · simp at hOk
    · cases hImg : resolveUpdatedImage existing.image patch.imagePatch newImg with
      | error e => rw [hImg] at hOk; simp at hOk
      | ok img? =>
        rw [hImg] at hOk; dsimp only at hOk
        simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
        rcases hOk with ⟨rfl, rfl⟩
        unfold getPost
        dsimp only
        have hNe' : ¬ (id = other) := fun h => hNe h.symm
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe', ↓reduceIte]

/-- Deleted primary keys return `none` on `getPost`. -/
theorem deletePost_getPost_self {db db' : DbState} {id : PostId} {rel : Option ImageRef}
    (hOk : db.deletePost id = .ok (rel, db')) :
    db'.getPost id = none := by
  unfold deletePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    unfold getPost
    exact Std.ExtTreeMap.getElem?_erase_self

/-- Non-interference of `deletePost` on other primary keys. -/
theorem deletePost_getPost_other {db db' : DbState} {id other : PostId} {rel : Option ImageRef}
    (hOk : db.deletePost id = .ok (rel, db'))
    (hNe : other ≠ id) :
    db'.getPost other = db.getPost other := by
  unfold deletePost at hOk
  cases hOld : db.posts[id]? with
  | none => rw [hOld] at hOk; simp at hOk
  | some existing =>
    rw [hOld] at hOk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
    rcases hOk with ⟨rfl, rfl⟩
    unfold getPost
    dsimp only
    have hNe' : ¬ (id = other) := fun h => hNe h.symm
    simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq, hNe', ↓reduceIte]

/-- Primary key uniqueness: two live entries sharing `Post.id` are the identical slot and record. -/
theorem pk_uniqueness {db : DbState} (hInv : Invariant db) {k₁ k₂ : PostId} {p₁ p₂ : Post}
    (h₁ : db.posts[k₁]? = some p₁) (h₂ : db.posts[k₂]? = some p₂)
    (hId : p₁.id = p₂.id) :
    k₁ = k₂ ∧ p₁ = p₂ := by
  have hk₁ := (hInv.posts_wf k₁ p₁ h₁).1
  have hk₂ := (hInv.posts_wf k₂ p₂ h₂).1
  have hkEq : k₁ = k₂ := hk₁.symm.trans (hId.trans hk₂)
  subst hkEq
  rw [h₁] at h₂
  injection h₂ with hpEq
  exact ⟨rfl, hpEq⟩

/-! ### Feed Query & Pagination Proofs -/

private def feedStep (db : DbState) (cursor? : Option FeedKey) (limit : Nat)
    (acc : Array Post) (k : FeedKey) (id : PostId) : Array Post :=
  if acc.size < limit && feedAfter cursor? k then
    match db.posts[id]? with
    | some p => acc.push p
    | none => acc
  else
    acc

private def takeStep {α β : Type} (f : α → Option β) (limit : Nat) (a : Array β) (x : α) : Array β :=
  if a.size < limit then
    match f x with
    | some b => a.push b
    | none => a
  else a

private theorem foldl_take_filterMap_aux {α β : Type} (f : α → Option β) (limit : Nat) :
    ∀ (xs : List α) (acc : Array β),
      (xs.foldl (takeStep f limit) acc).toList =
      acc.toList ++ (xs.filterMap f).take (limit - acc.size) := by
  intro xs
  induction xs with
  | nil =>
    intro acc
    simp [List.filterMap]
  | cons x xs ih =>
    intro acc
    dsimp only [List.foldl]
    by_cases hlt : acc.size < limit
    · cases hfx : f x with
      | none =>
        have hstep : takeStep f limit acc x = acc := by simp [takeStep, hlt, hfx]
        rw [hstep]
        simp only [List.filterMap_cons, hfx]
        exact ih acc
      | some b =>
        have hstep : takeStep f limit acc x = acc.push b := by simp [takeStep, hlt, hfx]
        have hrem : limit - acc.size = (limit - (acc.size + 1)) + 1 := by omega
        rw [hstep]
        simp only [List.filterMap_cons, hfx]
        rw [ih (acc.push b)]
        have hsz : (acc.push b).size = acc.size + 1 := by simp
        rw [hsz, hrem, List.take_succ_cons]
        simp [Array.toList_push, List.append_assoc]
    · have hzero : limit - acc.size = 0 := by omega
      have hstep : takeStep f limit acc x = acc := by simp [takeStep, hlt]
      rw [hstep]
      simp only [hzero, List.take_zero, List.append_nil]
      clear hzero hstep
      have hconst : ∀ (ys : List α) (a : Array β), ¬ a.size < limit →
          ys.foldl (takeStep f limit) a = a := by
        intro ys
        induction ys with
        | nil => intro a _; rfl
        | cons y ys' ihy =>
          intro a ha
          dsimp only [List.foldl]
          have hs : takeStep f limit a y = a := by simp [takeStep, ha]
          rw [hs]
          exact ihy a ha
      rw [hconst xs acc hlt]

private def feedEntryPost (db : DbState) (cursor? : Option FeedKey) (kv : FeedKey × PostId) : Option Post :=
  if feedAfter cursor? kv.1 then db.posts[kv.2]? else none

private theorem feedStep_eq_filterStep (db : DbState) (cursor? : Option FeedKey) (limit : Nat)
    (acc : Array Post) (kv : FeedKey × PostId) :
    feedStep db cursor? limit acc kv.1 kv.2 =
      takeStep (feedEntryPost db cursor?) limit acc kv := by
  unfold feedStep takeStep feedEntryPost
  by_cases hlt : acc.size < limit <;> by_cases ha : feedAfter cursor? kv.1
  · simp only [hlt, ha, ↓reduceIte]; cases db.posts[kv.2]? <;> rfl
  · simp [hlt, ha]
  · simp [hlt, ha]
  · simp [hlt, ha]

/-- All feed posts strictly after `cursor?` in index order. -/
def allFeedAfter (db : DbState) (cursor? : Option FeedKey) : List Post :=
  db.feedIndex.toList.filterMap (feedEntryPost db cursor?)

/-- Exact equivalence between `queryFeed` and taking `limit` items from `allFeedAfter`. -/
theorem queryFeed_toList_eq (db : DbState) (cursor? : Option FeedKey) (limit : Nat) :
    (db.queryFeed cursor? limit).toList = (allFeedAfter db cursor?).take limit := by
  unfold queryFeed allFeedAfter
  change (db.feedIndex.foldl (feedStep db cursor? limit) #[]).toList = _
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hfun : (fun a (b : FeedKey × PostId) => feedStep db cursor? limit a b.fst b.snd) =
      takeStep (feedEntryPost db cursor?) limit := by
    funext a b
    exact feedStep_eq_filterStep db cursor? limit a b
  rw [hfun]
  have hfold := foldl_take_filterMap_aux (feedEntryPost db cursor?) limit db.feedIndex.toList #[]
  simp only [List.nil_append, Array.size_empty, Nat.sub_zero] at hfold
  simpa using hfold

private theorem pairwise_filterMap_feed {db : DbState} (hInv : Invariant db) (cursor? : Option FeedKey) :
    (allFeedAfter db cursor?).Pairwise (fun p₁ p₂ => FeedKey.cmpDesc (FeedKey.ofPost p₁) (FeedKey.ofPost p₂) = .lt) := by
  unfold allFeedAfter
  have hOrd : db.feedIndex.toList.Pairwise (fun a b => FeedKey.cmpDesc a.1 b.1 = .lt) :=
    Std.ExtTreeMap.ordered_keys_toList
  have hPair : (db.feedIndex.toList.filterMap fun kv =>
      match kv with
      | (fk, id) =>
        if feedAfter cursor? fk then
          match db.posts[id]? with
          | some p => some (fk, p)
          | none => none
        else none).Pairwise (fun x y => FeedKey.cmpDesc x.1 y.1 = .lt) := by
    apply List.Pairwise.filterMap (R := fun a b => FeedKey.cmpDesc a.1 b.1 = .lt)
    · intro a b hab x hx y hy
      cases hfa : feedAfter cursor? a.1 <;> cases hfb : feedAfter cursor? b.1
      · simp [hfa] at hx
      · simp [hfa] at hx
      · simp [hfb] at hy
      · simp only [hfa, hfb, ↓reduceIte] at hx hy
        cases hpa : db.posts[a.2]? <;> cases hpb : db.posts[b.2]?
        · simp [hpa] at hx
        · simp [hpa] at hx
        · simp [hpb] at hy
        · simp only [hpa, hpb, Option.some.injEq] at hx hy
          subst hx; subst hy
          exact hab
    · exact hOrd
  have hMapEq : db.feedIndex.toList.filterMap (feedEntryPost db cursor?) =
      (db.feedIndex.toList.filterMap fun kv =>
        match kv with
        | (fk, id) =>
          if feedAfter cursor? fk then
            match db.posts[id]? with
            | some p => some (fk, p)
            | none => none
          else none).map Prod.snd := by
    induction db.feedIndex.toList with
    | nil => rfl
    | cons kv rest ih =>
      simp only [List.filterMap_cons]
      unfold feedEntryPost
      cases hfa : feedAfter cursor? kv.1
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih
      · simp only [↓reduceIte]
        cases hpk : db.posts[kv.2]?
        · simp only; exact ih
        · rename_i p
          simp only [List.map_cons]; exact congrArg (p :: ·) ih
  have hKeyMatch : ∀ x, x ∈ (db.feedIndex.toList.filterMap fun kv =>
        match kv with
        | (fk, id) =>
          if feedAfter cursor? fk then
            match db.posts[id]? with
            | some p => some (fk, p)
            | none => none
          else none) → x.1 = FeedKey.ofPost x.2 := by
    intro x hx
    rw [List.mem_filterMap] at hx
    rcases hx with ⟨⟨fk, pid⟩, hmem, hsome⟩
    dsimp only at hsome
    cases hfa : feedAfter cursor? fk
    · simp [hfa] at hsome
    · simp only [hfa, ↓reduceIte] at hsome
      cases hpk : db.posts[pid]? with
      | none => rw [hpk] at hsome; simp at hsome
      | some p =>
        rw [hpk] at hsome
        simp only [Option.some.injEq] at hsome
        subst hsome
        have hidx := (hInv.feed_bijection fk pid).mp
          (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem)
        rcases hidx with ⟨q, hq, hfk⟩
        rw [hpk] at hq
        injection hq with hpq
        subst hpq
        exact hfk
  rw [hMapEq, List.pairwise_map]
  refine hPair.imp_of_mem ?_
  intro x y hx hy hlt
  rw [← hKeyMatch x hx, ← hKeyMatch y hy]
  exact hlt

/-- Every `queryFeed` result is strictly sorted in descending feed order with no duplicates. -/
theorem queryFeed_pairwise_desc {db : DbState} (hInv : Invariant db)
    (cursor? : Option FeedKey) (limit : Nat) :
    (db.queryFeed cursor? limit).toList.Pairwise
      (fun p₁ p₂ => FeedKey.cmpDesc (FeedKey.ofPost p₁) (FeedKey.ofPost p₂) = .lt) := by
  rw [queryFeed_toList_eq]
  exact (pairwise_filterMap_feed hInv cursor?).take

/-- Membership characterization for `allFeedAfter`. -/
theorem mem_allFeedAfter_iff {db : DbState} (hInv : Invariant db)
    (cursor? : Option FeedKey) (p : Post) :
    p ∈ allFeedAfter db cursor? ↔
      db.posts[p.id]? = some p ∧ feedAfter cursor? (FeedKey.ofPost p) = true := by
  unfold allFeedAfter feedEntryPost
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨fk, pid⟩, hmem, hsome⟩
    dsimp only at hsome
    by_cases hfa : feedAfter cursor? fk
    · simp only [hfa, ↓reduceIte] at hsome
      have hget : db.feedIndex[fk]? = some pid :=
        Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
      rcases (hInv.feed_bijection fk pid).mp hget with ⟨q, hq, rfl⟩
      rw [hq] at hsome
      injection hsome with hqp
      subst hqp
      have hwf := (hInv.posts_wf pid q hq).1
      rw [hwf]
      exact ⟨hq, hfa⟩
    · simp [hfa] at hsome
  · rintro ⟨hp, hfa⟩
    have hfk : db.feedIndex[FeedKey.ofPost p]? = some p.id :=
      (hInv.feed_bijection (FeedKey.ofPost p) p.id).mpr ⟨p, hp, rfl⟩
    refine ⟨(FeedKey.ofPost p, p.id), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hfk, ?_⟩
    simp only [hfa, ↓reduceIte, hp]

/-- Membership soundness for `queryFeed`. -/
theorem mem_queryFeed_implies {db : DbState} (hInv : Invariant db)
    {cursor? : Option FeedKey} {limit : Nat} {p : Post}
    (hMem : p ∈ (db.queryFeed cursor? limit).toList) :
    db.getPost p.id = some p ∧ feedAfter cursor? (FeedKey.ofPost p) = true := by
  rw [queryFeed_toList_eq] at hMem
  exact (mem_allFeedAfter_iff hInv cursor? p).mp (List.mem_of_mem_take hMem)

/-- Deleting a post excludes it from all future `queryFeed` results. -/
theorem queryFeed_excludes_deleted {db db' : DbState} (hInv : Invariant db)
    {id : PostId} {rel : Option ImageRef}
    (hDel : db.deletePost id = .ok (rel, db'))
    (cursor? : Option FeedKey) (limit : Nat) {p : Post}
    (hMem : p ∈ (db'.queryFeed cursor? limit).toList) :
    p.id ≠ id := by
  have hInv' := deletePost_preserves_invariant hInv hDel
  have ⟨hGet, _⟩ := mem_queryFeed_implies hInv' hMem
  intro hEq
  rw [hEq] at hGet
  have hNone := deletePost_getPost_self hDel
  rw [hNone] at hGet
  simp at hGet

private theorem cmpDesc_irrefl (a : FeedKey) : FeedKey.cmpDesc a a ≠ .lt := by
  rw [Std.ReflCmp.compare_self (cmp := FeedKey.cmpDesc)]
  decide

private theorem cmpDesc_asym {a b : FeedKey} (h : FeedKey.cmpDesc a b = .lt) :
    FeedKey.cmpDesc b a ≠ .lt := by
  intro hba
  have hgt : FeedKey.cmpDesc a b = .gt := Std.OrientedCmp.gt_iff_lt.mpr hba
  rw [h] at hgt
  cases hgt

/-- No duplicate post IDs appear in a `queryFeed` page. -/
theorem queryFeed_nodup_ids {db : DbState} (hInv : Invariant db)
    (cursor? : Option FeedKey) (limit : Nat) :
    ((db.queryFeed cursor? limit).toList.map Post.id).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine (queryFeed_pairwise_desc hInv cursor? limit).imp_of_mem ?_
  intro p₁ p₂ hp₁ hp₂ hlt heq
  have h₁ := (mem_queryFeed_implies hInv hp₁).1
  have h₂ := (mem_queryFeed_implies hInv hp₂).1
  unfold getPost at h₁ h₂
  rw [heq, h₂] at h₁
  injection h₁ with hpEq
  subst hpEq
  exact cmpDesc_irrefl (FeedKey.ofPost p₂) hlt

private theorem pairwise_lt_ext {l₁ l₂ : List Post}
    (h₁ : l₁.Pairwise (fun a b => FeedKey.cmpDesc (FeedKey.ofPost a) (FeedKey.ofPost b) = .lt))
    (h₂ : l₂.Pairwise (fun a b => FeedKey.cmpDesc (FeedKey.ofPost a) (FeedKey.ofPost b) = .lt))
    (hMem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      have hy : y ∈ ([] : List Post) := (hMem y).mpr List.mem_cons_self
      cases hy
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      have hx : x ∈ ([] : List Post) := (hMem x).mp List.mem_cons_self
      cases hx
    | cons y ys =>
      have hxMem : x ∈ y :: ys := (hMem x).mp List.mem_cons_self
      have hyMem : y ∈ x :: xs := (hMem y).mpr List.mem_cons_self
      rcases List.pairwise_cons.mp h₁ with ⟨hR₁, hTail₁⟩
      rcases List.pairwise_cons.mp h₂ with ⟨hR₂, hTail₂⟩
      have hxy : x = y := by
        cases List.mem_cons.mp hxMem with
        | inl h => exact h
        | inr hxYs =>
          cases List.mem_cons.mp hyMem with
          | inl h => exact h.symm
          | inr hyXs =>
            exfalso
            exact cmpDesc_asym (hR₁ y hyXs) (hR₂ x hxYs)
      subst hxy
      congr 1
      apply ih hTail₁ hTail₂
      intro z
      constructor
      · intro hz
        have hNe : z ≠ x := fun hzx => cmpDesc_irrefl (FeedKey.ofPost x) (hzx ▸ hR₁ z hz)
        have hIn : z ∈ x :: ys := (hMem z).mp (List.mem_cons_of_mem x hz)
        cases List.mem_cons.mp hIn with
        | inl hzx => exact absurd hzx hNe
        | inr h => exact h
      · intro hz
        have hNe : z ≠ x := fun hzx => cmpDesc_irrefl (FeedKey.ofPost x) (hzx ▸ hR₂ z hz)
        have hIn : z ∈ x :: xs := (hMem z).mpr (List.mem_cons_of_mem x hz)
        cases List.mem_cons.mp hIn with
        | inl hzx => exact absurd hzx hNe
        | inr h => exact h

private theorem pairwise_rel_of_take_drop {α : Type} {R : α → α → Prop} {l : List α}
    (hPair : l.Pairwise R) {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    R l[i] l[j] := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    rcases List.pairwise_cons.mp hPair with ⟨hx, hxs⟩
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact hx _ (List.getElem_mem _)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.getElem_cons_succ]
        exact ih hxs (by simpa using hi) (by simpa using hj) (by omega)

/-- Cursor pagination continuation partitions descending results without omissions or duplicates. -/
theorem queryFeed_cursor_partition {db : DbState} (hInv : Invariant db)
    (cursor? : Option FeedKey) (limit₁ limit₂ : Nat)
    (hPos : 0 < limit₁)
    (hFull : (db.queryFeed cursor? limit₁).size = limit₁) :
    (db.queryFeed cursor? limit₁).toList ++
      (db.queryFeed (some (FeedKey.ofPost ((db.queryFeed cursor? limit₁)[limit₁ - 1]'(by omega)))) limit₂).toList =
    (db.queryFeed cursor? (limit₁ + limit₂)).toList := by
  let lastPost := (db.queryFeed cursor? limit₁)[limit₁ - 1]'(by omega)
  let all := allFeedAfter db cursor?
  let allAfter := allFeedAfter db (some (FeedKey.ofPost lastPost))
  have hPage1 : (db.queryFeed cursor? limit₁).toList = all.take limit₁ :=
    queryFeed_toList_eq db cursor? limit₁
  have hLenAll : limit₁ ≤ all.length := by
    have hLenPage : (db.queryFeed cursor? limit₁).toList.length = limit₁ := by
      simp [hFull]
    rw [hPage1, List.length_take] at hLenPage
    omega
  have hLastEq : lastPost = all[limit₁ - 1]'(by omega) := by
    have hIdxPage : lastPost = (db.queryFeed cursor? limit₁).toList[limit₁ - 1]'(by simp [hFull]; omega) := by
      simp [lastPost]
    rw [hIdxPage]
    simp only [hPage1, List.getElem_take]
  have hAllPair : all.Pairwise (fun a b => FeedKey.cmpDesc (FeedKey.ofPost a) (FeedKey.ofPost b) = .lt) :=
    pairwise_filterMap_feed hInv cursor?
  have hAfterPair : allAfter.Pairwise (fun a b => FeedKey.cmpDesc (FeedKey.ofPost a) (FeedKey.ofPost b) = .lt) :=
    pairwise_filterMap_feed hInv (some (FeedKey.ofPost lastPost))
  have hDropPair : (all.drop limit₁).Pairwise (fun a b => FeedKey.cmpDesc (FeedKey.ofPost a) (FeedKey.ofPost b) = .lt) :=
    hAllPair.drop
  have hLastInAll : lastPost ∈ all := by
    rw [hLastEq]
    exact List.getElem_mem _
  have hLastAfterCur : feedAfter cursor? (FeedKey.ofPost lastPost) = true :=
    ((mem_allFeedAfter_iff hInv cursor? lastPost).mp hLastInAll).2
  have hSplit : all = all.take limit₁ ++ all.drop limit₁ := (List.take_append_drop limit₁ all).symm
  have hMemEq : ∀ p, p ∈ allAfter ↔ p ∈ all.drop limit₁ := by
    intro p
    rw [mem_allFeedAfter_iff hInv (some (FeedKey.ofPost lastPost)) p]
    unfold feedAfter
    rw [beq_iff_eq]
    constructor
    · rintro ⟨hpPost, hpGt⟩
      have hpCur : feedAfter cursor? (FeedKey.ofPost p) = true := by
        cases cursor? with
        | none => rfl
        | some cur =>
          unfold feedAfter at hLastAfterCur ⊢
          rw [beq_iff_eq] at hLastAfterCur ⊢
          exact Std.TransCmp.lt_trans hLastAfterCur hpGt
      have hpInAll : p ∈ all := (mem_allFeedAfter_iff hInv cursor? p).mpr ⟨hpPost, hpCur⟩
      have hpSplit : p ∈ all.take limit₁ ++ all.drop limit₁ := hSplit ▸ hpInAll
      cases List.mem_append.mp hpSplit with
      | inr hDrop => exact hDrop
      | inl hTake =>
        exfalso
        rcases List.getElem_of_mem hTake with ⟨idx, hidxLt, hidxEq⟩
        rw [List.length_take] at hidxLt
        have hidxLe : idx ≤ limit₁ - 1 := by omega
        have hidxBound : idx < all.length := by omega
        rw [List.getElem_take] at hidxEq
        by_cases hEq : idx = limit₁ - 1
        · subst hEq
          rw [← hLastEq] at hidxEq
          subst hidxEq
          exact cmpDesc_irrefl (FeedKey.ofPost _) hpGt
        · have hLtIdx : idx < limit₁ - 1 := by omega
          have hRel : FeedKey.cmpDesc (FeedKey.ofPost all[idx]) (FeedKey.ofPost all[limit₁ - 1]) = .lt :=
            pairwise_rel_of_take_drop hAllPair hidxBound (by omega) hLtIdx
          rw [hidxEq, ← hLastEq] at hRel
          exact cmpDesc_asym hRel hpGt
    · intro hpDrop
      have hpInAll : p ∈ all := hSplit ▸ List.mem_append.mpr (.inr hpDrop)
      have hpPost : db.posts[p.id]? = some p := ((mem_allFeedAfter_iff hInv cursor? p).mp hpInAll).1
      rcases List.getElem_of_mem hpDrop with ⟨j, hjLt, hjEq⟩
      rw [List.length_drop] at hjLt
      rw [List.getElem_drop] at hjEq
      have hRel : FeedKey.cmpDesc (FeedKey.ofPost all[limit₁ - 1]) (FeedKey.ofPost all[limit₁ + j]) = .lt :=
        pairwise_rel_of_take_drop hAllPair (by omega) (by omega) (by omega)
      rw [← hLastEq, hjEq] at hRel
      exact ⟨hpPost, hRel⟩
  have hAfterEqDrop : allAfter = all.drop limit₁ := pairwise_lt_ext hAfterPair hDropPair hMemEq
  rw [queryFeed_toList_eq, queryFeed_toList_eq, queryFeed_toList_eq]
  change all.take limit₁ ++ allAfter.take limit₂ = all.take (limit₁ + limit₂)
  rw [hAfterEqDrop, List.take_add]

/-- Compaction preserves live posts, feed index, feed query results, and counters. -/
theorem compactDb_equiv (db : DbState) :
    db.compactDb.posts = db.posts ∧
    db.compactDb.feedIndex = db.feedIndex ∧
    db.compactDb.nextPostId = db.nextPostId ∧
    db.compactDb.lastSeq = db.lastSeq ∧
    (∀ cursor? limit, db.compactDb.queryFeed cursor? limit = db.queryFeed cursor? limit) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

end DbState

end Leaf.Core