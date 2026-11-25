import Leaf.Core.Frame
import Leaf.Core.DbModel
import Leaf.Core.BucketModel
import Std.Data.ExtTreeMap

namespace Leaf.Core

/-- Pure sequential frame scanner: decodes valid frames from offset 0 until EOF or first invalid frame,
    returning `(validFrames, validEndOffset)`. -/
def scanFramesAux (pol : StoragePolicy) (kind : FrameKind) (bytes : ByteArray)
    (offset : Nat) (acc : Array Frame) : Array Frame × Nat :=
  if hOff : offset < bytes.size then
    match decodeFrameAt pol kind bytes offset with
    | .ok (frame, nextOffset) =>
      if hAdv : offset < nextOffset then
        have : bytes.size - nextOffset < bytes.size - offset := Nat.sub_lt_sub_left hOff hAdv
        scanFramesAux pol kind bytes nextOffset (acc.push frame)
      else
        (acc, offset)
    | .error _ => (acc, offset)
  else
    (acc, offset)
termination_by bytes.size - offset

/-- Scans a contiguous byte buffer of frames, stopping at EOF or first corrupt/truncated frame. -/
def scanFrames (pol : StoragePolicy) (kind : FrameKind) (bytes : ByteArray) : Array Frame × Nat :=
  scanFramesAux pol kind bytes 0 #[]

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

/-- Applies a single committed `WalOp` to `DbState`, preserving `DbState.Invariant`. -/
def applyCommittedWalOp (db : DbState) (seq : SeqNo) (op : WalOp) : DbState :=
  let nextSeq : SeqNo := ⟨if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val⟩
  match op with
  | .putPost post =>
    if 0 < post.id.val.toNat ∧ post.id.val.toNat + 1 < 2 ^ 64 ∧ True then
      let feed1 :=
        match db.posts[post.id]? with
        | some old => db.feedIndex.erase (FeedKey.ofPost old)
        | none => db.feedIndex
      let nextId : PostId :=
        ⟨if db.nextPostId.val ≤ post.id.val then post.id.val + 1 else db.nextPostId.val⟩
      { posts := db.posts.insert post.id post
        feedIndex := feed1.insert (FeedKey.ofPost post) post.id
        tombstones := db.tombstones.erase post.id
        nextPostId := nextId
        lastSeq := nextSeq }
    else
      db
  | .updatePost post =>
    match db.posts[post.id]? with
    | none => db
    | some existing =>
      if True then
        let feed1 := db.feedIndex.erase (FeedKey.ofPost existing)
        { db with
          posts := db.posts.insert post.id post
          feedIndex := feed1.insert (FeedKey.ofPost post) post.id
          lastSeq := nextSeq }
      else
        db
  | .deletePost id =>
    match db.posts[id]? with
    | none => db
    | some existing =>
      { db with
        posts := db.posts.erase id
        feedIndex := db.feedIndex.erase (FeedKey.ofPost existing)
        tombstones := db.tombstones.insert id
        lastSeq := nextSeq }
  | .beginTx | .allocObject _ | .incRef _ | .decRef _ | .commitTx | .abortTx => db

theorem applyCommittedWalOp_preserves_invariant {db : DbState} (hInv : Invariant db)
    (seq : SeqNo) (op : WalOp) : Invariant (applyCommittedWalOp db seq op) := by
  cases op with
  | beginTx | allocObject _ | incRef _ | decRef _ | commitTx | abortTx => exact hInv
  | putPost post =>
    dsimp only [applyCommittedWalOp]
    by_cases hBounds : 0 < post.id.val.toNat ∧ post.id.val.toNat + 1 < 2 ^ 64 ∧
        post.version.val ≤ (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val)
    · rw [ite_eq_left_of_eq_true (h := eq_true hBounds)]
      have hPos : 0 < post.id.val.toNat := hBounds.1
      have hFits : post.id.val.toNat + 1 < 2 ^ 64 := hBounds.2.1
      have hVer : post.version.val.toNat ≤
          (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val).toNat := hBounds.2.2
      have hSeqLe : ∀ {x : UInt64}, x.toNat ≤ db.lastSeq.val.toNat →
          x.toNat ≤ (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val).toNat := by
        intro x hx
        by_cases hLt : db.lastSeq.val < seq.val
        · rw [ite_eq_left_of_eq_true (h := eq_true hLt)]
          have hlt' : db.lastSeq.val.toNat < seq.val.toNat := hLt
          omega
        · rw [ite_eq_right_of_eq_false (h := eq_false hLt)]; exact hx
      have hNextLt : post.id.val.toNat <
          (if db.nextPostId.val ≤ post.id.val then post.id.val + 1 else db.nextPostId.val).toNat := by
        by_cases hLe : db.nextPostId.val ≤ post.id.val
        · simp only [hLe, ↓reduceIte, uint64_succ_toNat hFits]; omega
        · simp only [hLe, ↓reduceIte]
          exact Nat.lt_of_not_le (mt (fun h => show db.nextPostId.val ≤ post.id.val from h) hLe)
      have hNextLe : ∀ {x : PostId}, x.val.toNat < db.nextPostId.val.toNat →
          x.val.toNat < (if db.nextPostId.val ≤ post.id.val then post.id.val + 1 else db.nextPostId.val).toNat := by
        intro x hx
        by_cases hLe : db.nextPostId.val ≤ post.id.val
        · simp only [hLe, ↓reduceIte, uint64_succ_toNat hFits]
          have hle' : db.nextPostId.val.toNat ≤ post.id.val.toNat := hLe
          omega
        · simp only [hLe, ↓reduceIte]; exact hx
      refine
        { nextPostId_pos := Nat.lt_trans hPos hNextLt
          posts_wf := ?_
          feed_bijection := ?_
          tombstone_disjoint := ?_
          tombstones_wf := ?_ }
      · intro k p hp
        dsimp only at hp
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hp
        by_cases hEq : post.id = k
        · simp only [hEq, ↓reduceIte] at hp; cases hp; subst hEq
          exact ⟨rfl, hPos, hNextLt, hVer⟩
        · simp only [hEq, ↓reduceIte] at hp
          have hwf := hInv.posts_wf k p hp
          exact ⟨hwf.1, hwf.2.1, hNextLe hwf.2.2.1, hSeqLe hwf.2.2.2⟩
      · intro fk id
        dsimp only
        simp only [Std.ExtTreeMap.getElem?_insert, cmpDesc_eq_iff_eq, compare_eq_iff_eq]
        constructor
        · intro h
          by_cases hFk : FeedKey.ofPost post = fk
          · simp only [hFk, ↓reduceIte] at h; cases h; subst hFk
            refine ⟨post, ?_, rfl⟩
            simp
          · simp only [hFk, ↓reduceIte] at h
            have hOldNe : id ≠ post.id := by
              cases hExisting : db.posts[post.id]? with
              | none =>
                rw [hExisting] at h; dsimp only at h
                obtain ⟨p, hp, _⟩ := (hInv.feed_bijection fk id).mp h
                intro hid; subst hid; rw [hExisting] at hp; cases hp
              | some old =>
                rw [hExisting] at h; dsimp only at h
                simp only [Std.ExtTreeMap.getElem?_erase, cmpDesc_eq_iff_eq] at h
                by_cases hFkOld : FeedKey.ofPost old = fk
                · simp only [hFkOld, ↓reduceIte] at h; cases h
                · simp only [hFkOld, ↓reduceIte] at h
                  obtain ⟨p, hp, hpfk⟩ := (hInv.feed_bijection fk id).mp h
                  intro hid; subst hid
                  rw [hExisting] at hp; cases hp
                  exact hFkOld hpfk.symm
            cases hExisting : db.posts[post.id]? with
            | none =>
              rw [hExisting] at h; dsimp only at h
              obtain ⟨p, hp, hpfk⟩ := (hInv.feed_bijection fk id).mp h
              refine ⟨p, ?_, hpfk⟩
              simp [hOldNe.symm, hp]
            | some old =>
              rw [hExisting] at h; dsimp only at h
              simp only [Std.ExtTreeMap.getElem?_erase, cmpDesc_eq_iff_eq] at h
              by_cases hFkOld : FeedKey.ofPost old = fk
              · simp only [hFkOld, ↓reduceIte] at h; cases h
              · simp only [hFkOld, ↓reduceIte] at h
                obtain ⟨p, hp, hpfk⟩ := (hInv.feed_bijection fk id).mp h
                refine ⟨p, ?_, hpfk⟩
                simp [hOldNe.symm, hp]
        · rintro ⟨p, hp, hpfk⟩
          by_cases hId : post.id = id
          · simp only [hId, ↓reduceIte] at hp; cases hp; subst hId
            have : FeedKey.ofPost post = fk := hpfk.symm
            simp [this]
          · simp only [hId, ↓reduceIte] at hp
            have hFkNe : FeedKey.ofPost post ≠ fk := by
              intro hEq
              have hIdEq : post.id = (FeedKey.ofPost post).id := rfl
              have hIdEq2 : p.id = fk.id := by rw [hpfk]; rfl
              have hwf := (hInv.posts_wf id p hp).1
              rw [hIdEq, hEq, ← hIdEq2, hwf] at hId
              exact hId rfl
            simp only [hFkNe, ↓reduceIte]
            have hOrig := (hInv.feed_bijection fk id).mpr ⟨p, hp, hpfk⟩
            cases hExisting : db.posts[post.id]? with
            | none => exact hOrig
            | some old =>
              dsimp only
              simp only [Std.ExtTreeMap.getElem?_erase, cmpDesc_eq_iff_eq]
              by_cases hFkOld : FeedKey.ofPost old = fk
              · simp only [hFkOld, ↓reduceIte]
                obtain ⟨p', hp', hpfk'⟩ := (hInv.feed_bijection fk id).mp hOrig
                have h1 : old.id = post.id := (hInv.posts_wf post.id old hExisting).1
                have h2 : p'.id = id := (hInv.posts_wf id p' hp').1
                have h3 : old.id = (FeedKey.ofPost old).id := rfl
                have h4 : p'.id = (FeedKey.ofPost p').id := rfl
                have hIdEq : post.id = id := by rw [← h1, h3, hFkOld, hpfk', ← h4, h2]
                exact absurd hIdEq hId
              · simp only [hFkOld, ↓reduceIte]; exact hOrig
      · intro id hid
        dsimp only at hid ⊢
        rw [Std.ExtTreeMap.mem_insert] at hid
        rw [Std.ExtTreeSet.mem_erase]
        rintro ⟨hNe, hMem⟩
        rcases hid with hEq | hIn
        · have hIdEq : post.id = id := Std.LawfulEqOrd.eq_of_compare (α := PostId) (by simpa using hEq)
          exact hNe (by simp [hIdEq])
        · exact hInv.tombstone_disjoint id hIn hMem
      · intro id hid
        dsimp only
        rw [Std.ExtTreeSet.mem_erase] at hid
        exact ⟨(hInv.tombstones_wf id hid.2).1, hNextLe (hInv.tombstones_wf id hid.2).2⟩
    · rw [ite_eq_right_of_eq_false (h := eq_false hBounds)]; exact hInv
  | updatePost post =>
    dsimp only [applyCommittedWalOp]
    cases hEx : db.posts[post.id]? with
    | none => exact hInv
    | some existing =>
      have hExWf := hInv.posts_wf post.id existing hEx
      dsimp only
      by_cases hVer : post.version.val ≤
          (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val)
      · rw [ite_eq_left_of_eq_true (h := eq_true hVer)]
        have hVerNat : post.version.val.toNat ≤
            (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val).toNat := hVer
        have hSeqLe : ∀ {x : UInt64}, x.toNat ≤ db.lastSeq.val.toNat →
            x.toNat ≤ (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val).toNat := by
          intro x hx
          by_cases hLt : db.lastSeq.val < seq.val
          · rw [ite_eq_left_of_eq_true (h := eq_true hLt)]
            have hlt' : db.lastSeq.val.toNat < seq.val.toNat := hLt
            omega
          · rw [ite_eq_right_of_eq_false (h := eq_false hLt)]; exact hx
        refine
          { nextPostId_pos := hInv.nextPostId_pos
            posts_wf := ?_
            feed_bijection := ?_
            tombstone_disjoint := ?_
            tombstones_wf := hInv.tombstones_wf }
        · intro k p hp
          dsimp only at hp
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hp
          by_cases hEq : post.id = k
          · simp only [hEq, ↓reduceIte] at hp; cases hp; subst hEq
            exact ⟨rfl, hExWf.2.1, hExWf.2.2.1, hVerNat⟩
          · simp only [hEq, ↓reduceIte] at hp
            have hwf := hInv.posts_wf k p hp
            exact ⟨hwf.1, hwf.2.1, hwf.2.2.1, hSeqLe hwf.2.2.2⟩
        · intro fk id
          dsimp only
          simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase,
            cmpDesc_eq_iff_eq, compare_eq_iff_eq]
          constructor
          · intro h
            by_cases hFk : FeedKey.ofPost post = fk
            · simp only [hFk, ↓reduceIte] at h; cases h; subst hFk
              refine ⟨post, ?_, rfl⟩
              simp
            · simp only [hFk, ↓reduceIte] at h
              by_cases hOldFk : FeedKey.ofPost existing = fk
              · simp only [hOldFk, ↓reduceIte] at h; cases h
              · simp only [hOldFk, ↓reduceIte] at h
                obtain ⟨p, hp, hpfk⟩ := (hInv.feed_bijection fk id).mp h
                have hidNe : post.id ≠ id := by
                  intro hid; subst hid; rw [hEx] at hp; cases hp; exact hOldFk hpfk.symm
                refine ⟨p, ?_, hpfk⟩
                simp only [hidNe, ↓reduceIte]; exact hp
          · rintro ⟨p, hp, hpfk⟩
            by_cases hId : post.id = id
            · simp only [hId, ↓reduceIte] at hp; cases hp; subst hId
              have : FeedKey.ofPost post = fk := hpfk.symm
              simp [this]
            · simp only [hId, ↓reduceIte] at hp
              have hFkNe : FeedKey.ofPost post ≠ fk := by
                intro hEq
                have h1 : post.id = (FeedKey.ofPost post).id := rfl
                have h2 : p.id = fk.id := by rw [hpfk]; rfl
                have hwf := (hInv.posts_wf id p hp).1
                rw [h1, hEq, ← h2, hwf] at hId
                exact hId rfl
              simp only [hFkNe, ↓reduceIte]
              have hOrig := (hInv.feed_bijection fk id).mpr ⟨p, hp, hpfk⟩
              by_cases hOldFk : FeedKey.ofPost existing = fk
              · simp only [hOldFk, ↓reduceIte]
                have h1 : existing.id = post.id := hExWf.1
                have h2 : p.id = id := (hInv.posts_wf id p hp).1
                have h3 : existing.id = (FeedKey.ofPost existing).id := rfl
                have h4 : p.id = (FeedKey.ofPost p).id := rfl
                have hIdEq : post.id = id := by rw [← h1, h3, hOldFk, hpfk, ← h4, h2]
                exact absurd hIdEq hId
              · simp only [hOldFk, ↓reduceIte]; exact hOrig
        · intro id hid
          dsimp only at hid ⊢
          rw [Std.ExtTreeMap.mem_insert] at hid
          rcases hid with hEq | hIn
          · have hIdEq : post.id = id := Std.LawfulEqOrd.eq_of_compare (α := PostId) (by simpa using hEq)
            subst hIdEq
            have hInEx : post.id ∈ db.posts :=
              Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hEx]; rfl)
            exact hInv.tombstone_disjoint post.id hInEx
          · exact hInv.tombstone_disjoint id hIn
      · rw [ite_eq_right_of_eq_false (h := eq_false hVer)]; exact hInv
  | deletePost id =>
    dsimp only [applyCommittedWalOp]
    cases hEx : db.posts[id]? with
    | none => exact hInv
    | some existing =>
      have hExWf := hInv.posts_wf id existing hEx
      have hSeqLe : ∀ {x : UInt64}, x.toNat ≤ db.lastSeq.val.toNat →
          x.toNat ≤ (if db.lastSeq.val < seq.val then seq.val else db.lastSeq.val).toNat := by
        intro x hx
        by_cases hLt : db.lastSeq.val < seq.val
        · rw [ite_eq_left_of_eq_true (h := eq_true hLt)]
          have hlt' : db.lastSeq.val.toNat < seq.val.toNat := hLt
          omega
        · rw [ite_eq_right_of_eq_false (h := eq_false hLt)]; exact hx
      dsimp only
      refine
        { nextPostId_pos := hInv.nextPostId_pos
          posts_wf := ?_
          feed_bijection := ?_
          tombstone_disjoint := ?_
          tombstones_wf := ?_ }
      · intro k p hp
        dsimp only at hp
        simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq] at hp
        by_cases hEq : id = k
        · simp only [hEq, ↓reduceIte] at hp; cases hp
        · simp only [hEq, ↓reduceIte] at hp
          have hwf := hInv.posts_wf k p hp
          exact ⟨hwf.1, hwf.2.1, hwf.2.2.1, hSeqLe hwf.2.2.2⟩
      · intro fk pid
        dsimp only
        simp only [Std.ExtTreeMap.getElem?_erase, cmpDesc_eq_iff_eq, compare_eq_iff_eq]
        constructor
        · intro h
          by_cases hFk : FeedKey.ofPost existing = fk
          · simp only [hFk, ↓reduceIte] at h; cases h
          · simp only [hFk, ↓reduceIte] at h
            obtain ⟨p, hp, hpfk⟩ := (hInv.feed_bijection fk pid).mp h
            have hidNe : id ≠ pid := by
              intro hEq; subst hEq; rw [hEx] at hp; cases hp; exact hFk hpfk.symm
            simp only [hidNe, ↓reduceIte]
            exact ⟨p, hp, hpfk⟩
        · rintro ⟨p, hp, hpfk⟩
          by_cases hEq : id = pid
          · simp only [hEq, ↓reduceIte] at hp; cases hp
          · simp only [hEq, ↓reduceIte] at hp
            have hFkNe : FeedKey.ofPost existing ≠ fk := by
              intro hFkEq
              have h1 : existing.id = (FeedKey.ofPost existing).id := rfl
              have h2 : p.id = fk.id := by rw [hpfk]; rfl
              have hwf := (hInv.posts_wf pid p hp).1
              rw [← hExWf.1, h1, hFkEq, ← h2, hwf] at hEq
              exact hEq rfl
            simp only [hFkNe, ↓reduceIte]
            exact (hInv.feed_bijection fk pid).mpr ⟨p, hp, hpfk⟩
      · intro tid hmem
        dsimp only at hmem ⊢
        rw [Std.ExtTreeMap.mem_erase] at hmem
        rw [Std.ExtTreeSet.mem_insert]
        rintro (hEq | hOld)
        · have hIdEq : id = tid := Std.LawfulEqOrd.eq_of_compare (α := PostId) (by simpa using hEq)
          exact hmem.1 (by simp [hIdEq])
        · exact hInv.tombstone_disjoint tid hmem.2 hOld
      · intro tid hmem
        dsimp only
        rw [Std.ExtTreeSet.mem_insert] at hmem
        rcases hmem with hEq | hOld
        · have hIdEq : id = tid := Std.LawfulEqOrd.eq_of_compare (α := PostId) (by simpa using hEq)
          subst hIdEq; exact ⟨hExWf.2.1, hExWf.2.2.1⟩
        · exact hInv.tombstones_wf tid hOld

/-- Auxiliary transactional WAL replay holding per-`TxId` buffered operations until `commitTx`. -/
def replayWalOpsAux (db : DbState)
    (pending : Std.ExtTreeMap UInt64 (List (SeqNo × WalOp)))
    (entries : List (TxId × SeqNo × WalOp)) : DbState :=
  match entries with
  | [] => db
  | (txId, seq, op) :: rest =>
    match op with
    | .beginTx =>
      replayWalOpsAux db (pending.insert txId.val []) rest
    | .abortTx =>
      replayWalOpsAux db (pending.erase txId.val) rest
    | .commitTx =>
      let ops := (pending[txId.val]? ).getD []
      let db' := ops.foldl (fun s (so : SeqNo × WalOp) => applyCommittedWalOp s so.1 so.2) db
      replayWalOpsAux db' (pending.erase txId.val) rest
    | _ =>
      let prev := (pending[txId.val]? ).getD []
      replayWalOpsAux db (pending.insert txId.val (prev ++ [(seq, op)])) rest

/-- Replays a stream of WAL entries onto `base`, applying only committed transactions. -/
def replayWalOps (base : DbState) (entries : List (TxId × SeqNo × WalOp)) : DbState :=
  replayWalOpsAux base ∅ entries

private theorem foldl_applyCommittedWalOp_preserves_invariant
    (ops : List (SeqNo × WalOp)) {db : DbState} (hInv : Invariant db) :
    Invariant (ops.foldl (fun s (so : SeqNo × WalOp) => applyCommittedWalOp s so.1 so.2) db) := by
  induction ops generalizing db with
  | nil => exact hInv
  | cons hd tl ih => exact ih (applyCommittedWalOp_preserves_invariant hInv hd.1 hd.2)

theorem replayWalOpsAux_preserves_invariant
    (entries : List (TxId × SeqNo × WalOp))
    {db : DbState} (hInv : Invariant db)
    (pending : Std.ExtTreeMap UInt64 (List (SeqNo × WalOp))) :
    Invariant (replayWalOpsAux db pending entries) := by
  induction entries generalizing db pending with
  | nil => exact hInv
  | cons hd tl ih =>
    rcases hd with ⟨txId, seq, op⟩
    cases op with
    | beginTx => exact ih hInv _
    | abortTx => exact ih hInv _
    | commitTx =>
      apply ih
      exact foldl_applyCommittedWalOp_preserves_invariant _ hInv
    | putPost _ | updatePost _ | deletePost _ | allocObject _ | incRef _ | decRef _ =>
      exact ih hInv _

theorem replayWalOps_preserves_invariant
    {base : DbState} (hInv : Invariant base)
    (entries : List (TxId × SeqNo × WalOp)) :
    Invariant (replayWalOps base entries) :=
  replayWalOpsAux_preserves_invariant entries hInv ∅

private theorem txId_bne_self (t : TxId) : (t != t) = false := by
  cases t with
  | mk v =>
    change (!(v == v)) = false
    simp

private theorem txId_bne_ne {a b : TxId} (h : a.val ≠ b.val) : (a != b) = true := by
  cases a with
  | mk va =>
    cases b with
    | mk vb =>
      change (!(va == vb)) = true
      simp [h]

private theorem replayWalOpsAux_uncommitted_aux
    (tx : TxId) (entries : List (TxId × SeqNo × WalOp))
    (hNoCommit : ∀ s, (tx, s, WalOp.commitTx) ∉ entries)
    (db : DbState)
    (p1 p2 : Std.ExtTreeMap UInt64 (List (SeqNo × WalOp)))
    (hAgree : ∀ k : UInt64, k ≠ tx.val → p1[k]? = p2[k]?) :
    replayWalOpsAux db p1 entries =
      replayWalOpsAux db p2 (entries.filter (fun e => e.1 != tx)) := by
  induction entries generalizing db p1 p2 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨txId, seq, op⟩
    have hNoCommitTl : ∀ s, (tx, s, WalOp.commitTx) ∉ tl := fun s h =>
      hNoCommit s (List.mem_cons_of_mem _ h)
    by_cases hTx : txId = tx
    · subst hTx
      have hNotCommit : op ≠ .commitTx := fun h => by
        subst h; exact hNoCommit seq (List.mem_cons_self ..)
      have hFilter : ((txId, seq, op) :: tl).filter (fun e => e.1 != txId) =
          tl.filter (fun e => e.1 != txId) := by
        simp [List.filter, txId_bne_self]
      rw [hFilter]
      cases op with
      | commitTx => exact absurd rfl hNotCommit
      | beginTx =>
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
        by_cases hEq : txId.val = k
        · exact absurd hEq.symm hk
        · simp [hEq, hAgree k hk]
      | abortTx =>
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq]
        by_cases hEq : txId.val = k
        · exact absurd hEq.symm hk
        · simp [hEq, hAgree k hk]
      | putPost _ | updatePost _ | deletePost _ | allocObject _ | incRef _ | decRef _ =>
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
        by_cases hEq : txId.val = k
        · exact absurd hEq.symm hk
        · simp [hEq, hAgree k hk]
    · have hNeVal : txId.val ≠ tx.val := fun h => hTx (by cases txId; cases tx; cases h; rfl)
      have hFilter : ((txId, seq, op) :: tl).filter (fun e => e.1 != tx) =
          (txId, seq, op) :: tl.filter (fun e => e.1 != tx) := by
        simp [List.filter, txId_bne_ne hNeVal]
      rw [hFilter]
      cases op with
      | beginTx =>
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
        by_cases hEq : txId.val = k <;> simp [hEq, hAgree k hk]
      | abortTx =>
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq]
        by_cases hEq : txId.val = k <;> simp [hEq, hAgree k hk]
      | commitTx =>
        have hEqPending : p1[txId.val]? = p2[txId.val]? := hAgree txId.val hNeVal
        dsimp only [replayWalOpsAux]
        rw [hEqPending]
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_erase, compare_eq_iff_eq]
        by_cases hEq : txId.val = k <;> simp [hEq, hAgree k hk]
      | putPost _ | updatePost _ | deletePost _ | allocObject _ | incRef _ | decRef _ =>
        have hEqPending : p1[txId.val]? = p2[txId.val]? := hAgree txId.val hNeVal
        dsimp only [replayWalOpsAux]
        rw [hEqPending]
        apply ih hNoCommitTl
        intro k hk
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
        by_cases hEq : txId.val = k <;> simp [hEq, hAgree k hk]

/-- Uncommitted transactions (those without a `commitTx` record) have zero effect on `replayWalOps`. -/
theorem replayWalOps_uncommitted_ignored (base : DbState) (tx : TxId)
    (entries : List (TxId × SeqNo × WalOp))
    (hNoCommit : ∀ s, (tx, s, WalOp.commitTx) ∉ entries) :
    replayWalOps base entries = replayWalOps base (entries.filter (fun e => e.1 != tx)) :=
  replayWalOpsAux_uncommitted_aux tx entries hNoCommit base ∅ ∅ (fun _ _ => rfl)

end DbState

/-- Pure bounded segment read cache with capacity enforcement. -/
structure BoundedCache where
  capacity : Nat
  entries  : List (UInt64 × ByteArray) := []
  deriving Inhabited

namespace BoundedCache

def empty (capacity : Nat) : BoundedCache :=
  { capacity := capacity, entries := [] }

def lookup (c : BoundedCache) (key : UInt64) : Option ByteArray :=
  (c.entries.find? (fun e => e.1 == key)).map (·.2)

def insert (c : BoundedCache) (key : UInt64) (val : ByteArray) : BoundedCache :=
  if c.capacity == 0 then
    c
  else
    let filtered := c.entries.filter (fun e => e.1 != key)
    { c with entries := ((key, val) :: filtered).take c.capacity }

def invalidate (c : BoundedCache) (key : UInt64) : BoundedCache :=
  { c with entries := c.entries.filter (fun e => e.1 != key) }

theorem insert_length_le (c : BoundedCache) (k : UInt64) (v : ByteArray)
    (hCap : c.entries.length ≤ c.capacity) :
    (c.insert k v).entries.length ≤ c.capacity := by
  dsimp only [insert]
  by_cases h0 : (c.capacity == 0) = true
  · simp only [h0, ↓reduceIte]; exact hCap
  · simp only [h0, Bool.false_eq_true, ↓reduceIte, List.length_take]
    exact Nat.min_le_left _ _

theorem insert_lookup_self (c : BoundedCache) (k : UInt64) (v : ByteArray)
    (hPos : 0 < c.capacity) :
    (c.insert k v).lookup k = some v := by
  have hNe : (c.capacity == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  dsimp only [insert, lookup]
  simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨m, hm⟩ : ∃ m, c.capacity = m + 1 := ⟨c.capacity - 1, by omega⟩
  rw [hm]
  simp [List.take]

end BoundedCache

section PinGC

/-- Predicate deciding whether an object must be retained during pin-aware GC. -/
def shouldKeepObject {segSize : Nat} (pinned : ObjectKey → Bool) (k : ObjectKey)
    (m : BucketEntryMeta segSize) : Bool :=
  m.refCount > 0 || pinned k

/-- Pin-aware object filtering: retains all live (`refCount > 0`) and reader-pinned objects. -/
def filterPinnedObjects {segSize : Nat} (pinned : ObjectKey → Bool)
    (objs : Std.ExtTreeMap ObjectKey (BucketEntryMeta segSize)) :
    Std.ExtTreeMap ObjectKey (BucketEntryMeta segSize) :=
  objs.filter (fun k m => shouldKeepObject pinned k m)

theorem filterPinnedObjects_preserves_live_or_pinned {segSize : Nat}
    (pinned : ObjectKey → Bool)
    (objs : Std.ExtTreeMap ObjectKey (BucketEntryMeta segSize))
    (k : ObjectKey) (m : BucketEntryMeta segSize)
    (hMem : objs[k]? = some m)
    (hKeep : m.refCount > 0 ∨ pinned k = true) :
    (filterPinnedObjects pinned objs)[k]? = some m := by
  dsimp only [filterPinnedObjects]
  rw [Std.ExtTreeMap.getElem?_filter']
  rw [hMem]
  dsimp only [Option.filter, shouldKeepObject]
  rcases hKeep with hRc | hPin
  · have : (decide (m.refCount > 0) || pinned k) = true := by simp [hRc]
    simp [this]
  · simp [hPin]

end PinGC

end Leaf.Core
