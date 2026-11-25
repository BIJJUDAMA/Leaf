import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Leaf.Core.Schema
import Leaf.Core.Crc32
import Leaf.Core.Sha256

namespace Leaf.Core

/-- Metadata for a content-addressed object stored in a pack segment. -/
structure BucketEntryMeta (segmentSize : Nat) where
  key      : ObjectKey
  location : ObjectLocation segmentSize
  mime     : MimeType
  crc32    : UInt32
  byteSize : Nat
  refCount : Nat
  deriving DecidableEq, Repr

/-- Metadata describing allocated byte spans inside a pack segment. -/
structure SegmentMeta (segmentSize : Nat) where
  id      : SegmentId
  used    : Nat
  used_le : used ≤ segmentSize
  live    : Array (ObjectLocation segmentSize)
  deriving DecidableEq, Repr

/-- In-memory verified model of content-addressed segmented object storage. -/
structure BucketState (policy : StoragePolicy) where
  objects   : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize)
  byDigest  : Std.ExtTreeMap Sha256Digest (Array ObjectKey)
  segments  : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)
  activeSeg : SegmentId
  nextSegId : SegmentId
  blobs     : Std.ExtTreeMap ObjectKey ByteArray

namespace BucketState

/-- Allocator state shared between normal insertion and segment compaction. -/
structure RepackAcc (policy : StoragePolicy) where
  objects   : Std.ExtTreeMap ObjectKey (BucketEntryMeta policy.segmentSize)
  segments  : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)
  activeSeg : SegmentId
  nextSegId : SegmentId

/-- Structural invariant over `segments` and `objects` spans starting at `minSeg`. -/
structure RepackValid {policy : StoragePolicy} (minSeg : SegmentId) (acc : RepackAcc policy) : Prop where
  minSeg_pos  : 1 ≤ minSeg.val.toNat
  active_ge   : minSeg.val.toNat ≤ acc.activeSeg.val.toNat
  active_lt   : acc.activeSeg.val.toNat < acc.nextSegId.val.toNat
  active_mem  : ∃ seg, acc.segments[acc.activeSeg]? = some seg
  segments_wf : ∀ (sid : SegmentId) (seg : SegmentMeta policy.segmentSize),
    acc.segments[sid]? = some seg →
      seg.id = sid ∧ minSeg.val.toNat ≤ sid.val.toNat ∧
      sid.val.toNat < acc.nextSegId.val.toNat ∧ seg.used ≤ policy.segmentSize ∧
      (∀ loc ∈ seg.live.toList, loc.segment = sid ∧ loc.offset + loc.length ≤ seg.used) ∧
      seg.live.toList.Pairwise (fun a b => a.offset + a.length ≤ b.offset)
  objects_wf  : ∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
    acc.objects[k]? = some bm →
      bm.key = k ∧
      ∃ seg, acc.segments[bm.location.segment]? = some seg ∧ bm.location ∈ seg.live.toList
  unique_locs : ∀ (k₁ k₂ : ObjectKey) (m₁ m₂ : BucketEntryMeta policy.segmentSize),
    acc.objects[k₁]? = some m₁ → acc.objects[k₂]? = some m₂ → m₁.location = m₂.location → k₁ = k₂

/-- Full storage invariant on `BucketState policy`. -/
structure Invariant {policy : StoragePolicy} (b : BucketState policy) : Prop where
  active_ge    : 1 ≤ b.activeSeg.val.toNat
  active_lt    : b.activeSeg.val.toNat < b.nextSegId.val.toNat
  active_mem   : ∃ seg, b.segments[b.activeSeg]? = some seg
  segments_wf  : ∀ (sid : SegmentId) (seg : SegmentMeta policy.segmentSize),
    b.segments[sid]? = some seg →
      seg.id = sid ∧ 1 ≤ sid.val.toNat ∧ sid.val.toNat < b.nextSegId.val.toNat ∧
      seg.used ≤ policy.segmentSize ∧
      (∀ loc ∈ seg.live.toList, loc.segment = sid ∧ loc.offset + loc.length ≤ seg.used) ∧
      seg.live.toList.Pairwise (fun a b => a.offset + a.length ≤ b.offset)
  objects_wf   : ∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
    b.objects[k]? = some bm →
      bm.key = k ∧
      bm.byteSize ≤ policy.maxImageBytes ∧
      bm.location.length = StoragePolicy.segmentEntryOverhead + bm.byteSize ∧
      (∃ bs, b.blobs[k]? = some bs ∧ bs.size = bm.byteSize ∧ bm.crc32 = crc32 bs) ∧
      (∃ seg, b.segments[bm.location.segment]? = some seg ∧ bm.location ∈ seg.live.toList)
  unique_locs  : ∀ (k₁ k₂ : ObjectKey) (m₁ m₂ : BucketEntryMeta policy.segmentSize),
    b.objects[k₁]? = some m₁ → b.objects[k₂]? = some m₂ → m₁.location = m₂.location → k₁ = k₂
  blobs_wf     : ∀ (k : ObjectKey), k ∈ b.blobs ↔ k ∈ b.objects
  byDigest_wf  : ∀ (d : Sha256Digest) (ks : Array ObjectKey),
    b.byDigest[d]? = some ks →
      (∀ x ∈ ks.toList, x.digest = d ∧ x ∈ b.objects) ∧ ks.toList.Nodup
  byDigest_cov : ∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
    b.objects[k]? = some bm →
      ∃ ks, b.byDigest[k.digest]? = some ks ∧ k ∈ ks.toList
  unique_bytes : ∀ (k₁ k₂ : ObjectKey) (m₁ m₂ : BucketEntryMeta policy.segmentSize)
      (bs₁ bs₂ : ByteArray),
    b.objects[k₁]? = some m₁ → b.objects[k₂]? = some m₂ →
    b.blobs[k₁]? = some bs₁ → b.blobs[k₂]? = some bs₂ →
    k₁.digest = k₂.digest → m₁.mime = m₂.mime → bs₁ = bs₂ → k₁ = k₂

/-- Empty bucket initialized with segment `1` open and `nextSegId = 2`. -/
def empty (policy : StoragePolicy := {}) : BucketState policy where
  objects   := ∅
  byDigest  := ∅
  segments  := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
    ⟨1⟩ ⟨⟨1⟩, 0, Nat.zero_le _, #[]⟩
  activeSeg := ⟨1⟩
  nextSegId := ⟨2⟩
  blobs     := ∅

instance {policy : StoragePolicy} : Inhabited (BucketState policy) := ⟨empty policy⟩

/-- Reads object bytes by key. -/
def getObject {policy : StoragePolicy} (b : BucketState policy) (k : ObjectKey) : Option ByteArray :=
  b.blobs[k]?

/-- Reads object metadata by key. -/
def getMeta {policy : StoragePolicy} (b : BucketState policy) (k : ObjectKey) :
    Option (BucketEntryMeta policy.segmentSize) :=
  b.objects[k]?

private def findMatchingKey {segmentSize : Nat}
    (blobs : Std.ExtTreeMap ObjectKey ByteArray)
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta segmentSize))
    (mime : MimeType) (bytes : ByteArray) : List ObjectKey → Option ObjectKey
  | [] => none
  | k :: rest =>
    match blobs[k]?, objects[k]? with
    | some existingBytes, some bm =>
      if existingBytes == bytes && bm.mime == mime then some k
      else findMatchingKey blobs objects mime bytes rest
    | _, _ => findMatchingKey blobs objects mime bytes rest

private def nextCollisionTag (candidates : Array ObjectKey) : Except CoreError CollisionTag :=
  let nxt := candidates.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0
  if _h : nxt < 2 ^ 64 then
    .ok ⟨UInt64.ofNat nxt⟩
  else
    .error (.invariantViolated "CollisionTag overflow")

/-- Allocates a bounded segment location sequentially, rolling over to a fresh segment when full. -/
def allocLocation (policy : StoragePolicy) (len : Nat) (hPos : 0 < len)
    (hFits : len ≤ policy.segmentSize)
    (segments : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize))
    (activeSeg nextSegId : SegmentId) :
    Except CoreError (ObjectLocation policy.segmentSize ×
      Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize) × SegmentId × SegmentId) :=
  match segments[activeSeg]? with
  | some seg =>
    if hSpace : seg.used + len ≤ policy.segmentSize then
      let loc : ObjectLocation policy.segmentSize := ⟨seg.id, seg.used, len, hPos, hSpace⟩
      let seg' : SegmentMeta policy.segmentSize := ⟨seg.id, seg.used + len, hSpace, seg.live.push loc⟩
      .ok (loc, segments.insert seg.id seg', activeSeg, nextSegId)
    else
      if nextSegId.val.toNat + 1 ≥ 2 ^ 64 then
        .error (.invariantViolated "SegmentId overflow")
      else
        have hZeroSpace : 0 + len ≤ policy.segmentSize := by simpa using hFits
        let newSid := nextSegId
        let loc : ObjectLocation policy.segmentSize := ⟨newSid, 0, len, hPos, hZeroSpace⟩
        let seg' : SegmentMeta policy.segmentSize := ⟨newSid, len, hFits, #[loc]⟩
        .ok (loc, segments.insert newSid seg', newSid, ⟨newSid.val + 1⟩)
  | none =>
    if nextSegId.val.toNat + 1 ≥ 2 ^ 64 then
      .error (.invariantViolated "SegmentId overflow")
    else
      have hZeroSpace : 0 + len ≤ policy.segmentSize := by simpa using hFits
      let newSid := nextSegId
      let loc : ObjectLocation policy.segmentSize := ⟨newSid, 0, len, hPos, hZeroSpace⟩
      let seg' : SegmentMeta policy.segmentSize := ⟨newSid, len, hFits, #[loc]⟩
      .ok (loc, segments.insert newSid seg', newSid, ⟨newSid.val + 1⟩)

/-- Collision-safe CAS put under an explicit digest (used both by SHA-256 put and collision tests). -/
def putObjectWithHash {policy : StoragePolicy} (b : BucketState policy)
    (digest : Sha256Digest) (mime : MimeType) (bytes : ByteArray) :
    Except CoreError (ObjectKey × BucketState policy) :=
  if hImg : bytes.size ≤ policy.maxImageBytes then
    let candidates := (b.byDigest[digest]?).getD #[]
    match findMatchingKey b.blobs b.objects mime bytes candidates.toList with
    | some existingKey => .ok (existingKey, b)
    | none =>
      match nextCollisionTag candidates with
      | .error e => .error e
      | .ok tag =>
        let len := StoragePolicy.segmentEntryOverhead + bytes.size
        have hPos : 0 < len := by
          dsimp only [len]
          unfold StoragePolicy.segmentEntryOverhead
          omega
        have hFits : len ≤ policy.segmentSize := by
          have h1 := StoragePolicy.segmentEntryOverhead_le_reserve
          have h2 := policy.imageFitsSegment
          omega
        match allocLocation policy len hPos hFits b.segments b.activeSeg b.nextSegId with
        | .error e => .error e
        | .ok (loc, segments', activeSeg', nextSegId') =>
          let key : ObjectKey := ⟨digest, tag⟩
          let bm : BucketEntryMeta policy.segmentSize :=
            { key := key
              location := loc
              mime := mime
              crc32 := crc32 bytes
              byteSize := bytes.size
              refCount := 0 }
          let nextState : BucketState policy :=
            { objects := b.objects.insert key bm
              byDigest := b.byDigest.insert digest (candidates.push key)
              segments := segments'
              activeSeg := activeSeg'
              nextSegId := nextSegId'
              blobs := b.blobs.insert key bytes }
          .ok (key, nextState)
  else
    .error .imageTooLarge

/-- Hashes `bytes` with pure-Lean SHA-256 and delegates to `putObjectWithHash`. -/
def putObject {policy : StoragePolicy} (b : BucketState policy)
    (mime : MimeType) (bytes : ByteArray) :
    Except CoreError (ObjectKey × BucketState policy) :=
  b.putObjectWithHash (sha256 bytes) mime bytes

/-- Increments the reference count of an existing object. -/
def incRef {policy : StoragePolicy} (b : BucketState policy) (k : ObjectKey) :
    Except CoreError (BucketState policy) :=
  match b.objects[k]? with
  | none => .error (.objectNotFound k)
  | some bm =>
    .ok { b with objects := b.objects.insert k { bm with refCount := bm.refCount + 1 } }

/-- Decrements the reference count of an existing object (failing on underflow). -/
def decRef {policy : StoragePolicy} (b : BucketState policy) (k : ObjectKey) :
    Except CoreError (BucketState policy) :=
  match b.objects[k]? with
  | none => .error (.objectNotFound k)
  | some bm =>
    if bm.refCount == 0 then
      .error (.invariantViolated "refCount underflow on decRef")
    else
      .ok { b with objects := b.objects.insert k { bm with refCount := bm.refCount - 1 } }

private def isLiveKey {policy : StoragePolicy} (b : BucketState policy) (k : ObjectKey) : Bool :=
  match b.objects[k]? with
  | some bm => bm.refCount > 0
  | none => false

private def locInObjects {segmentSize : Nat}
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta segmentSize))
    (loc : ObjectLocation segmentSize) : Bool :=
  objects.foldl (fun acc _ bm => acc || decide (bm.location = loc)) false

/-- Garbage collects all `refCount = 0` objects without mutating live objects. -/
def gcStep {policy : StoragePolicy} (b : BucketState policy) : BucketState policy :=
  let objects' := b.objects.filter (fun _ bm => bm.refCount > 0)
  let blobs' := b.blobs.filter (fun k _ => isLiveKey b k)
  let byDigest' := b.byDigest.filterMap fun _ ks =>
    let kept := ks.filter (isLiveKey b)
    if kept.isEmpty then none else some kept
  let segments' := b.segments.map fun _ seg =>
    { seg with live := seg.live.filter (locInObjects objects') }
  { b with
    objects := objects'
    blobs := blobs'
    byDigest := byDigest'
    segments := segments' }

private def repackEntry {policy : StoragePolicy}
    (acc : RepackAcc policy) (entry : ObjectKey × BucketEntryMeta policy.segmentSize) :
    Except CoreError (RepackAcc policy) :=
  let (k, bm) := entry
  have hPos : 0 < bm.location.length := bm.location.nonEmpty
  have hFits : bm.location.length ≤ policy.segmentSize := by
    have := bm.location.validBounds
    omega
  match allocLocation policy bm.location.length hPos hFits acc.segments acc.activeSeg acc.nextSegId with
  | .error e => .error e
  | .ok (loc, segments', activeSeg', nextSegId') =>
    let bm' : BucketEntryMeta policy.segmentSize := { bm with location := loc }
    .ok
      { objects := acc.objects.insert k bm'
        segments := segments'
        activeSeg := activeSeg'
        nextSegId := nextSegId' }

/-- Rewrites all retained objects into fresh tightly packed segments starting at `b.nextSegId`. -/
def compactBucket {policy : StoragePolicy} (b : BucketState policy) :
    Except CoreError (BucketState policy) :=
  if hOv : b.nextSegId.val.toNat + 1 ≥ 2 ^ 64 then
    .error (.invariantViolated "SegmentId overflow on compactBucket")
  else
    let firstSeg : SegmentId := b.nextSegId
    let initAcc : RepackAcc policy :=
      { objects := ∅
        segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
          firstSeg ⟨firstSeg, 0, Nat.zero_le _, #[]⟩
        activeSeg := firstSeg
        nextSegId := ⟨firstSeg.val + 1⟩ }
    match b.objects.toList.foldlM (m := Except CoreError) repackEntry initAcc with
    | .error e => .error e
    | .ok fin =>
      .ok
        { objects := fin.objects
          byDigest := b.byDigest
          segments := fin.segments
          activeSeg := fin.activeSeg
          nextSegId := fin.nextSegId
          blobs := b.blobs }

end BucketState

abbrev BucketInvariant {policy : StoragePolicy} (b : BucketState policy) : Prop := BucketState.Invariant b

namespace BucketState

private theorem uint64_succ_toNat {x : UInt64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  exact Nat.mod_eq_of_lt h

private theorem compare_eq_iff_eq {α : Type} [Ord α] [Std.LawfulEqOrd α] {a b : α} :
    compare a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqOrd.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self (cmp := compare)⟩

private theorem repackValid_of_invariant {policy : StoragePolicy} {b : BucketState policy}
    (hInv : Invariant b) :
    RepackValid ⟨1⟩ ⟨b.objects, b.segments, b.activeSeg, b.nextSegId⟩ where
  minSeg_pos := by decide
  active_ge := hInv.active_ge
  active_lt := hInv.active_lt
  active_mem := hInv.active_mem
  segments_wf := hInv.segments_wf
  objects_wf := fun k m hk =>
    have h := hInv.objects_wf k m hk
    ⟨h.1, h.2.2.2.2⟩
  unique_locs := hInv.unique_locs

private theorem locInObjects_iff {segmentSize : Nat}
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta segmentSize))
    (loc : ObjectLocation segmentSize) :
    locInObjects objects loc = true ↔
      ∃ (k : ObjectKey) (bm : BucketEntryMeta segmentSize),
        objects[k]? = some bm ∧ bm.location = loc := by
  unfold locInObjects
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hfold : ∀ (xs : List (ObjectKey × BucketEntryMeta segmentSize)) (init : Bool),
      xs.foldl (fun acc kv => acc || decide (kv.2.location = loc)) init = true ↔
        init = true ∨ ∃ kv ∈ xs, kv.2.location = loc := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons kv rest ih =>
      intro init
      dsimp only [List.foldl]
      rw [ih]
      cases init <;> simp [decide_eq_true_eq]
  rw [hfold]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨⟨k, m⟩, hmem, hloc⟩
    exact ⟨k, m, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem, hloc⟩
  · rintro ⟨k, m, hget, hloc⟩
    exact ⟨(k, m), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hget, hloc⟩

private theorem foldl_max_tag_ge (xs : List ObjectKey) (init : Nat) :
    (∀ k ∈ xs, k.tag.val.toNat < xs.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) init) ∧
    init ≤ xs.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) init := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    dsimp only [List.foldl]
    have hx := ih (max init (x.tag.val.toNat + 1))
    constructor
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hkTail
      · have hle : max init (k.tag.val.toNat + 1) ≤ _ := hx.2
        omega
      · exact hx.1 k hkTail
    · have hle := hx.2
      omega

private theorem nextCollisionTag_fresh {candidates : Array ObjectKey} {tag : CollisionTag}
    (hOk : nextCollisionTag candidates = .ok tag) :
    ∀ k ∈ candidates.toList, k.tag ≠ tag := by
  unfold nextCollisionTag at hOk
  dsimp only at hOk
  split at hOk
  · next hlt =>
    injection hOk with hTag
    subst hTag
    intro k hk heq
    have hge := (foldl_max_tag_ge candidates.toList 0).1 k hk
    have hfold : candidates.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0 =
        candidates.toList.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0 := by
      rw [← Array.foldl_toList]
    rw [hfold] at hlt heq
    have hVal : (UInt64.ofNat (candidates.toList.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0)).toNat =
        candidates.toList.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0 := by
      change (BitVec.ofNat 64 _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hEqNat : k.tag.val.toNat =
        candidates.toList.foldl (fun acc k => max acc (k.tag.val.toNat + 1)) 0 := by
      rw [← hVal]
      exact congrArg (fun t : CollisionTag => t.val.toNat) heq
    omega
  · simp at hOk

private theorem findMatchingKey_spec {segmentSize : Nat}
    (blobs : Std.ExtTreeMap ObjectKey ByteArray)
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta segmentSize))
    (mime : MimeType) (bytes : ByteArray) :
    ∀ (ks : List ObjectKey) (k : ObjectKey),
      findMatchingKey blobs objects mime bytes ks = some k →
        k ∈ ks ∧ blobs[k]? = some bytes ∧
        ∃ (m : BucketEntryMeta segmentSize), objects[k]? = some m ∧ m.mime = mime := by
  intro ks
  induction ks with
  | nil => intro k h; simp [findMatchingKey] at h
  | cons x rest ih =>
    intro k h
    unfold findMatchingKey at h
    cases hb : blobs[x]? with
    | none =>
      rw [hb] at h
      have hrec := ih k h
      exact ⟨List.mem_cons_of_mem x hrec.1, hrec.2⟩
    | some eb =>
      rw [hb] at h
      cases ho : objects[x]? with
      | none =>
        rw [ho] at h
        have hrec := ih k h
        exact ⟨List.mem_cons_of_mem x hrec.1, hrec.2⟩
      | some m =>
        rw [ho] at h
        dsimp only at h
        split at h
        · next hEq =>
          injection h with hxk
          subst hxk
          simp only [Bool.and_eq_true, beq_iff_eq] at hEq
          have hMimeEq : m.mime = mime := by
            have hB : (m.mime == mime) = true := hEq.2
            revert hB
            cases m.mime <;> cases mime <;> decide
          exact ⟨List.mem_cons_self, by rw [hb, hEq.1], m, ho, hMimeEq⟩
        · have hrec := ih k h
          exact ⟨List.mem_cons_of_mem x hrec.1, hrec.2⟩

private theorem findMatchingKey_complete {segmentSize : Nat}
    (blobs : Std.ExtTreeMap ObjectKey ByteArray)
    (objects : Std.ExtTreeMap ObjectKey (BucketEntryMeta segmentSize))
    (mime : MimeType) (bytes : ByteArray) :
    ∀ (ks : List ObjectKey) (target : ObjectKey) (m : BucketEntryMeta segmentSize),
      target ∈ ks → blobs[target]? = some bytes → objects[target]? = some m → m.mime = mime →
      ∃ found, findMatchingKey blobs objects mime bytes ks = some found := by
  intro ks
  induction ks with
  | nil => intro _ _ h; cases h
  | cons x rest ih =>
    intro target m hmem hb ho hm
    unfold findMatchingKey
    rcases List.mem_cons.mp hmem with rfl | htail
    · rw [hb, ho]
      dsimp only
      have hme : (mime == mime) = true := by cases mime <;> decide
      simp [hm, hme]
    · cases hbx : blobs[x]?
      · exact ih target m htail hb ho hm
      · cases hox : objects[x]?
        · exact ih target m htail hb ho hm
        · next ebx mx =>
          dsimp only
          by_cases hmatch : (ebx == bytes && mx.mime == mime) = true
          · exact ⟨x, by simp [hmatch]⟩
          · simp only [hmatch, Bool.false_eq_true, ↓reduceIte]
            exact ih target m htail hb ho hm

private theorem allocLocation_length {policy : StoragePolicy} {len : Nat} {hPos : 0 < len}
    {hFits : len ≤ policy.segmentSize}
    {segments segments' : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)}
    {activeSeg nextSegId activeSeg' nextSegId' : SegmentId}
    {loc : ObjectLocation policy.segmentSize}
    (hOk : allocLocation policy len hPos hFits segments activeSeg nextSegId =
      .ok (loc, segments', activeSeg', nextSegId')) :
    loc.length = len := by
  unfold allocLocation at hOk
  split at hOk
  · split at hOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, _⟩; rfl
    · split at hOk
      · simp at hOk
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
        rcases hOk with ⟨rfl, _⟩; rfl
  · split at hOk
    · simp at hOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, _⟩; rfl

/-- Preserves `RepackValid` across `allocLocation` and fresh key insertion. -/
private theorem alloc_insert_preserves_valid {policy : StoragePolicy}
    {minSeg : SegmentId} {acc : RepackAcc policy}
    (hVal : RepackValid minSeg acc)
    (key : ObjectKey) (_hNotMem : key ∉ acc.objects)
    (len : Nat) (hPos : 0 < len) (hFits : len ≤ policy.segmentSize)
    (loc : ObjectLocation policy.segmentSize)
    (segments' : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize))
    (activeSeg' nextSegId' : SegmentId)
    (hAlloc : allocLocation policy len hPos hFits acc.segments acc.activeSeg acc.nextSegId =
      .ok (loc, segments', activeSeg', nextSegId'))
    (mime : MimeType) (crc : UInt32) (byteSize refCount : Nat) :
    let bm' : BucketEntryMeta policy.segmentSize := ⟨key, loc, mime, crc, byteSize, refCount⟩
    let acc' : RepackAcc policy := ⟨acc.objects.insert key bm', segments', activeSeg', nextSegId'⟩
    RepackValid minSeg acc' ∧
    acc.nextSegId.val.toNat ≤ nextSegId'.val.toNat ∧
    (∀ (sid : SegmentId) (seg : SegmentMeta policy.segmentSize), acc.segments[sid]? = some seg →
      ∃ (seg' : SegmentMeta policy.segmentSize), segments'[sid]? = some seg' ∧
        ∀ l ∈ seg.live.toList, l ∈ seg'.live.toList) ∧
    (∀ (kOld : ObjectKey) (mOld : BucketEntryMeta policy.segmentSize),
      acc.objects[kOld]? = some mOld → loc ≠ mOld.location) := by
  unfold allocLocation at hAlloc
  cases hAct : acc.segments[acc.activeSeg]? with
  | none =>
    exfalso
    rcases hVal.active_mem with ⟨s, hs⟩
    rw [hAct] at hs
    simp at hs
  | some seg =>
    rw [hAct] at hAlloc
    have hSegWf := hVal.segments_wf acc.activeSeg seg hAct
    by_cases hSpace : seg.used + len ≤ policy.segmentSize
    · simp only [hSpace, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at hAlloc
      rcases hAlloc with ⟨rfl, rfl, rfl, rfl⟩
      have hDisjOld : ∀ l ∈ seg.live.toList,
          l ≠ (⟨seg.id, seg.used, len, hPos, hSpace⟩ : ObjectLocation policy.segmentSize) := by
        intro l hl heq
        have hlBound := (hSegWf.2.2.2.2.1 l hl).2
        rw [heq] at hlBound
        dsimp only at hlBound
        omega
      have hLocDisj : ∀ (kOld : ObjectKey) (mOld : BucketEntryMeta policy.segmentSize),
          acc.objects[kOld]? = some mOld →
          (⟨seg.id, seg.used, len, hPos, hSpace⟩ : ObjectLocation policy.segmentSize) ≠ mOld.location := by
        intro kOld mOld hm heq
        rcases (hVal.objects_wf kOld mOld hm).2 with ⟨sOld, hsOld, hlMem⟩
        have hsEq : mOld.location.segment = seg.id := by rw [← heq]
        rw [hsEq, hSegWf.1] at hsOld
        rw [hAct] at hsOld
        injection hsOld with hSEq
        subst hSEq
        exact hDisjOld mOld.location hlMem heq.symm
      refine ⟨?_, Nat.le_refl _, ?_, hLocDisj⟩
      · refine ⟨hVal.minSeg_pos, hVal.active_ge, hVal.active_lt,
          ⟨⟨seg.id, seg.used + len, hSpace, seg.live.push ⟨seg.id, seg.used, len, hPos, hSpace⟩⟩,
            by rw [hSegWf.1]; simp⟩, ?_, ?_, ?_⟩
        · intro sid segCheck hCheck
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hCheck
          split at hCheck
          · next hEq =>
            injection hCheck with hSegEq
            subst hSegEq
            subst hEq
            refine ⟨rfl, ?_, ?_, hSpace, ?_, ?_⟩
            · rw [hSegWf.1]; exact hSegWf.2.1
            · rw [hSegWf.1]; exact hSegWf.2.2.1
            · intro locCheck hMem
              rw [Array.toList_push] at hMem
              rcases List.mem_append.mp hMem with hOldMem | hNewMem
              · have hB := hSegWf.2.2.2.2.1 locCheck hOldMem
                refine ⟨hSegWf.1 ▸ hB.1, Nat.le_trans hB.2 (Nat.le_add_right _ _)⟩
              · simp only [List.mem_singleton] at hNewMem
                subst hNewMem
                exact ⟨rfl, Nat.le_refl _⟩
            · rw [Array.toList_push, List.pairwise_append]
              refine ⟨hSegWf.2.2.2.2.2, List.pairwise_singleton _ _, ?_⟩
              intro a ha b hb
              simp only [List.mem_singleton] at hb
              subst hb
              exact (hSegWf.2.2.2.2.1 a ha).2
          · exact hVal.segments_wf sid segCheck hCheck
        · intro k m hk
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hk
          split at hk
          · next hEq =>
            injection hk with hMeta
            subst hMeta; subst hEq
            refine ⟨rfl, ⟨⟨seg.id, seg.used + len, hSpace,
                seg.live.push ⟨seg.id, seg.used, len, hPos, hSpace⟩⟩, ?_, ?_⟩⟩
            · simp
            · rw [Array.toList_push]; exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))
          · have hkOld := hVal.objects_wf k m hk
            rcases hkOld.2 with ⟨sOld, hsOld, hlMem⟩
            refine ⟨hkOld.1, ?_⟩
            by_cases hSid : seg.id = m.location.segment
            · rw [← hSid] at hsOld ⊢
              rw [hSegWf.1] at hsOld ⊢
              rw [hAct] at hsOld
              injection hsOld with hSEq
              subst hSEq
              refine ⟨⟨seg.id, seg.used + len, hSpace,
                  seg.live.push ⟨seg.id, seg.used, len, hPos, hSpace⟩⟩,
                by rw [hSegWf.1]; simp, ?_⟩
              rw [Array.toList_push]
              exact List.mem_append.mpr (.inl hlMem)
            · refine ⟨sOld, ?_, hlMem⟩
              simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hSid, ↓reduceIte]
              exact hsOld
        · intro k₁ k₂ m₁ m₂ hm₁ hm₂ hLocEq
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
          split at hm₁ <;> split at hm₂
          · next h₁ h₂ => exact h₁.symm.trans h₂
          · next h₁ _ =>
            injection hm₁ with hm₁Eq
            subst hm₁Eq; subst h₁
            exfalso
            exact hLocDisj k₂ m₂ hm₂ hLocEq
          · next _ h₂ =>
            injection hm₂ with hm₂Eq
            subst hm₂Eq; subst h₂
            exfalso
            exact hLocDisj k₁ m₁ hm₁ hLocEq.symm
          · exact hVal.unique_locs k₁ k₂ m₁ m₂ hm₁ hm₂ hLocEq
      · intro sid seg0 hseg0
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq]
        split
        · next hEq =>
          subst hEq
          rw [hSegWf.1] at hseg0
          rw [hAct] at hseg0
          injection hseg0 with hSEq
          subst hSEq
          refine ⟨_, rfl, ?_⟩
          intro l hl
          rw [Array.toList_push]
          exact List.mem_append.mpr (.inl hl)
        · exact ⟨seg0, hseg0, fun _ h => h⟩
    · simp only [hSpace, ↓reduceDIte] at hAlloc
      split at hAlloc
      · simp at hAlloc
      · next hNoOv =>
        simp only [Nat.not_le] at hNoOv
        simp only [Except.ok.injEq, Prod.mk.injEq] at hAlloc
        rcases hAlloc with ⟨rfl, rfl, rfl, rfl⟩
        have hSucc : (acc.nextSegId.val + 1).toNat = acc.nextSegId.val.toNat + 1 :=
          uint64_succ_toNat hNoOv
        have hZeroSpace : 0 + len ≤ policy.segmentSize := by simpa using hFits
        have hNotSeg : acc.segments[acc.nextSegId]? = none := by
          cases hCheck : acc.segments[acc.nextSegId]? with
          | none => rfl
          | some s =>
            have hlt := (hVal.segments_wf acc.nextSegId s hCheck).2.2.1
            exact absurd hlt (Nat.lt_irrefl _)
        have hLocDisj : ∀ (kOld : ObjectKey) (mOld : BucketEntryMeta policy.segmentSize),
            acc.objects[kOld]? = some mOld →
            (⟨acc.nextSegId, 0, len, hPos, hZeroSpace⟩ : ObjectLocation policy.segmentSize) ≠ mOld.location := by
          intro kOld mOld hm heq
          rcases (hVal.objects_wf kOld mOld hm).2 with ⟨sOld, hsOld, _⟩
          have hSegEq : mOld.location.segment = acc.nextSegId := by rw [← heq]
          rw [hSegEq, hNotSeg] at hsOld
          simp at hsOld
        refine ⟨?_, ?_, ?_, hLocDisj⟩
        · refine ⟨hVal.minSeg_pos, ?_, ?_,
            ⟨⟨acc.nextSegId, len, hFits, #[⟨acc.nextSegId, 0, len, hPos, hZeroSpace⟩]⟩, ?_⟩, ?_, ?_, ?_⟩
          · exact Nat.le_trans hVal.active_ge (Nat.le_of_lt hVal.active_lt)
          · dsimp only; rw [hSucc]; omega
          · simp
          · intro sid segCheck hCheck
            dsimp only at hCheck ⊢
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hCheck
            split at hCheck
            · next hEq =>
              injection hCheck with hSEq
              subst hSEq; subst hEq
              refine ⟨rfl, Nat.le_trans hVal.active_ge (Nat.le_of_lt hVal.active_lt), ?_, hFits, ?_, ?_⟩
              · rw [hSucc]; omega
              · intro l hl
                simp at hl
                subst hl
                exact ⟨rfl, by simp⟩
              · simp
            · have hsOld := hVal.segments_wf sid segCheck hCheck
              refine ⟨hsOld.1, hsOld.2.1, ?_, hsOld.2.2.2.1, hsOld.2.2.2.2⟩
              rw [hSucc]
              exact Nat.lt_succ_of_lt hsOld.2.2.1
          · intro k m hk
            dsimp only at hk
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hk
            split at hk
            · next hEq =>
              injection hk with hMeta
              subst hMeta; subst hEq
              refine ⟨rfl, ⟨⟨acc.nextSegId, len, hFits, #[⟨acc.nextSegId, 0, len, hPos, hZeroSpace⟩]⟩,
                by simp, by simp⟩⟩
            · have hkOld := hVal.objects_wf k m hk
              rcases hkOld.2 with ⟨sOld, hsOld, hlMem⟩
              have hNe : acc.nextSegId ≠ m.location.segment := by
                intro hEq
                rw [← hEq, hNotSeg] at hsOld
                simp at hsOld
              refine ⟨hkOld.1, sOld, ?_, hlMem⟩
              simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
              exact hsOld
          · intro k₁ k₂ m₁ m₂ hm₁ hm₂ hLocEq
            dsimp only at hm₁ hm₂
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
            split at hm₁ <;> split at hm₂
            · next h₁ h₂ => exact h₁.symm.trans h₂
            · next h₁ _ =>
              injection hm₁ with hMeta
              subst hMeta; subst h₁
              exfalso; exact hLocDisj k₂ m₂ hm₂ hLocEq
            · next _ h₂ =>
              injection hm₂ with hMeta
              subst hMeta; subst h₂
              exfalso; exact hLocDisj k₁ m₁ hm₁ hLocEq.symm
            · exact hVal.unique_locs k₁ k₂ m₁ m₂ hm₁ hm₂ hLocEq
        · rw [hSucc]; omega
        · intro sid seg0 hseg0
          have hNe : acc.nextSegId ≠ sid := by
            intro hEq
            subst hEq
            rw [hNotSeg] at hseg0
            simp at hseg0
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
          exact ⟨seg0, hseg0, fun _ h => h⟩

theorem empty_invariant (policy : StoragePolicy) : Invariant (empty policy) where
  active_ge := by change 1 ≤ 1; exact Nat.le_refl _
  active_lt := by change 1 < 2; exact Nat.lt_succ_self 1
  active_mem := ⟨⟨⟨1⟩, 0, Nat.zero_le _, #[]⟩, by simp [empty]⟩
  segments_wf := by
    intro sid seg h
    simp only [empty, Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at h
    split at h
    · next hEq =>
      injection h with hS
      subst hS; subst hEq
      refine ⟨rfl, Nat.le_refl _, Nat.lt_succ_self _, Nat.zero_le _, ?_, ?_⟩
      · intro l hl; simp at hl
      · simp
    · simp at h
  objects_wf := by intro k m h; simp [empty] at h
  unique_locs := by intro k₁ k₂ m₁ m₂ h₁; simp [empty] at h₁
  blobs_wf := by intro k; simp [empty]
  byDigest_wf := by intro d ks h; simp [empty] at h
  byDigest_cov := by intro k m h; simp [empty] at h
  unique_bytes := by intro k₁ k₂ m₁ m₂ bs₁ bs₂ h₁; simp [empty] at h₁

theorem putObjectWithHash_preserves_invariant {policy : StoragePolicy}
    {b b' : BucketState policy} {digest : Sha256Digest} {mime : MimeType}
    {bytes : ByteArray} {key : ObjectKey}
    (hInv : Invariant b)
    (hOk : b.putObjectWithHash digest mime bytes = .ok (key, b')) :
    Invariant b' := by
  unfold putObjectWithHash at hOk
  by_cases hImg : bytes.size ≤ policy.maxImageBytes
  · simp only [hImg, ↓reduceDIte] at hOk
    cases hFind : findMatchingKey b.blobs b.objects mime bytes ((b.byDigest[digest]?).getD #[]).toList with
    | some existingKey =>
      rw [hFind] at hOk
      dsimp only at hOk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, rfl⟩
      exact hInv
    | none =>
      rw [hFind] at hOk
      dsimp only at hOk
      cases hTag : nextCollisionTag ((b.byDigest[digest]?).getD #[]) with
      | error e => rw [hTag] at hOk; simp at hOk
      | ok tag =>
        rw [hTag] at hOk
        dsimp only at hOk
        cases hAlloc : allocLocation policy (StoragePolicy.segmentEntryOverhead + bytes.size)
            (by unfold StoragePolicy.segmentEntryOverhead; omega)
            (by have := StoragePolicy.segmentEntryOverhead_le_reserve; have := policy.imageFitsSegment; omega)
            b.segments b.activeSeg b.nextSegId with
        | error e => rw [hAlloc] at hOk; simp at hOk
        | ok allocRes =>
          rw [hAlloc] at hOk
          dsimp only at hOk
          rcases allocRes with ⟨loc, segments', activeSeg', nextSegId'⟩
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          let cand := (b.byDigest[digest]?).getD #[]
          have hFreshTag : ∀ x ∈ cand.toList, x.tag ≠ tag := nextCollisionTag_fresh hTag
          have hNewNotMem : (⟨digest, tag⟩ : ObjectKey) ∉ b.objects := by
            intro hmem
            rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
            cases hObj : b.objects[(⟨digest, tag⟩ : ObjectKey)]? with
            | none => rw [hObj] at hmem; simp at hmem
            | some m =>
              rcases hInv.byDigest_cov ⟨digest, tag⟩ m hObj with ⟨ks, hks, hInKs⟩
              have hCandEq : cand = ks := by simp [cand, hks]
              rw [← hCandEq] at hInKs
              exact hFreshTag ⟨digest, tag⟩ hInKs rfl
          have hRepack := alloc_insert_preserves_valid (repackValid_of_invariant hInv)
            ⟨digest, tag⟩ hNewNotMem _ _ _ loc segments' activeSeg' nextSegId' hAlloc
            mime (crc32 bytes) bytes.size 0
          rcases hRepack with ⟨hVal', hNextLe, _, _⟩
          have hNotBlob : ⟨digest, tag⟩ ∉ b.blobs := fun h => hNewNotMem ((hInv.blobs_wf _).mp h)
          have hCandWf : (∀ x ∈ cand.toList, x.digest = digest ∧ x ∈ b.objects) ∧ cand.toList.Nodup := by
            cases hOldDig : b.byDigest[digest]? with
            | none => simp [cand, hOldDig]
            | some ks =>
              have hEqCand : cand = ks := by simp [cand, hOldDig]
              rw [hEqCand]
              exact hInv.byDigest_wf digest ks hOldDig
          have hNotInCand : ⟨digest, tag⟩ ∉ cand.toList := fun hm =>
            hFreshTag ⟨digest, tag⟩ hm rfl
          refine ⟨hVal'.active_ge, hVal'.active_lt, hVal'.active_mem, hVal'.segments_wf, ?_, hVal'.unique_locs, ?_, ?_, ?_, ?_⟩
          · intro k m hm
            have hmBase := hVal'.objects_wf k m hm
            dsimp only at hm
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm
            split at hm
            · next hEq =>
              injection hm with hMetaEq
              subst hMetaEq; subst hEq
              have hLocLen : loc.length = StoragePolicy.segmentEntryOverhead + bytes.size :=
                allocLocation_length hAlloc
              refine ⟨rfl, hImg, hLocLen, ⟨bytes, by simp, rfl, rfl⟩, hmBase.2⟩
            · next hNe =>
              have hmOld := hInv.objects_wf k m hm
              rcases hmOld.2.2.2.1 with ⟨bs, hbs, hbsSz, hcrc⟩
              refine ⟨hmOld.1, hmOld.2.1, hmOld.2.2.1, ?_, hmBase.2⟩
              refine ⟨bs, ?_, hbsSz, hcrc⟩
              simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
              exact hbs
          · intro k
            dsimp only
            simp only [Std.ExtTreeMap.mem_insert, compare_eq_iff_eq]
            rw [hInv.blobs_wf k]
          · intro d ks hks
            dsimp only at hks
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hks
            split at hks
            · next hd =>
              injection hks with hksEq
              subst hksEq; subst hd
              constructor
              · intro x hx
                rw [Array.toList_push] at hx
                rcases List.mem_append.mp hx with hxOld | hxNew
                · have hOld := hCandWf.1 x hxOld
                  refine ⟨hOld.1, ?_⟩
                  dsimp only
                  rw [Std.ExtTreeMap.mem_insert]
                  exact .inr hOld.2
                · simp only [List.mem_singleton] at hxNew
                  subst hxNew
                  refine ⟨rfl, ?_⟩
                  dsimp only
                  exact Std.ExtTreeMap.mem_insert_self
              · rw [Array.toList_push, List.nodup_append]
                refine ⟨hCandWf.2, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
                intro a ha b hb
                simp only [List.mem_singleton] at hb
                subst hb
                intro heq
                subst heq
                exact hNotInCand ha
            · have hOld := hInv.byDigest_wf d ks hks
              refine ⟨?_, hOld.2⟩
              intro x hx
              have hxOld := hOld.1 x hx
              refine ⟨hxOld.1, ?_⟩
              dsimp only
              rw [Std.ExtTreeMap.mem_insert]
              exact .inr hxOld.2
          · intro k m hm
            dsimp only at hm ⊢
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm
            split at hm
            · next hEq =>
              injection hm with hMetaEq
              subst hMetaEq; subst hEq
              refine ⟨cand.push ⟨digest, tag⟩, by simp [cand], ?_⟩
              rw [Array.toList_push]
              exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))
            · rcases hInv.byDigest_cov k m hm with ⟨ks, hks, hMem⟩
              by_cases hDig : digest = k.digest
              · subst hDig
                have hCandEq : cand = ks := by simp [cand, hks]
                refine ⟨cand.push (⟨k.digest, tag⟩ : ObjectKey), by simp [cand], ?_⟩
                rw [Array.toList_push, hCandEq]
                exact List.mem_append.mpr (.inl hMem)
              · refine ⟨ks, ?_, hMem⟩
                simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hDig, ↓reduceIte]
                exact hks
          · intro k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes
            dsimp only at hm₁ hm₂ hb₁ hb₂
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂ hb₁ hb₂
            by_cases h₁ : (⟨digest, tag⟩ : ObjectKey) = k₁ <;> by_cases h₂ : (⟨digest, tag⟩ : ObjectKey) = k₂
            · exact h₁.symm.trans h₂
            · exfalso
              simp only [h₁, ↓reduceIte, Option.some.injEq] at hm₁ hb₁
              subst hm₁; subst hb₁
              simp only [h₂, ↓reduceIte] at hm₂ hb₂
              have hDig₂ : digest = k₂.digest := (congrArg ObjectKey.digest h₁).trans hdEq
              rcases hInv.byDigest_cov k₂ m₂ hm₂ with ⟨ks, hks, hInKs⟩
              have hCandEq : cand = ks := by dsimp only [cand]; rw [hDig₂, hks]; rfl
              have hInCand : k₂ ∈ cand.toList := hCandEq ▸ hInKs
              have hb₂' : b.blobs[k₂]? = some bytes := by rw [hBytes, hb₂]
              have ⟨found, hFound⟩ := findMatchingKey_complete b.blobs b.objects mime bytes cand.toList
                k₂ m₂ hInCand hb₂' hm₂ hMime.symm
              rw [hFind] at hFound
              simp at hFound
            · exfalso
              simp only [h₁, ↓reduceIte] at hm₁ hb₁
              simp only [h₂, ↓reduceIte, Option.some.injEq] at hm₂ hb₂
              subst hm₂; subst hb₂
              have hDig₁ : digest = k₁.digest := (congrArg ObjectKey.digest h₂).trans hdEq.symm
              rcases hInv.byDigest_cov k₁ m₁ hm₁ with ⟨ks, hks, hInKs⟩
              have hCandEq : cand = ks := by dsimp only [cand]; rw [hDig₁, hks]; rfl
              have hInCand : k₁ ∈ cand.toList := hCandEq ▸ hInKs
              have hb₁' : b.blobs[k₁]? = some bytes := by rw [← hBytes, hb₁]
              have ⟨found, hFound⟩ := findMatchingKey_complete b.blobs b.objects mime bytes cand.toList
                k₁ m₁ hInCand hb₁' hm₁ hMime
              rw [hFind] at hFound
              simp at hFound
            · simp only [h₁, h₂, ↓reduceIte] at hm₁ hm₂ hb₁ hb₂
              exact hInv.unique_bytes k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes
  · simp [hImg] at hOk

theorem putObject_preserves_invariant {policy : StoragePolicy}
    {b b' : BucketState policy} {mime : MimeType} {bytes : ByteArray} {key : ObjectKey}
    (hInv : Invariant b)
    (hOk : b.putObject mime bytes = .ok (key, b')) :
    Invariant b' :=
  putObjectWithHash_preserves_invariant hInv hOk

theorem incRef_preserves_invariant {policy : StoragePolicy}
    {b b' : BucketState policy} {k : ObjectKey}
    (hInv : Invariant b) (hOk : b.incRef k = .ok b') :
    Invariant b' := by
  unfold incRef at hOk
  cases hk : b.objects[k]? with
  | none => rw [hk] at hOk; simp at hOk
  | some m0 =>
    rw [hk] at hOk
    simp only [Except.ok.injEq] at hOk
    subst hOk
    have hm0Wf := hInv.objects_wf k m0 hk
    refine ⟨hInv.active_ge, hInv.active_lt, hInv.active_mem, hInv.segments_wf, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x m hx
      dsimp only at hx
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hx
      split at hx
      · next hEq =>
        injection hx with hmEq
        subst hmEq; subst hEq
        exact ⟨hm0Wf.1, hm0Wf.2.1, hm0Wf.2.2.1, hm0Wf.2.2.2.1, hm0Wf.2.2.2.2⟩
      · exact hInv.objects_wf x m hx
    · intro k₁ k₂ m₁ m₂ hm₁ hm₂ hLoc
      dsimp only at hm₁ hm₂
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
      split at hm₁ <;> split at hm₂
      · next h₁ h₂ => exact h₁.symm.trans h₂
      · next h₁ _ =>
        injection hm₁ with hEq; subst hEq; subst h₁
        exact hInv.unique_locs k k₂ m0 m₂ hk hm₂ hLoc
      · next _ h₂ =>
        injection hm₂ with hEq; subst hEq; subst h₂
        exact hInv.unique_locs k₁ k m₁ m0 hm₁ hk hLoc
      · exact hInv.unique_locs k₁ k₂ m₁ m₂ hm₁ hm₂ hLoc
    · intro x
      dsimp only
      rw [hInv.blobs_wf x, Std.ExtTreeMap.mem_insert, compare_eq_iff_eq]
      constructor
      · exact .inr
      · rintro (rfl | hx)
        · rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hk]; rfl
        · exact hx
    · intro d ks hks
      rcases hInv.byDigest_wf d ks hks with ⟨hAll, hNodup⟩
      refine ⟨fun x hx => ⟨(hAll x hx).1, ?_⟩, hNodup⟩
      dsimp only; rw [Std.ExtTreeMap.mem_insert]; exact .inr (hAll x hx).2
    · intro x m hx
      dsimp only at hx
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hx
      split at hx
      · next hEq => subst hEq; exact hInv.byDigest_cov k m0 hk
      · exact hInv.byDigest_cov x m hx
    · intro k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes
      dsimp only at hm₁ hm₂ hb₁ hb₂
      simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
      by_cases h₁ : k = k₁ <;> by_cases h₂ : k = k₂
      · exact h₁.symm.trans h₂
      · simp only [h₁, ↓reduceIte, Option.some.injEq] at hm₁
        simp only [h₂, ↓reduceIte] at hm₂
        subst hm₁; subst h₁
        exact hInv.unique_bytes k k₂ m0 m₂ bs₁ bs₂ hk hm₂ hb₁ hb₂ hdEq hMime hBytes
      · simp only [h₁, ↓reduceIte] at hm₁
        simp only [h₂, ↓reduceIte, Option.some.injEq] at hm₂
        subst hm₂; subst h₂
        exact hInv.unique_bytes k₁ k m₁ m0 bs₁ bs₂ hm₁ hk hb₁ hb₂ hdEq hMime hBytes
      · simp only [h₁, ↓reduceIte] at hm₁
        simp only [h₂, ↓reduceIte] at hm₂
        exact hInv.unique_bytes k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes

theorem decRef_preserves_invariant {policy : StoragePolicy}
    {b b' : BucketState policy} {k : ObjectKey}
    (hInv : Invariant b) (hOk : b.decRef k = .ok b') :
    Invariant b' := by
  unfold decRef at hOk
  cases hk : b.objects[k]? with
  | none => rw [hk] at hOk; simp at hOk
  | some m0 =>
    rw [hk] at hOk
    dsimp only at hOk
    split at hOk
    · simp at hOk
    · simp only [Except.ok.injEq] at hOk
      subst hOk
      have hm0Wf := hInv.objects_wf k m0 hk
      refine ⟨hInv.active_ge, hInv.active_lt, hInv.active_mem, hInv.segments_wf, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x m hx
        dsimp only at hx
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hx
        split at hx
        · next hEq =>
          injection hx with hmEq
          subst hmEq; subst hEq
          exact ⟨hm0Wf.1, hm0Wf.2.1, hm0Wf.2.2.1, hm0Wf.2.2.2.1, hm0Wf.2.2.2.2⟩
        · exact hInv.objects_wf x m hx
      · intro k₁ k₂ m₁ m₂ hm₁ hm₂ hLoc
        dsimp only at hm₁ hm₂
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
        split at hm₁ <;> split at hm₂
        · next h₁ h₂ => exact h₁.symm.trans h₂
        · next h₁ _ =>
          injection hm₁ with hEq; subst hEq; subst h₁
          exact hInv.unique_locs k k₂ m0 m₂ hk hm₂ hLoc
        · next _ h₂ =>
          injection hm₂ with hEq; subst hEq; subst h₂
          exact hInv.unique_locs k₁ k m₁ m0 hm₁ hk hLoc
        · exact hInv.unique_locs k₁ k₂ m₁ m₂ hm₁ hm₂ hLoc
      · intro x
        dsimp only
        rw [hInv.blobs_wf x, Std.ExtTreeMap.mem_insert, compare_eq_iff_eq]
        constructor
        · exact .inr
        · rintro (rfl | hx)
          · rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hk]; rfl
          · exact hx
      · intro d ks hks
        rcases hInv.byDigest_wf d ks hks with ⟨hAll, hNodup⟩
        refine ⟨fun x hx => ⟨(hAll x hx).1, ?_⟩, hNodup⟩
        dsimp only; rw [Std.ExtTreeMap.mem_insert]; exact .inr (hAll x hx).2
      · intro x m hx
        dsimp only at hx
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hx
        split at hx
        · next hEq => subst hEq; exact hInv.byDigest_cov k m0 hk
        · exact hInv.byDigest_cov x m hx
      · intro k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes
        dsimp only at hm₁ hm₂ hb₁ hb₂
        simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hm₁ hm₂
        by_cases h₁ : k = k₁ <;> by_cases h₂ : k = k₂
        · exact h₁.symm.trans h₂
        · simp only [h₁, ↓reduceIte, Option.some.injEq] at hm₁
          simp only [h₂, ↓reduceIte] at hm₂
          subst hm₁; subst h₁
          exact hInv.unique_bytes k k₂ m0 m₂ bs₁ bs₂ hk hm₂ hb₁ hb₂ hdEq hMime hBytes
        · simp only [h₁, ↓reduceIte] at hm₁
          simp only [h₂, ↓reduceIte, Option.some.injEq] at hm₂
          subst hm₂; subst h₂
          exact hInv.unique_bytes k₁ k m₁ m0 bs₁ bs₂ hm₁ hk hb₁ hb₂ hdEq hMime hBytes
        · simp only [h₁, ↓reduceIte] at hm₁
          simp only [h₂, ↓reduceIte] at hm₂
          exact hInv.unique_bytes k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes

theorem gcStep_preserves_invariant {policy : StoragePolicy} {b : BucketState policy}
    (hInv : Invariant b) :
    Invariant b.gcStep := by
  unfold gcStep
  dsimp only
  let objects' := b.objects.filter (fun _ m => m.refCount > 0)
  have hObjIff : ∀ (k : ObjectKey) (m : BucketEntryMeta policy.segmentSize),
      objects'[k]? = some m ↔ b.objects[k]? = some m ∧ m.refCount > 0 := by
    intro k m
    rw [Std.ExtTreeMap.getElem?_filter']
    cases b.objects[k]? <;> simp
  have hLiveIff : ∀ k, isLiveKey b k = true ↔ ∃ m, objects'[k]? = some m := by
    intro k
    unfold isLiveKey
    cases hk : b.objects[k]? with
    | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists]
      intro m hm
      rw [(hObjIff k m).mp hm |>.1] at hk
      simp at hk
    | some m0 =>
      simp only [decide_eq_true_eq]
      constructor
      · intro hPos
        exact ⟨m0, (hObjIff k m0).mpr ⟨hk, hPos⟩⟩
      · rintro ⟨m, hm⟩
        have h := (hObjIff k m).mp hm
        rw [hk] at h
        injection h.1 with hEq
        subst hEq
        exact h.2
  refine ⟨hInv.active_ge, hInv.active_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hInv.active_mem with ⟨seg, hs⟩
    exact ⟨{ seg with live := seg.live.filter (locInObjects (b.objects.filter (fun _ bm => 0 < bm.refCount))) },
      by dsimp only; simp [Std.ExtTreeMap.getElem?_map, hs]⟩
  · -- segments_wf
    intro sid seg hseg
    simp only [Std.ExtTreeMap.getElem?_map] at hseg
    cases hs : b.segments[sid]? with
    | none => rw [hs] at hseg; simp at hseg
    | some seg0 =>
      rw [hs] at hseg
      injection hseg with hEq
      subst hEq
      have hOld := hInv.segments_wf sid seg0 hs
      refine ⟨hOld.1, hOld.2.1, hOld.2.2.1, hOld.2.2.2.1, ?_, ?_⟩
      · intro loc hloc
        simp only [Array.toList_filter, List.mem_filter] at hloc
        exact hOld.2.2.2.2.1 loc hloc.1
      · rw [Array.toList_filter]
        exact hOld.2.2.2.2.2.filter _
  · -- objects_wf
    intro k m hm
    change objects'[k]? = some m at hm
    have ⟨hmOld, hPos⟩ := (hObjIff k m).mp hm
    have hOldWf := hInv.objects_wf k m hmOld
    rcases hOldWf.2.2.2.1 with ⟨bs, hbs, hbsSz, hcrc⟩
    rcases hOldWf.2.2.2.2 with ⟨seg, hseg, hlocMem⟩
    refine ⟨hOldWf.1, hOldWf.2.1, hOldWf.2.2.1, ⟨bs, ?_, hbsSz, hcrc⟩, ?_⟩
    · rw [Std.ExtTreeMap.getElem?_filter']
      have hLive : isLiveKey b k = true := (hLiveIff k).mpr ⟨m, hm⟩
      simp [hbs, hLive]
    · refine ⟨{ seg with live := seg.live.filter (locInObjects objects') },
        by simp only [Std.ExtTreeMap.getElem?_map, hseg]; rfl, ?_⟩
      rw [Array.toList_filter, List.mem_filter]
      refine ⟨hlocMem, (locInObjects_iff objects' m.location).mpr ⟨k, m, hm, rfl⟩⟩
  · -- unique_locs
    intro k₁ k₂ m₁ m₂ hm₁ hm₂ hLoc
    exact hInv.unique_locs k₁ k₂ m₁ m₂ ((hObjIff k₁ m₁).mp hm₁).1 ((hObjIff k₂ m₂).mp hm₂).1 hLoc
  · -- blobs_wf
    intro k
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Std.ExtTreeMap.mem_iff_isSome_getElem?,
      Std.ExtTreeMap.getElem?_filter']
    cases hbk : b.blobs[k]? with
    | none =>
      simp only [Option.filter_none, Option.isSome_none, Bool.false_eq_true, false_iff, Bool.not_eq_true]
      cases hok : objects'[k]? with
      | none => rfl
      | some m =>
        exfalso
        have hMemObj : k ∈ b.objects := by
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, ((hObjIff k m).mp hok).1]; rfl
        have hMemBlob := (hInv.blobs_wf k).mpr hMemObj
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hbk] at hMemBlob
        simp at hMemBlob
    | some bs =>
      dsimp only
      by_cases hl : isLiveKey b k = true
      · simp only [hl, Option.filter_some, ↓reduceIte, Option.isSome_some, true_iff]
        rcases (hLiveIff k).mp hl with ⟨m, hm⟩
        change objects'[k]? = some m at hm
        rw [hm]; rfl
      · simp only [hl, Option.filter_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_iff]
        intro hSome
        cases hok : objects'[k]? with
        | none => rw [hok] at hSome; simp at hSome
        | some m => exact hl ((hLiveIff k).mpr ⟨m, hok⟩)
  · -- byDigest_wf
    intro d ks hks
    rw [Std.ExtTreeMap.getElem?_filterMap'] at hks
    cases hd : b.byDigest[d]? with
    | none => rw [hd] at hks; simp at hks
    | some ks0 =>
      rw [hd] at hks
      simp only [Option.bind_some] at hks
      split at hks
      · simp at hks
      · injection hks with hksEq
        subst hksEq
        have hOld := hInv.byDigest_wf d ks0 hd
        constructor
        · intro x hx
          rw [Array.toList_filter, List.mem_filter] at hx
          refine ⟨(hOld.1 x hx.1).1, ?_⟩
          dsimp only
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
          rcases (hLiveIff x).mp hx.2 with ⟨m, hm⟩
          change objects'[x]? = some m at hm
          rw [hm]; rfl
        · rw [Array.toList_filter]
          exact hOld.2.filter _
  · -- byDigest_cov
    intro k m hm
    have ⟨hmOld, hPos⟩ := (hObjIff k m).mp hm
    rcases hInv.byDigest_cov k m hmOld with ⟨ks0, hks0, hMem0⟩
    have hLive : isLiveKey b k = true := (hLiveIff k).mpr ⟨m, hm⟩
    have hMemKept : k ∈ (ks0.filter (isLiveKey b)).toList := by
      rw [Array.toList_filter, List.mem_filter]
      exact ⟨hMem0, hLive⟩
    have hNotEmpty : ¬ (ks0.filter (isLiveKey b)).isEmpty = true := by
      intro hEmp
      have hSz : (ks0.filter (isLiveKey b)).size = 0 := by
        simpa [Array.isEmpty] using hEmp
      have hNil : (ks0.filter (isLiveKey b)).toList = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hSz)
      rw [hNil] at hMemKept
      cases hMemKept
    refine ⟨ks0.filter (isLiveKey b), ?_, hMemKept⟩
    dsimp only
    rw [Std.ExtTreeMap.getElem?_filterMap', hks0, Option.bind_some]
    simp only [hNotEmpty, Bool.false_eq_true, ↓reduceIte]
  · -- unique_bytes
    intro k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq hMime hBytes
    dsimp only at hb₁ hb₂
    rw [Std.ExtTreeMap.getElem?_filter'] at hb₁ hb₂
    cases hbo₁ : b.blobs[k₁]? with
    | none => rw [hbo₁] at hb₁; simp at hb₁
    | some bs₁' =>
      rw [hbo₁] at hb₁
      cases hbo₂ : b.blobs[k₂]? with
      | none => rw [hbo₂] at hb₂; simp at hb₂
      | some bs₂' =>
        rw [hbo₂] at hb₂
        by_cases hl₁ : isLiveKey b k₁ <;> by_cases hl₂ : isLiveKey b k₂
        · simp only [hl₁, hl₂, Option.filter_some, ↓reduceIte, Option.some.injEq] at hb₁ hb₂
          subst hb₁; subst hb₂
          exact hInv.unique_bytes k₁ k₂ m₁ m₂ bs₁' bs₂'
            ((hObjIff k₁ m₁).mp hm₁).1 ((hObjIff k₂ m₂).mp hm₂).1 hbo₁ hbo₂ hdEq hMime hBytes
        · simp [hl₂] at hb₂
        · simp [hl₁] at hb₁
        · simp [hl₁] at hb₁

private theorem foldlM_repack_preserves {policy : StoragePolicy}
    (entries : List (ObjectKey × BucketEntryMeta policy.segmentSize))
    (hNodup : (entries.map Prod.fst).Nodup)
    (hKeys : ∀ e ∈ entries, e.2.key = e.1)
    (init : RepackAcc policy) (minSeg : SegmentId)
    (hVal : RepackValid minSeg init)
    (hDisj : ∀ e ∈ entries, e.1 ∉ init.objects)
    (fin : RepackAcc policy)
    (hOk : entries.foldlM (m := Except CoreError) repackEntry init = .ok fin) :
    RepackValid minSeg fin ∧
    (∀ (kOld : ObjectKey) (mOld : BucketEntryMeta policy.segmentSize),
      init.objects[kOld]? = some mOld → fin.objects[kOld]? = some mOld) ∧
    (∀ e ∈ entries, ∃ m', fin.objects[e.1]? = some m' ∧
      m'.key = e.2.key ∧ m'.mime = e.2.mime ∧ m'.crc32 = e.2.crc32 ∧
      m'.byteSize = e.2.byteSize ∧ m'.refCount = e.2.refCount ∧
      m'.location.length = e.2.location.length) ∧
    (∀ k m', fin.objects[k]? = some m' →
      init.objects[k]? = some m' ∨ ∃ m0, (k, m0) ∈ entries ∧
        m'.key = m0.key ∧ m'.mime = m0.mime ∧ m'.crc32 = m0.crc32 ∧
        m'.byteSize = m0.byteSize ∧ m'.refCount = m0.refCount ∧
        m'.location.length = m0.location.length) := by
  induction entries generalizing init with
  | nil =>
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hOk
    subst hOk
    exact ⟨hVal, (fun _ _ h => h), (fun _ h => False.elim (List.not_mem_nil h)), (fun _ _ h => Or.inl h)⟩
  | cons hd tl ih =>
    rcases hd with ⟨k, bm⟩
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hNodup
    rcases hNodup with ⟨hkNotInTl, hTlNodup⟩
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at hOk
    cases hStep : repackEntry init (k, bm) with
    | error e => rw [hStep] at hOk; simp at hOk
    | ok mid =>
      rw [hStep] at hOk
      dsimp only at hOk
      unfold repackEntry at hStep
      dsimp only at hStep
      cases hAlloc : allocLocation policy bm.location.length bm.location.nonEmpty
          (by have := bm.location.validBounds; omega)
          init.segments init.activeSeg init.nextSegId with
      | error e => rw [hAlloc] at hStep; simp at hStep
      | ok res =>
        rw [hAlloc] at hStep
        rcases res with ⟨loc, segs', act', next'⟩
        dsimp only at hStep
        injection hStep with hMid
        subst hMid
        have hLocLen : loc.length = bm.location.length := allocLocation_length hAlloc
        have hKeyEq : bm.key = k := hKeys (k, bm) List.mem_cons_self
        have hMetaEq : ({ bm with location := loc } : BucketEntryMeta policy.segmentSize) =
            ⟨k, loc, bm.mime, bm.crc32, bm.byteSize, bm.refCount⟩ := by
          cases bm; dsimp only at hKeyEq; subst hKeyEq; rfl
        have hNotInit := hDisj (k, bm) List.mem_cons_self
        have hAllocVal := (alloc_insert_preserves_valid hVal k hNotInit
          bm.location.length bm.location.nonEmpty _ loc segs' act' next' hAlloc
          bm.mime bm.crc32 bm.byteSize bm.refCount).1
        rw [← hMetaEq] at hAllocVal
        have hMidObjSelf : (init.objects.insert k { bm with location := loc })[k]? =
            some { bm with location := loc } :=
          Std.ExtTreeMap.getElem?_insert_self
        have hDisjTl : ∀ e ∈ tl, e.1 ∉ (init.objects.insert k { bm with location := loc }) := by
          intro e he hmem
          rw [Std.ExtTreeMap.mem_insert, compare_eq_iff_eq] at hmem
          rcases hmem with rfl | hOldMem
          · exact hkNotInTl ⟨e, he, rfl⟩
          · exact hDisj e (List.mem_cons_of_mem _ he) hOldMem
        have hRec := ih hTlNodup (fun e he => hKeys e (List.mem_cons_of_mem _ he)) _ hAllocVal hDisjTl hOk
        rcases hRec with ⟨hValFin, hPresMid, hInsTl, hFromFin⟩
        refine ⟨hValFin, ?_, ?_, ?_⟩
        · intro kOld mOld hmOld
          have hNe : k ≠ kOld := by
            rintro rfl
            rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hmOld] at hNotInit
            simp at hNotInit
          apply hPresMid
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
          exact hmOld
        · intro e he
          rcases List.mem_cons.mp he with rfl | heTl
          · refine ⟨{ bm with location := loc }, hPresMid k _ hMidObjSelf,
              rfl, rfl, rfl, rfl, rfl, hLocLen⟩
          · exact hInsTl e heTl
        · intro kf mf hmf
          rcases hFromFin kf mf hmf with hMid | hTl
          · dsimp only at hMid
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hMid
            split at hMid
            · next hEq =>
              subst hEq
              injection hMid with hEqMeta
              subst hEqMeta
              exact .inr ⟨bm, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, hLocLen⟩
            · exact .inl hMid
          · rcases hTl with ⟨m0, hm0Mem, hProps⟩
            exact .inr ⟨m0, List.mem_cons_of_mem _ hm0Mem, hProps⟩

theorem compactBucket_preserves_invariant {policy : StoragePolicy}
    {b b' : BucketState policy}
    (hInv : Invariant b) (hOk : b.compactBucket = .ok b') :
    Invariant b' := by
  unfold compactBucket at hOk
  split at hOk
  · simp at hOk
  · next hNoOv =>
    simp only [Nat.not_le] at hNoOv
    dsimp only at hOk
    cases hFold : b.objects.toList.foldlM (m := Except CoreError) repackEntry
        { objects := ∅
          segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
            b.nextSegId ⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩
          activeSeg := b.nextSegId
          nextSegId := ⟨b.nextSegId.val + 1⟩ } with
    | error e => rw [hFold] at hOk; simp at hOk
    | ok fin =>
      rw [hFold] at hOk
      injection hOk with hb'
      subst hb'
      have hSucc : (b.nextSegId.val + 1).toNat = b.nextSegId.val.toNat + 1 :=
        uint64_succ_toNat hNoOv
      have hFirstPos : 1 ≤ b.nextSegId.val.toNat :=
        Nat.le_trans hInv.active_ge (Nat.le_of_lt hInv.active_lt)
      have hInitVal : RepackValid b.nextSegId
          { objects := ∅
            segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
              b.nextSegId ⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩
            activeSeg := b.nextSegId
            nextSegId := ⟨b.nextSegId.val + 1⟩ } :=
        { minSeg_pos := hFirstPos
          active_ge := Nat.le_refl _
          active_lt := by dsimp only; rw [hSucc]; omega
          active_mem := ⟨⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩, by simp⟩
          segments_wf := by
            intro sid seg hs
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hs
            split at hs
            · next hEq =>
              injection hs with hS
              subst hS; subst hEq
              refine ⟨rfl, Nat.le_refl _, ?_, Nat.zero_le _, ?_, ?_⟩
              · rw [hSucc]; omega
              · intro l hl; simp at hl
              · simp
            · simp at hs
          objects_wf := by intro k m hm; simp at hm
          unique_locs := by intro k₁ k₂ m₁ m₂ hm₁; simp at hm₁ }
      have hNodup : (b.objects.toList.map Prod.fst).Nodup := by
        have hDist := Std.ExtTreeMap.distinct_keys_toList (t := b.objects)
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact hDist.imp fun {a b} hcmp heq => hcmp (by rw [heq, Std.ReflCmp.compare_self (cmp := compare)])
      have hPack := foldlM_repack_preserves b.objects.toList hNodup
        (fun e he => (hInv.objects_wf e.1 e.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp he)).1)
        _ b.nextSegId hInitVal (fun _ _ h => by simp at h) fin hFold
      rcases hPack with ⟨hValFin, _, hIns, hFromFin⟩
      have hKeyMatch : ∀ (k : ObjectKey) (m' : BucketEntryMeta policy.segmentSize),
          fin.objects[k]? = some m' →
          ∃ m0, b.objects[k]? = some m0 ∧
            m'.key = m0.key ∧ m'.mime = m0.mime ∧ m'.crc32 = m0.crc32 ∧
            m'.byteSize = m0.byteSize ∧ m'.refCount = m0.refCount ∧
            m'.location.length = m0.location.length := by
        intro k m' hm'
        rcases hFromFin k m' hm' with hInInit | ⟨m0, hMemList, hProps⟩
        · simp at hInInit
        · exact ⟨m0, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hMemList, hProps⟩
      have hSameMem : ∀ (k : ObjectKey), k ∈ fin.objects ↔ k ∈ b.objects := by
        intro k
        constructor
        · intro hk
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hk ⊢
          cases hfk : fin.objects[k]? with
          | none => rw [hfk] at hk; simp at hk
          | some m' =>
            rcases hKeyMatch k m' hfk with ⟨m0, hm0, _⟩
            simp [hm0]
        · intro hk
          rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hk ⊢
          cases hok : b.objects[k]? with
          | none => rw [hok] at hk; simp at hk
          | some m0 =>
            have ⟨m', hm', _⟩ := hIns (k, m0) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hok)
            simp [hm']
      refine ⟨Nat.le_trans hFirstPos hValFin.active_ge, hValFin.active_lt, hValFin.active_mem, ?_, ?_, hValFin.unique_locs, ?_, ?_, ?_, ?_⟩
      · intro sid seg hseg
        have hs := hValFin.segments_wf sid seg hseg
        exact ⟨hs.1, Nat.le_trans hFirstPos hs.2.1, hs.2.2⟩
      · intro k m' hm'
        rcases hKeyMatch k m' hm' with ⟨m0, hm0, _, hMime, hCrc, hSz, _, hLen⟩
        have hOldWf := hInv.objects_wf k m0 hm0
        have hFinWf := hValFin.objects_wf k m' hm'
        refine ⟨hFinWf.1, hSz ▸ hOldWf.2.1, ?_, ?_, hFinWf.2⟩
        · rw [hLen, hSz]; exact hOldWf.2.2.1
        · rcases hOldWf.2.2.2.1 with ⟨bs, hbs, hbsSz, hOldCrc⟩
          exact ⟨bs, hbs, hSz ▸ hbsSz, hCrc ▸ hOldCrc⟩
      · intro k
        dsimp only
        rw [hInv.blobs_wf k, hSameMem k]
      · intro d ks hks
        rcases hInv.byDigest_wf d ks hks with ⟨hAll, hNd⟩
        exact ⟨fun x hx => ⟨(hAll x hx).1, (hSameMem x).mpr (hAll x hx).2⟩, hNd⟩
      · intro k m' hm'
        rcases hKeyMatch k m' hm' with ⟨m0, hm0, _⟩
        exact hInv.byDigest_cov k m0 hm0
      · intro k₁ k₂ m₁' m₂' bs₁ bs₂ hm₁' hm₂' hb₁ hb₂ hdEq hMime hBytes
        rcases hKeyMatch k₁ m₁' hm₁' with ⟨m₁, hm₁, _, hMime₁, _⟩
        rcases hKeyMatch k₂ m₂' hm₂' with ⟨m₂, hm₂, _, hMime₂, _⟩
        exact hInv.unique_bytes k₁ k₂ m₁ m₂ bs₁ bs₂ hm₁ hm₂ hb₁ hb₂ hdEq
          (hMime₁.symm.trans (hMime.trans hMime₂)) hBytes

private theorem pairwise_disjoint_of_mem {α : Type} {R : α → α → Prop} {l : List α}
    (hPair : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b ∨ R b a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rcases List.pairwise_cons.mp hPair with ⟨hx, hxs⟩
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hne
    · exact .inl (hx b hb')
    · exact .inr (hx a ha')
    · exact ih hxs ha' hb'

/-- Distinct objects residing in the same segment occupy strictly disjoint byte intervals. -/
theorem alloc_disjoint {policy : StoragePolicy} {b : BucketState policy} (hInv : Invariant b)
    {k₁ k₂ : ObjectKey} {m₁ m₂ : BucketEntryMeta policy.segmentSize}
    (hm₁ : b.objects[k₁]? = some m₁) (hm₂ : b.objects[k₂]? = some m₂)
    (hNe : k₁ ≠ k₂) (hSameSeg : m₁.location.segment = m₂.location.segment) :
    m₁.location.offset + m₁.location.length ≤ m₂.location.offset ∨
    m₂.location.offset + m₂.location.length ≤ m₁.location.offset := by
  have hLocNe : m₁.location ≠ m₂.location := fun h => hNe (hInv.unique_locs k₁ k₂ m₁ m₂ hm₁ hm₂ h)
  rcases (hInv.objects_wf k₁ m₁ hm₁).2.2.2.2 with ⟨seg₁, hseg₁, hmem₁⟩
  rcases (hInv.objects_wf k₂ m₂ hm₂).2.2.2.2 with ⟨seg₂, hseg₂, hmem₂⟩
  rw [hSameSeg, hseg₂] at hseg₁
  injection hseg₁ with hSegEq
  subst hSegEq
  have hPair := (hInv.segments_wf m₂.location.segment seg₂ hseg₂).2.2.2.2.2
  exact pairwise_disjoint_of_mem hPair hmem₁ hmem₂ hLocNe

/-- Deduplication soundness: putting `(mime, bytes)` matching an existing entry reuses that exact `ObjectKey`. -/
theorem putObject_dedup_sound {policy : StoragePolicy} {b : BucketState policy}
    (hInv : Invariant b) {k : ObjectKey} {m : BucketEntryMeta policy.segmentSize}
    {mime : MimeType} {bytes : ByteArray}
    (hm : b.objects[k]? = some m) (hb : b.blobs[k]? = some bytes)
    (hDig : k.digest = sha256 bytes) (hMime : m.mime = mime) :
    b.putObject mime bytes = .ok (k, b) := by
  have hWf := hInv.objects_wf k m hm
  have hSz : bytes.size ≤ policy.maxImageBytes := by
    rcases hWf.2.2.2.1 with ⟨bs, hbs, hbsSz, _⟩
    rw [hb] at hbs
    injection hbs with hbsEq
    subst hbsEq
    rw [hbsSz]
    exact hWf.2.1
  rcases hInv.byDigest_cov k m hm with ⟨ks, hks, hInKs⟩
  rw [hDig] at hks
  have ⟨found, hFound⟩ := findMatchingKey_complete b.blobs b.objects mime bytes ks.toList
    k m hInKs hb hm hMime
  have hSpec := findMatchingKey_spec b.blobs b.objects mime bytes ks.toList found hFound
  rcases hSpec with ⟨hFoundMem, hFoundBlob, mFound, hmFound, hMimeFound⟩
  have hFoundDig : found.digest = sha256 bytes := by
    have hd := (hInv.byDigest_wf (sha256 bytes) ks hks).1 found hFoundMem
    exact hd.1
  have hKeyEq : found = k :=
    hInv.unique_bytes found k mFound m bytes bytes hmFound hm hFoundBlob hb
      (hFoundDig.trans hDig.symm) (hMimeFound.trans hMime.symm) rfl
  subst hKeyEq
  unfold putObject putObjectWithHash
  simp only [hSz, ↓reduceDIte, hks, Option.getD_some, hFound]

/-- Content immutability: `putObjectWithHash` never mutates existing object payloads. -/
theorem putObjectWithHash_preserves_blobs {policy : StoragePolicy}
    {b b' : BucketState policy} {digest : Sha256Digest} {mime : MimeType}
    {bytes : ByteArray} {key : ObjectKey}
    (hInv : Invariant b)
    (hOk : b.putObjectWithHash digest mime bytes = .ok (key, b'))
    {kOld : ObjectKey} (hOld : kOld ∈ b.blobs) :
    b'.blobs[kOld]? = b.blobs[kOld]? := by
  unfold putObjectWithHash at hOk
  dsimp only at hOk
  split at hOk
  · cases hFind : findMatchingKey b.blobs b.objects mime bytes ((b.byDigest[digest]?).getD #[]).toList with
    | some _ =>
      rw [hFind] at hOk; simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rw [hOk.2]
    | none =>
      rw [hFind] at hOk; dsimp only at hOk
      cases hTag : nextCollisionTag ((b.byDigest[digest]?).getD #[]) with
      | error _ => rw [hTag] at hOk; simp at hOk
      | ok tag =>
        rw [hTag] at hOk; dsimp only at hOk
        split at hOk
        · simp at hOk
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          have hFreshTag : ∀ x ∈ ((b.byDigest[digest]?).getD #[]).toList, x.tag ≠ tag :=
            nextCollisionTag_fresh hTag
          have hNe : ⟨digest, tag⟩ ≠ kOld := by
            intro hEq
            subst hEq
            have hMemObj : ⟨digest, tag⟩ ∈ b.objects := (hInv.blobs_wf _).mp hOld
            rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hMemObj
            cases hObj : b.objects[(⟨digest, tag⟩ : ObjectKey)]? with
            | none => rw [hObj] at hMemObj; simp at hMemObj
            | some m =>
              rcases hInv.byDigest_cov ⟨digest, tag⟩ m hObj with ⟨ks, hks, hInKs⟩
              have hCand : (b.byDigest[digest]?).getD #[] = ks := by simp [hks]
              rw [← hCand] at hInKs
              exact hFreshTag ⟨digest, tag⟩ hInKs rfl
          dsimp only
          simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
  · simp at hOk

/-- Explicit hash-collision safety: distinct payloads under the same digest receive distinct keys and retrieve faithfully. -/
theorem putObjectWithHash_collision_safe {policy : StoragePolicy}
    {b b₁' b₂' : BucketState policy} {digest : Sha256Digest} {mime : MimeType}
    {bytes₁ bytes₂ : ByteArray} {k₁ k₂ : ObjectKey}
    (hInv : Invariant b)
    (h₁ : b.putObjectWithHash digest mime bytes₁ = .ok (k₁, b₁'))
    (h₂ : b₁'.putObjectWithHash digest mime bytes₂ = .ok (k₂, b₂'))
    (hDiff : bytes₁ ≠ bytes₂) :
    k₁ ≠ k₂ ∧ b₂'.getObject k₁ = some bytes₁ ∧ b₂'.getObject k₂ = some bytes₂ := by
  have hInv₁ := putObjectWithHash_preserves_invariant hInv h₁
  have hGet1 : b₁'.blobs[k₁]? = some bytes₁ := by
    unfold putObjectWithHash at h₁
    dsimp only at h₁
    split at h₁
    · cases hFind : findMatchingKey b.blobs b.objects mime bytes₁ ((b.byDigest[digest]?).getD #[]).toList with
      | some existing =>
        rw [hFind] at h₁
        simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨rfl, rfl⟩
        exact (findMatchingKey_spec b.blobs b.objects mime bytes₁ _ existing hFind).2.1
      | none =>
        rw [hFind] at h₁; dsimp only at h₁
        split at h₁
        · simp at h₁
        · split at h₁
          · simp at h₁
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
            rcases h₁ with ⟨rfl, rfl⟩
            simp
    · simp at h₁
  have hGet2 : b₂'.blobs[k₂]? = some bytes₂ := by
    unfold putObjectWithHash at h₂
    dsimp only at h₂
    split at h₂
    · cases hFind : findMatchingKey b₁'.blobs b₁'.objects mime bytes₂ ((b₁'.byDigest[digest]?).getD #[]).toList with
      | some existing =>
        rw [hFind] at h₂
        simp only [Except.ok.injEq, Prod.mk.injEq] at h₂
        rcases h₂ with ⟨rfl, rfl⟩
        exact (findMatchingKey_spec b₁'.blobs b₁'.objects mime bytes₂ _ existing hFind).2.1
      | none =>
        rw [hFind] at h₂; dsimp only at h₂
        split at h₂
        · simp at h₂
        · split at h₂
          · simp at h₂
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h₂
            rcases h₂ with ⟨rfl, rfl⟩
            simp
    · simp at h₂
  have hk₁Mem : k₁ ∈ b₁'.blobs := by
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hGet1]; rfl
  have hPres1 := putObjectWithHash_preserves_blobs hInv₁ h₂ hk₁Mem
  have hGet1After : b₂'.blobs[k₁]? = some bytes₁ := hPres1.trans hGet1
  have hNe : k₁ ≠ k₂ := by
    intro hEq
    rw [hEq, hGet2] at hGet1After
    injection hGet1After with hB
    exact hDiff hB.symm
  exact ⟨hNe, hGet1After, hGet2⟩

/-- `incRef` never modifies stored object payloads. -/
theorem incRef_preserves_blobs {policy : StoragePolicy}
    {b b' : BucketState policy} {k : ObjectKey}
    (hOk : b.incRef k = .ok b') : b'.blobs = b.blobs := by
  unfold incRef at hOk
  split at hOk
  · simp at hOk
  · simp only [Except.ok.injEq] at hOk; subst hOk; rfl

/-- `decRef` never modifies stored object payloads. -/
theorem decRef_preserves_blobs {policy : StoragePolicy}
    {b b' : BucketState policy} {k : ObjectKey}
    (hOk : b.decRef k = .ok b') : b'.blobs = b.blobs := by
  unfold decRef at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · simp only [Except.ok.injEq] at hOk; subst hOk; rfl

/-- GC safety: live objects (`refCount > 0`) retain identical metadata, location, and bytes. -/
theorem gcStep_preserves_live {policy : StoragePolicy} (b : BucketState policy)
    {k : ObjectKey} {m : BucketEntryMeta policy.segmentSize}
    (hm : b.objects[k]? = some m) (hPos : 0 < m.refCount) :
    b.gcStep.objects[k]? = some m ∧ b.gcStep.blobs[k]? = b.blobs[k]? := by
  unfold gcStep isLiveKey
  dsimp only
  rw [Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_filter', hm]
  simp only [hPos, decide_true, Option.filter_some]
  cases b.blobs[k]? <;> simp

/-- GC reclaims unreferenced (`refCount = 0`) objects completely. -/
theorem gcStep_reclaims_unreferenced {policy : StoragePolicy} (b : BucketState policy)
    {k : ObjectKey} {m : BucketEntryMeta policy.segmentSize}
    (hm : b.objects[k]? = some m) (hZero : m.refCount = 0) :
    b.gcStep.objects[k]? = none ∧ b.gcStep.blobs[k]? = none := by
  unfold gcStep isLiveKey
  dsimp only
  rw [Std.ExtTreeMap.getElem?_filter', Std.ExtTreeMap.getElem?_filter', hm]
  simp only [hZero, Nat.lt_irrefl, decide_false, Option.filter_some]
  cases b.blobs[k]? <;> simp

/-- Compaction equivalence: every retained object keeps identical payload and metadata. -/
theorem compactBucket_equiv {policy : StoragePolicy}
    {b b' : BucketState policy}
    (hInv : Invariant b) (hOk : b.compactBucket = .ok b') :
    b'.blobs = b.blobs ∧
    (∀ (k : ObjectKey), b'.getObject k = b.getObject k) ∧
    (∀ (k : ObjectKey) (m : BucketEntryMeta policy.segmentSize),
      b.objects[k]? = some m →
      ∃ m', b'.objects[k]? = some m' ∧
        m'.key = m.key ∧ m'.mime = m.mime ∧ m'.crc32 = m.crc32 ∧
        m'.byteSize = m.byteSize ∧ m'.refCount = m.refCount) := by
  unfold compactBucket at hOk
  split at hOk
  · simp at hOk
  · next hNoOv =>
    simp only [Nat.not_le] at hNoOv
    dsimp only at hOk
    cases hFold : b.objects.toList.foldlM (m := Except CoreError) repackEntry
        { objects := ∅
          segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
            b.nextSegId ⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩
          activeSeg := b.nextSegId
          nextSegId := ⟨b.nextSegId.val + 1⟩ } with
    | error _ => rw [hFold] at hOk; simp at hOk
    | ok fin =>
      rw [hFold] at hOk
      injection hOk with hb'
      subst hb'
      have hSucc : (b.nextSegId.val + 1).toNat = b.nextSegId.val.toNat + 1 :=
        uint64_succ_toNat hNoOv
      have hFirstPos : 1 ≤ b.nextSegId.val.toNat :=
        Nat.le_trans hInv.active_ge (Nat.le_of_lt hInv.active_lt)
      have hInitVal : RepackValid b.nextSegId
          { objects := ∅
            segments := (∅ : Std.ExtTreeMap SegmentId (SegmentMeta policy.segmentSize)).insert
              b.nextSegId ⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩
            activeSeg := b.nextSegId
            nextSegId := ⟨b.nextSegId.val + 1⟩ } :=
        { minSeg_pos := hFirstPos
          active_ge := Nat.le_refl _
          active_lt := by dsimp only; rw [hSucc]; omega
          active_mem := ⟨⟨b.nextSegId, 0, Nat.zero_le _, #[]⟩, by simp⟩
          segments_wf := by
            intro sid seg hs
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hs
            split at hs
            · next hEq =>
              injection hs with hS; subst hS; subst hEq
              refine ⟨rfl, Nat.le_refl _, ?_, Nat.zero_le _, ?_, ?_⟩
              · rw [hSucc]; omega
              · intro l hl; simp at hl
              · simp
            · simp at hs
          objects_wf := by intro k m hm; simp at hm
          unique_locs := by intro k₁ k₂ m₁ m₂ hm₁; simp at hm₁ }
      have hNodup : (b.objects.toList.map Prod.fst).Nodup := by
        have hDist := Std.ExtTreeMap.distinct_keys_toList (t := b.objects)
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact hDist.imp fun {a b} hcmp heq => hcmp (by rw [heq, Std.ReflCmp.compare_self (cmp := compare)])
      have hPack := foldlM_repack_preserves b.objects.toList hNodup
        (fun e he => (hInv.objects_wf e.1 e.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp he)).1)
        _ b.nextSegId hInitVal (fun _ _ h => by simp at h) fin hFold
      rcases hPack with ⟨_, _, hIns, _⟩
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro k m hm
      rcases hIns (k, m) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hm) with
        ⟨m', hm', hk, hmime, hcrc, hsz, href, _⟩
      exact ⟨m', hm', hk, hmime, hcrc, hsz, href⟩

/-- `putObjectWithHash` preserves all existing object entries and initializes any new key with `refCount = 0`. -/
theorem putObjectWithHash_objects_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {digest : Sha256Digest} {mime : MimeType}
    {bytes : ByteArray} {key : ObjectKey}
    (hInv : Invariant b)
    (hOk : b.putObjectWithHash digest mime bytes = .ok (key, b')) :
    (∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
      b.objects[k]? = some bm → b'.objects[k]? = some bm) ∧
    (∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
      b'.objects[k]? = some bm →
      b.objects[k]? = some bm ∨ (k = key ∧ bm.refCount = 0 ∧ b.objects[key]? = none)) := by
  unfold putObjectWithHash at hOk
  dsimp only at hOk
  split at hOk
  · cases hFind : findMatchingKey b.blobs b.objects mime bytes ((b.byDigest[digest]?).getD #[]).toList with
    | some existing =>
      rw [hFind] at hOk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      rcases hOk with ⟨rfl, rfl⟩
      exact ⟨fun _ _ h => h, fun _ _ h => .inl h⟩
    | none =>
      rw [hFind] at hOk; dsimp only at hOk
      cases hTag : nextCollisionTag ((b.byDigest[digest]?).getD #[]) with
      | error _ => rw [hTag] at hOk; simp at hOk
      | ok tag =>
        rw [hTag] at hOk; dsimp only at hOk
        split at hOk
        · simp at hOk
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          have hFreshTag : ∀ x ∈ ((b.byDigest[digest]?).getD #[]).toList, x.tag ≠ tag :=
            nextCollisionTag_fresh hTag
          have hNone : b.objects[(⟨digest, tag⟩ : ObjectKey)]? = none := by
            cases hObj : b.objects[(⟨digest, tag⟩ : ObjectKey)]? with
            | none => rfl
            | some m =>
              exfalso
              rcases hInv.byDigest_cov ⟨digest, tag⟩ m hObj with ⟨ks, hks, hInKs⟩
              have hCand : (b.byDigest[digest]?).getD #[] = ks := by simp [hks]
              rw [← hCand] at hInKs
              exact hFreshTag ⟨digest, tag⟩ hInKs rfl
          constructor
          · intro k bm hbm
            have hNe : (⟨digest, tag⟩ : ObjectKey) ≠ k := by
              rintro rfl; rw [hNone] at hbm; simp at hbm
            dsimp only
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq, hNe, ↓reduceIte]
            exact hbm
          · intro k bm hbm
            dsimp only at hbm
            simp only [Std.ExtTreeMap.getElem?_insert, compare_eq_iff_eq] at hbm
            split at hbm
            · next hEq =>
              subst hEq
              injection hbm with hBm
              subst hBm
              exact .inr ⟨rfl, rfl, hNone⟩
            · exact .inl hbm
  · simp at hOk

/-- `putObject` preserves all existing object entries and initializes any new key with `refCount = 0`. -/
theorem putObject_objects_spec {policy : StoragePolicy}
    {b b' : BucketState policy} {mime : MimeType} {bytes : ByteArray} {key : ObjectKey}
    (hInv : Invariant b)
    (hOk : b.putObject mime bytes = .ok (key, b')) :
    (∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
      b.objects[k]? = some bm → b'.objects[k]? = some bm) ∧
    (∀ (k : ObjectKey) (bm : BucketEntryMeta policy.segmentSize),
      b'.objects[k]? = some bm →
      b.objects[k]? = some bm ∨ (k = key ∧ bm.refCount = 0 ∧ b.objects[key]? = none)) :=
  putObjectWithHash_objects_spec hInv hOk

end BucketState

end Leaf.Core