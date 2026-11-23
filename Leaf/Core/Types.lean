namespace Leaf.Core

open Std

instance : Repr ByteArray where
  reprPrec b _ := s!"<ByteArray {b.size}B>"

/-- Helper proving `TransCmp` for any projection into `Nat`. -/
theorem transCmp_of_natProj {α : Type} (proj : α → Nat) :
    TransCmp (fun a b : α => compare (proj a) (proj b)) :=
  inferInstanceAs (TransCmp (compareOn proj))

/-- Helper proving `LawfulEqCmp` for any injective projection into `Nat`. -/
theorem lawfulEqCmp_of_natProj {α : Type} (proj : α → Nat)
    (inj : ∀ {a b}, proj a = proj b → a = b) :
    LawfulEqCmp (fun a b : α => compare (proj a) (proj b)) where
  compare_self {a} := ReflOrd.compare_self (a := proj a)
  eq_of_compare h := inj (LawfulEqOrd.eq_of_compare h)

/-- Primary key for posts (1-indexed for persisted records). -/
structure PostId where
  val : UInt64
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace PostId
instance : Ord PostId := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : LT PostId := ⟨fun a b => a.val.toNat < b.val.toNat⟩
instance : LE PostId := ⟨fun a b => a.val.toNat ≤ b.val.toNat⟩
instance : DecidableLT PostId := fun a b => inferInstanceAs (Decidable (a.val.toNat < b.val.toNat))
instance : DecidableLE PostId := fun a b => inferInstanceAs (Decidable (a.val.toNat ≤ b.val.toNat))
instance : TransOrd PostId := transCmp_of_natProj (fun x : PostId => x.val.toNat)
instance : LawfulEqOrd PostId :=
  lawfulEqCmp_of_natProj (fun x : PostId => x.val.toNat) (fun {a b} h => by
    cases a; cases b; simp only at h; congr 1; exact UInt64.toNat_inj.mp h)
end PostId

/-- Monotonic transaction identifier (1-indexed). -/
structure TxId where
  val : UInt64
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace TxId
instance : Ord TxId := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : LT TxId := ⟨fun a b => a.val.toNat < b.val.toNat⟩
instance : LE TxId := ⟨fun a b => a.val.toNat ≤ b.val.toNat⟩
instance : DecidableLT TxId := fun a b => inferInstanceAs (Decidable (a.val.toNat < b.val.toNat))
instance : DecidableLE TxId := fun a b => inferInstanceAs (Decidable (a.val.toNat ≤ b.val.toNat))
instance : TransOrd TxId := transCmp_of_natProj (fun x : TxId => x.val.toNat)
instance : LawfulEqOrd TxId :=
  lawfulEqCmp_of_natProj (fun x : TxId => x.val.toNat) (fun {a b} h => by
    cases a; cases b; simp only at h; congr 1; exact UInt64.toNat_inj.mp h)
end TxId

/-- Monotonic log and post version sequence number. -/
structure SeqNo where
  val : UInt64
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace SeqNo
instance : Ord SeqNo := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : LT SeqNo := ⟨fun a b => a.val.toNat < b.val.toNat⟩
instance : LE SeqNo := ⟨fun a b => a.val.toNat ≤ b.val.toNat⟩
instance : DecidableLT SeqNo := fun a b => inferInstanceAs (Decidable (a.val.toNat < b.val.toNat))
instance : DecidableLE SeqNo := fun a b => inferInstanceAs (Decidable (a.val.toNat ≤ b.val.toNat))
instance : TransOrd SeqNo := transCmp_of_natProj (fun x : SeqNo => x.val.toNat)
instance : LawfulEqOrd SeqNo :=
  lawfulEqCmp_of_natProj (fun x : SeqNo => x.val.toNat) (fun {a b} h => by
    cases a; cases b; simp only at h; congr 1; exact UInt64.toNat_inj.mp h)
end SeqNo

/-- Object pack segment identifier (1-indexed). -/
structure SegmentId where
  val : UInt64
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace SegmentId
instance : Ord SegmentId := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : LT SegmentId := ⟨fun a b => a.val.toNat < b.val.toNat⟩
instance : LE SegmentId := ⟨fun a b => a.val.toNat ≤ b.val.toNat⟩
instance : DecidableLT SegmentId := fun a b => inferInstanceAs (Decidable (a.val.toNat < b.val.toNat))
instance : DecidableLE SegmentId := fun a b => inferInstanceAs (Decidable (a.val.toNat ≤ b.val.toNat))
instance : TransOrd SegmentId := transCmp_of_natProj (fun x : SegmentId => x.val.toNat)
instance : LawfulEqOrd SegmentId :=
  lawfulEqCmp_of_natProj (fun x : SegmentId => x.val.toNat) (fun {a b} h => by
    cases a; cases b; simp only at h; congr 1; exact UInt64.toNat_inj.mp h)
end SegmentId

/-- Disambiguation tag for distinct payloads sharing a SHA-256 digest. -/
structure CollisionTag where
  val : UInt64
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace CollisionTag
instance : Ord CollisionTag := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : TransOrd CollisionTag := transCmp_of_natProj (fun x : CollisionTag => x.val.toNat)
instance : LawfulEqOrd CollisionTag :=
  lawfulEqCmp_of_natProj (fun x : CollisionTag => x.val.toNat) (fun {a b} h => by
    cases a; cases b; simp only at h; congr 1; exact UInt64.toNat_inj.mp h)
end CollisionTag

/-- Fixed 32-byte SHA-256 digest. -/
structure Sha256Digest where
  bytes   : ByteArray
  size_eq : bytes.size = 32

namespace Sha256Digest

private theorem eq_of_bytes_eq {a b : Sha256Digest} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

instance : DecidableEq Sha256Digest := fun a b =>
  if h : a.bytes = b.bytes then isTrue (eq_of_bytes_eq h)
  else isFalse (fun hab => h (hab ▸ rfl))

instance : BEq Sha256Digest := ⟨fun a b => a.bytes == b.bytes⟩

instance : Inhabited Sha256Digest where
  default := ⟨ByteArray.mk (Array.replicate 32 0), by simp [ByteArray.size]⟩

instance : Hashable Sha256Digest where
  hash d := Id.run do
    let mut h : UInt64 := 14695981039346656037
    for b in d.bytes.data do
      h := (h ^^^ b.toUInt64) * 1099511628211
    return h

private def cmpBytes (a b : ByteArray) : Ordering :=
  compare (a.data.map (·.toNat)) (b.data.map (·.toNat))

private theorem list_map_toNat_inj : ∀ {xs ys : List UInt8},
    xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [] => fun _ => rfl
  | _ :: _, [] => fun h => by simp at h
  | [], _ :: _ => fun h => by simp at h
  | x :: xs, y :: ys => fun h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [UInt8.toNat_inj.mp h.1, list_map_toNat_inj h.2]

private theorem map_toNat_inj {xs ys : Array UInt8}
    (h : xs.map (·.toNat) = ys.map (·.toNat)) : xs = ys := by
  have hl : (xs.map (·.toNat)).toList = (ys.map (·.toNat)).toList := congrArg Array.toList h
  simp only [Array.toList_map] at hl
  exact Array.ext' (list_map_toNat_inj hl)

instance : Ord Sha256Digest := ⟨fun a b => cmpBytes a.bytes b.bytes⟩

instance : TransOrd Sha256Digest :=
  inferInstanceAs (TransCmp (compareOn (fun d : Sha256Digest => d.bytes.data.map (·.toNat))))

instance : LawfulEqOrd Sha256Digest where
  compare_self {a} := ReflOrd.compare_self (a := a.bytes.data.map (·.toNat))
  eq_of_compare {a b} h := by
    have h1 := LawfulEqOrd.eq_of_compare (α := Array Nat) h
    have h2 : a.bytes.data = b.bytes.data := map_toNat_inj h1
    exact eq_of_bytes_eq (by
      cases ha : a.bytes; cases hb : b.bytes
      simp only [ha, hb] at h2
      congr 1)

/-- Constructs a `Sha256Digest` only when `b.size = 32`. -/
def ofBytes? (b : ByteArray) : Option Sha256Digest :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase 64-character hexadecimal representation. -/
def toHex (d : Sha256Digest) : String := Id.run do
  let mut chars : Array Char := Array.mkEmpty 64
  for b in d.bytes.data do
    chars := chars.push (hexDigit (b >>> 4))
    chars := chars.push (hexDigit (b &&& 0x0F))
  return String.ofList chars.toList

instance : Repr Sha256Digest where
  reprPrec d _ := repr d.toHex

end Sha256Digest

/-- Collision-safe content-addressed object identifier. -/
structure ObjectKey where
  digest : Sha256Digest
  tag    : CollisionTag
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace ObjectKey
def cmp (a b : ObjectKey) : Ordering :=
  compareLex (compareOn (fun x : ObjectKey => x.digest)) (compareOn (fun x : ObjectKey => x.tag)) a b

instance : Ord ObjectKey := ⟨cmp⟩

instance : TransOrd ObjectKey :=
  inferInstanceAs (TransCmp (compareLex (compareOn (fun x : ObjectKey => x.digest)) (compareOn (fun x : ObjectKey => x.tag))))

instance : LawfulEqOrd ObjectKey where
  compare_self {a} := by
    have h1 : Sha256Digest.cmpBytes a.digest.bytes a.digest.bytes = .eq :=
      ReflOrd.compare_self (α := Sha256Digest) (a := a.digest)
    have h2 : compare a.tag.val.toNat a.tag.val.toNat = .eq :=
      ReflOrd.compare_self (α := CollisionTag) (a := a.tag)
    simp only [Ord.compare, cmp, compareLex, compareOn]
    change (Sha256Digest.cmpBytes a.digest.bytes a.digest.bytes).then
      (compare a.tag.val.toNat a.tag.val.toNat) = .eq
    rw [h1, h2]
    rfl
  eq_of_compare {a b} h := by
    simp only [Ord.compare, cmp, compareLex_eq_eq, compareOn] at h
    have hd := LawfulEqOrd.eq_of_compare (α := Sha256Digest) h.1
    have ht := LawfulEqOrd.eq_of_compare (α := CollisionTag) h.2
    cases a; cases b; simp only at hd ht; subst hd; subst ht; rfl
end ObjectKey

/-- Dependent bounded byte span inside a segment of capacity `segmentSize`. -/
structure ObjectLocation (segmentSize : Nat) where
  segment     : SegmentId
  offset      : Nat
  length      : Nat
  nonEmpty    : 0 < length
  validBounds : offset + length ≤ segmentSize
  deriving DecidableEq, Repr

/-- Supported image media formats. -/
inductive MimeType where
  | jpeg
  | png
  | webp
  | gif
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace MimeType

def toTag : MimeType → UInt8
  | .jpeg => 0
  | .png  => 1
  | .webp => 2
  | .gif  => 3

def fromTag? : UInt8 → Option MimeType
  | 0 => some .jpeg
  | 1 => some .png
  | 2 => some .webp
  | 3 => some .gif
  | _ => none

def toString : MimeType → String
  | .jpeg => "image/jpeg"
  | .png  => "image/png"
  | .webp => "image/webp"
  | .gif  => "image/gif"

theorem fromTag?_toTag (m : MimeType) : fromTag? m.toTag = some m := by
  cases m <;> rfl

end MimeType

/-- Sniffs supported image formats from leading magic bytes. -/
def detectMimeType (b : ByteArray) : Option MimeType :=
  if b.size ≥ 8 && (b.extract 0 8).data == #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] then
    some .png
  else if b.size ≥ 3 && (b.extract 0 3).data == #[0xFF, 0xD8, 0xFF] then
    some .jpeg
  else if b.size ≥ 12 && (b.extract 0 4).data == #[0x52, 0x49, 0x46, 0x46] &&
      (b.extract 8 12).data == #[0x57, 0x45, 0x42, 0x50] then
    some .webp
  else if b.size ≥ 6 && ((b.extract 0 6).data == #[0x47, 0x49, 0x46, 0x38, 0x37, 0x61] ||
      (b.extract 0 6).data == #[0x47, 0x49, 0x46, 0x38, 0x39, 0x61]) then
    some .gif
  else
    none

/-- Total descending feed ordering key `(createdAt, id)` breaking same-second ties cleanly. -/
structure FeedKey where
  createdAt : Int64
  id        : PostId
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

namespace FeedKey

def cmpDesc (a b : FeedKey) : Ordering :=
  compareLex
    (fun x y => compare y.createdAt.toInt x.createdAt.toInt)
    (fun x y => compare y.id.val.toNat x.id.val.toNat)
    a b

instance : TransCmp cmpDesc :=
  letI : TransCmp (fun x y : FeedKey => compare y.createdAt.toInt x.createdAt.toInt) :=
    TransCmp.opposite (cmp := compareOn (fun x : FeedKey => x.createdAt.toInt))
  letI : TransCmp (fun x y : FeedKey => compare y.id.val.toNat x.id.val.toNat) :=
    TransCmp.opposite (cmp := compareOn (fun x : FeedKey => x.id.val.toNat))
  inferInstanceAs (TransCmp (compareLex _ _))

private theorem int64_eq_of_toInt_eq {a b : Int64} (h : a.toInt = b.toInt) : a = b := by
  have hbv : a.toBitVec = b.toBitVec := BitVec.eq_of_toInt_eq h
  cases a; cases b
  rename_i ua ub
  cases ua; cases ub
  simp only [Int64.toBitVec] at hbv
  subst hbv
  rfl

instance : LawfulEqCmp cmpDesc where
  compare_self {a} := by
    have hc : compare a.createdAt.toInt a.createdAt.toInt = .eq :=
      ReflOrd.compare_self (α := Int) (a := a.createdAt.toInt)
    have hi : compare a.id.val.toNat a.id.val.toNat = .eq :=
      ReflOrd.compare_self (α := Nat) (a := a.id.val.toNat)
    change (compare a.createdAt.toInt a.createdAt.toInt).then
      (compare a.id.val.toNat a.id.val.toNat) = .eq
    rw [hc, hi]
    rfl
  eq_of_compare {a b} h := by
    cases a with | mk ca ia =>
    cases b with | mk cb ib =>
    change compareLex _ _ (⟨ca, ia⟩ : FeedKey) (⟨cb, ib⟩ : FeedKey) = .eq at h
    rw [compareLex_eq_eq] at h
    have hc : cb.toInt = ca.toInt := LawfulEqOrd.eq_of_compare h.1
    have hi : ib.val.toNat = ia.val.toNat := LawfulEqOrd.eq_of_compare h.2
    have hci : ca = cb := int64_eq_of_toInt_eq hc.symm
    have hii : ia = ib := by
      cases ia; cases ib; simp only at hi; congr 1; exact UInt64.toNat_inj.mp hi.symm
    subst hci; subst hii; rfl

end FeedKey

/-- Binary codec error categories. -/
inductive DecodeError where
  | unexpectedEof
  | invalidUtf8
  | invalidTag
  | invalidMagic
  | unsupportedVersion
  | checksumMismatch
  | lengthMismatch
  | boundsExceeded
  | invariantViolation
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Pure storage engine error categories. -/
inductive CoreError where
  | emptyContent
  | authorTooLong
  | emptyAuthor
  | titleTooLong
  | emptyTitle
  | captionTooLong
  | tooManyTags
  | tagTooLong
  | emptyTag
  | invalidImageSignature
  | imageTooLarge
  | decode (err : DecodeError)
  | postNotFound (id : PostId)
  | duplicatePostId (id : PostId)
  | objectNotFound (key : ObjectKey)
  | segmentFull (seg : SegmentId)
  | txNotActive
  | txAlreadyActive
  | invariantViolated (reason : String)
  deriving DecidableEq, BEq, Repr, Inhabited

end Leaf.Core
