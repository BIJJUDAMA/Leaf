import Leaf.Core.Types
import Leaf.Core.Schema

namespace Leaf.Core

/-- Total binary encoder returning raw serialized bytes. -/
abbrev Encoder (α : Type) := α → ByteArray

/-- Total cursor-indexed binary decoder advancing position from `pos`. -/
abbrev Decoder (α : Type) := ByteArray → Nat → Except DecodeError (α × Nat)

private def u32MaxPlusOne : Nat := 2 ^ 32

private theorem ByteArray.getElem_append_middle {i : Nat} {pfx mid rest : ByteArray}
    (h : i < mid.size) :
    (pfx ++ mid ++ rest)[pfx.size + i]'(by
      rw [ByteArray.size_append, ByteArray.size_append]; omega) = mid[i] := by
  rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega)]
  rw [ByteArray.getElem_append_right (by omega)]
  have hi : pfx.size + i - pfx.size = i := Nat.add_sub_cancel_left pfx.size i
  simp only [hi]

theorem extract_append_middle (pfx mid rest : ByteArray) :
    (pfx ++ mid ++ rest).extract pfx.size (pfx.size + mid.size) = mid := by
  apply ByteArray.ext
  apply Array.ext
  · change ((pfx ++ mid ++ rest).extract pfx.size (pfx.size + mid.size)).size = mid.size
    rw [ByteArray.size_extract, ByteArray.size_append, ByteArray.size_append]
    omega
  · intro i hi1 hi2
    have him : i < mid.size := hi2
    change ((pfx ++ mid ++ rest).extract pfx.size (pfx.size + mid.size))[i]'(by
      change i < ((pfx ++ mid ++ rest).extract pfx.size (pfx.size + mid.size)).size
      exact hi1) = mid[i]
    rw [ByteArray.getElem_extract]
    exact ByteArray.getElem_append_middle him

theorem decode_at_slice {α : Type} {dec : Decoder α} {ea : ByteArray} {x : α}
    (h : ∀ p r, dec (p ++ ea ++ r) p.size = .ok (x, p.size + ea.size))
    {enc pre post pfx rest : ByteArray}
    (henc : enc = pre ++ ea ++ post) :
    dec (pfx ++ enc ++ rest) (pfx.size + pre.size) =
      .ok (x, pfx.size + pre.size + ea.size) := by
  subst henc
  have hassoc : pfx ++ (pre ++ ea ++ post) ++ rest = (pfx ++ pre) ++ ea ++ (post ++ rest) := by
    simp only [ByteArray.append_assoc]
  rw [hassoc, ← ByteArray.size_append (a := pfx) (b := pre)]
  exact h (pfx ++ pre) (post ++ rest)

theorem decode_at_first {α : Type} {dec : Decoder α} {ea : ByteArray} {x : α}
    (h : ∀ p r, dec (p ++ ea ++ r) p.size = .ok (x, p.size + ea.size))
    {enc post pfx rest : ByteArray}
    (henc : enc = ea ++ post) :
    dec (pfx ++ enc ++ rest) pfx.size = .ok (x, pfx.size + ea.size) := by
  have hr := decode_at_slice h (enc := enc) (pre := ByteArray.empty) (post := post)
    (pfx := pfx) (rest := rest) (by rw [henc, ByteArray.empty_append])
  have he : ByteArray.empty.size = 0 := rfl
  simpa [he] using hr

theorem decode_at_last {α : Type} {dec : Decoder α} {ea : ByteArray} {x : α}
    (h : ∀ p r, dec (p ++ ea ++ r) p.size = .ok (x, p.size + ea.size))
    {enc pre pfx rest : ByteArray}
    (henc : enc = pre ++ ea) :
    dec (pfx ++ enc ++ rest) (pfx.size + pre.size) = .ok (x, pfx.size + pre.size + ea.size) := by
  exact decode_at_slice h (enc := enc) (pre := pre) (post := ByteArray.empty)
    (pfx := pfx) (rest := rest) (by rw [henc, ByteArray.append_empty])

private theorem nat_split_or (x w : Nat) (hx : x < 2 ^ (2 * w)) :
    (x % 2 ^ w) ||| (((x >>> w) % 2 ^ w) <<< w % 2 ^ (2 * w)) = x := by
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [← Nat.pow_add, Nat.two_mul]
  have hp : 0 < 2 ^ w := Nat.pow_pos (by decide)
  have hdiv : x >>> w < 2 ^ w := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [hpow] using hx)
  have hmod : (x >>> w) % 2 ^ w = x >>> w := Nat.mod_eq_of_lt hdiv
  have hshl : (x >>> w) <<< w < 2 ^ (2 * w) := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    calc (x / 2 ^ w) * 2 ^ w ≤ x := Nat.div_mul_le_self x (2 ^ w)
      _ < 2 ^ (2 * w) := hx
  rw [hmod, Nat.mod_eq_of_lt hshl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hiw : i < w
  · have hge : ¬ (w ≤ i) := by omega
    simp [hiw, hge]
  · have hge : w ≤ i := by omega
    have hiw' : ¬ (i < w) := by omega
    have hadd : w + (i - w) = i := by omega
    simp [hiw', hge, hadd]

/-! ### Fixed-Size Integer Codecs -/

def encodeUInt8 (v : UInt8) : ByteArray := ByteArray.mk #[v]

def decodeUInt8At : Decoder UInt8 := fun bytes pos =>
  if h : pos < bytes.size then
    .ok (bytes[pos], pos + 1)
  else
    .error .unexpectedEof

theorem decodeUInt8At_encode_prefix (pfx rest : ByteArray) (v : UInt8) :
    decodeUInt8At (pfx ++ encodeUInt8 v ++ rest) pfx.size =
      .ok (v, pfx.size + (encodeUInt8 v).size) := by
  unfold decodeUInt8At encodeUInt8
  have h1 : (ByteArray.mk #[v]).size = 1 := rfl
  have hlt : pfx.size < (pfx ++ ByteArray.mk #[v] ++ rest).size := by
    rw [ByteArray.size_append, ByteArray.size_append]; omega
  rw [h1]
  split
  · have hb : (pfx ++ ByteArray.mk #[v] ++ rest)[pfx.size]'hlt = v := by
      rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega)]
      rw [ByteArray.getElem_append_right (Nat.le_refl _)]
      simp [Nat.sub_self]
      rfl
    rw [hb]
  · contradiction

def encodeUInt16LE (v : UInt16) : ByteArray :=
  encodeUInt8 v.toUInt8 ++ encodeUInt8 (v >>> 8).toUInt8

def decodeUInt16LEAt : Decoder UInt16 := fun bytes pos => do
  let (b0, pos1) ← decodeUInt8At bytes pos
  let (b1, pos2) ← decodeUInt8At bytes pos1
  return (b0.toUInt16 ||| (b1.toUInt16 <<< 8), pos2)

private theorem u16_reassemble (v : UInt16) :
    v.toUInt8.toUInt16 ||| ((v >>> 8).toUInt8.toUInt16 <<< 8) = v := by
  apply UInt16.toNat_inj.mp
  have hk : (8 : UInt16).toNat % 16 = 8 := by decide
  rw [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt8.toNat_toUInt16,
      UInt16.toNat_toUInt8, UInt16.toNat_toUInt8, hk, UInt16.toNat_shiftRight, hk]
  exact nat_split_or v.toNat 8 v.toBitVec.isLt

theorem decodeUInt16LEAt_encode_prefix (pfx rest : ByteArray) (v : UInt16) :
    decodeUInt16LEAt (pfx ++ encodeUInt16LE v ++ rest) pfx.size =
      .ok (v, pfx.size + (encodeUInt16LE v).size) := by
  let enc := encodeUInt16LE v
  have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 v.toUInt8) (x := v.toUInt8)
    (fun p r => decodeUInt8At_encode_prefix p r v.toUInt8) (enc := enc)
    (post := encodeUInt8 (v >>> 8).toUInt8) (pfx := pfx) (rest := rest) rfl
  have h1 := decode_at_last (dec := decodeUInt8At) (ea := encodeUInt8 (v >>> 8).toUInt8) (x := (v >>> 8).toUInt8)
    (fun p r => decodeUInt8At_encode_prefix p r _) (enc := enc)
    (pre := encodeUInt8 v.toUInt8) (pfx := pfx) (rest := rest) rfl
  simp only [decodeUInt16LEAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [u16_reassemble]
  simp only [encodeUInt16LE, ByteArray.size_append, Nat.add_assoc]

def encodeUInt32LE (v : UInt32) : ByteArray :=
  encodeUInt16LE v.toUInt16 ++ encodeUInt16LE (v >>> 16).toUInt16

def decodeUInt32LEAt : Decoder UInt32 := fun bytes pos => do
  let (lo, pos1) ← decodeUInt16LEAt bytes pos
  let (hi, pos2) ← decodeUInt16LEAt bytes pos1
  return (lo.toUInt32 ||| (hi.toUInt32 <<< 16), pos2)

private theorem u32_reassemble (v : UInt32) :
    v.toUInt16.toUInt32 ||| ((v >>> 16).toUInt16.toUInt32 <<< 16) = v := by
  apply UInt32.toNat_inj.mp
  have hk : (16 : UInt32).toNat % 32 = 16 := by decide
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32,
      UInt32.toNat_toUInt16, UInt32.toNat_toUInt16, hk, UInt32.toNat_shiftRight, hk]
  exact nat_split_or v.toNat 16 v.toBitVec.isLt

theorem decodeUInt32LEAt_encode_prefix (pfx rest : ByteArray) (v : UInt32) :
    decodeUInt32LEAt (pfx ++ encodeUInt32LE v ++ rest) pfx.size =
      .ok (v, pfx.size + (encodeUInt32LE v).size) := by
  let enc := encodeUInt32LE v
  have h0 := decode_at_first (dec := decodeUInt16LEAt) (ea := encodeUInt16LE v.toUInt16) (x := v.toUInt16)
    (fun p r => decodeUInt16LEAt_encode_prefix p r _) (enc := enc)
    (post := encodeUInt16LE (v >>> 16).toUInt16) (pfx := pfx) (rest := rest) rfl
  have h1 := decode_at_last (dec := decodeUInt16LEAt) (ea := encodeUInt16LE (v >>> 16).toUInt16)
    (x := (v >>> 16).toUInt16) (fun p r => decodeUInt16LEAt_encode_prefix p r _) (enc := enc)
    (pre := encodeUInt16LE v.toUInt16) (pfx := pfx) (rest := rest) rfl
  simp only [decodeUInt32LEAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [u32_reassemble]
  simp only [encodeUInt32LE, ByteArray.size_append, Nat.add_assoc]

def encodeUInt64LE (v : UInt64) : ByteArray :=
  encodeUInt32LE v.toUInt32 ++ encodeUInt32LE (v >>> 32).toUInt32

def decodeUInt64LEAt : Decoder UInt64 := fun bytes pos => do
  let (lo, pos1) ← decodeUInt32LEAt bytes pos
  let (hi, pos2) ← decodeUInt32LEAt bytes pos1
  return (lo.toUInt64 ||| (hi.toUInt64 <<< 32), pos2)

private theorem u64_reassemble (v : UInt64) :
    v.toUInt32.toUInt64 ||| ((v >>> 32).toUInt32.toUInt64 <<< 32) = v := by
  apply UInt64.toNat_inj.mp
  have hk : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
      UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, hk, UInt64.toNat_shiftRight, hk]
  exact nat_split_or v.toNat 32 v.toBitVec.isLt

theorem decodeUInt64LEAt_encode_prefix (pfx rest : ByteArray) (v : UInt64) :
    decodeUInt64LEAt (pfx ++ encodeUInt64LE v ++ rest) pfx.size =
      .ok (v, pfx.size + (encodeUInt64LE v).size) := by
  let enc := encodeUInt64LE v
  have h0 := decode_at_first (dec := decodeUInt32LEAt) (ea := encodeUInt32LE v.toUInt32) (x := v.toUInt32)
    (fun p r => decodeUInt32LEAt_encode_prefix p r _) (enc := enc)
    (post := encodeUInt32LE (v >>> 32).toUInt32) (pfx := pfx) (rest := rest) rfl
  have h1 := decode_at_last (dec := decodeUInt32LEAt) (ea := encodeUInt32LE (v >>> 32).toUInt32)
    (x := (v >>> 32).toUInt32) (fun p r => decodeUInt32LEAt_encode_prefix p r _) (enc := enc)
    (pre := encodeUInt32LE v.toUInt32) (pfx := pfx) (rest := rest) rfl
  simp only [decodeUInt64LEAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [u64_reassemble]
  simp only [encodeUInt64LE, ByteArray.size_append, Nat.add_assoc]

def encodeInt64LE (v : Int64) : ByteArray :=
  encodeUInt64LE v.toUInt64

def decodeInt64LEAt : Decoder Int64 := fun bytes pos => do
  let (u, pos') ← decodeUInt64LEAt bytes pos
  return (u.toInt64, pos')

theorem decodeInt64LEAt_encode_prefix (pfx rest : ByteArray) (v : Int64) :
    decodeInt64LEAt (pfx ++ encodeInt64LE v ++ rest) pfx.size =
      .ok (v, pfx.size + (encodeInt64LE v).size) := by
  unfold decodeInt64LEAt encodeInt64LE
  have hrt : v.toUInt64.toInt64 = v := by cases v; simp [UInt64.toInt64]
  have hs := decodeUInt64LEAt_encode_prefix pfx rest v.toUInt64
  rw [hs]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hrt]

/-! ### Variable-Length Container Codecs -/

def encodeBytes (b : ByteArray) : ByteArray :=
  encodeUInt32LE b.size.toUInt32 ++ b

def encodeBytesChecked (b : ByteArray) : Except DecodeError ByteArray :=
  if b.size < u32MaxPlusOne then .ok (encodeBytes b) else .error .boundsExceeded

def decodeSliceAt (bytes : ByteArray) (pos len : Nat) : Except DecodeError (ByteArray × Nat) :=
  if pos + len ≤ bytes.size then
    .ok (bytes.extract pos (pos + len), pos + len)
  else
    .error .unexpectedEof

theorem decodeSliceAt_prefix (pfx mid rest : ByteArray) :
    decodeSliceAt (pfx ++ mid ++ rest) pfx.size mid.size =
      .ok (mid, pfx.size + mid.size) := by
  unfold decodeSliceAt
  have hle : pfx.size + mid.size ≤ (pfx ++ mid ++ rest).size := by
    rw [ByteArray.size_append, ByteArray.size_append]; omega
  split
  · rw [extract_append_middle]
  · contradiction

def decodeBytesAt : Decoder ByteArray := fun bytes pos => do
  let (len, pos1) ← decodeUInt32LEAt bytes pos
  decodeSliceAt bytes pos1 len.toNat

theorem decodeBytesAt_encode_prefix (pfx b rest : ByteArray) (hb : b.size < u32MaxPlusOne) :
    decodeBytesAt (pfx ++ encodeBytes b ++ rest) pfx.size =
      .ok (b, pfx.size + (encodeBytes b).size) := by
  have hlen : b.size.toUInt32.toNat = b.size := by
    change b.size % 2 ^ 32 = b.size
    exact Nat.mod_eq_of_lt hb
  have h0 := decode_at_first (dec := decodeUInt32LEAt) (ea := encodeUInt32LE b.size.toUInt32) (x := b.size.toUInt32)
    (fun p r => decodeUInt32LEAt_encode_prefix p r _) (enc := encodeBytes b)
    (post := b) (pfx := pfx) (rest := rest) rfl
  simp only [decodeBytesAt, Bind.bind, Except.bind]
  rw [h0]; dsimp only
  have hsl := decodeSliceAt_prefix (pfx ++ encodeUInt32LE b.size.toUInt32) b rest
  have hassoc : (pfx ++ encodeUInt32LE b.size.toUInt32) ++ b ++ rest = pfx ++ encodeBytes b ++ rest := by
    simp only [encodeBytes, ByteArray.append_assoc]
  rw [hassoc, ByteArray.size_append] at hsl
  rw [hlen, hsl]
  simp only [encodeBytes, ByteArray.size_append, Nat.add_assoc]

def encodeString (s : String) : ByteArray :=
  encodeBytes s.toUTF8

def encodeStringChecked (s : String) : Except DecodeError ByteArray :=
  encodeBytesChecked s.toUTF8

def decodeStringAt : Decoder String := fun bytes pos => do
  let (raw, pos') ← decodeBytesAt bytes pos
  match String.fromUTF8? raw with
  | some s => return (s, pos')
  | none => throw .invalidUtf8

theorem decodeStringAt_encode_prefix (pfx rest : ByteArray) (s : String)
    (hs : s.toUTF8.size < u32MaxPlusOne) :
    decodeStringAt (pfx ++ encodeString s ++ rest) pfx.size =
      .ok (s, pfx.size + (encodeString s).size) := by
  unfold decodeStringAt encodeString
  rw [decodeBytesAt_encode_prefix pfx s.toUTF8 rest hs]
  dsimp only [Bind.bind, Except.bind]
  have hutf : String.fromUTF8? s.toUTF8 = some s := by
    simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]
  rw [hutf]
  rfl

def encodeOptionWith {α : Type} (enc : Encoder α) : Option α → ByteArray
  | none => encodeUInt8 0
  | some x => encodeUInt8 1 ++ enc x

def decodeOptionAt {α : Type} (dec : Decoder α) : Decoder (Option α) := fun bytes pos => do
  let (tag, pos1) ← decodeUInt8At bytes pos
  match tag with
  | 0 => return (none, pos1)
  | 1 =>
    let (x, pos2) ← dec bytes pos1
    return (some x, pos2)
  | _ => throw .invalidTag

theorem decodeOptionAt_encode_prefix {α : Type} (enc : Encoder α) (dec : Decoder α)
    (P : α → Prop)
    (hdec : ∀ x pfx rest, P x → dec (pfx ++ enc x ++ rest) pfx.size = .ok (x, pfx.size + (enc x).size))
    (pfx rest : ByteArray) (opt : Option α) (hopt : ∀ x, opt = some x → P x) :
    decodeOptionAt dec (pfx ++ encodeOptionWith enc opt ++ rest) pfx.size =
      .ok (opt, pfx.size + (encodeOptionWith enc opt).size) := by
  cases opt with
  | none =>
    unfold decodeOptionAt encodeOptionWith
    rw [decodeUInt8At_encode_prefix]
    rfl
  | some x =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 1) (x := 1)
      (fun p r => decodeUInt8At_encode_prefix p r 1) (enc := encodeOptionWith enc (some x))
      (post := enc x) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := dec) (ea := enc x) (x := x)
      (fun p r => hdec x p r (hopt x rfl)) (enc := encodeOptionWith enc (some x))
      (pre := encodeUInt8 1) (pfx := pfx) (rest := rest) rfl
    simp only [decodeOptionAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only
    rw [h1]; dsimp only
    simp only [encodeOptionWith, ByteArray.size_append, Nat.add_assoc]

private def foldEncodeList {α : Type} (enc : Encoder α) (xs : List α) : ByteArray :=
  xs.foldl (fun buf x => buf ++ enc x) ByteArray.empty

private theorem foldEncodeList_cons {α : Type} (enc : Encoder α) (x : α) (xs : List α) :
    foldEncodeList enc (x :: xs) = enc x ++ foldEncodeList enc xs := by
  have hgen : ∀ (ys : List α) (acc : ByteArray),
      ys.foldl (fun buf y => buf ++ enc y) acc = acc ++ ys.foldl (fun buf y => buf ++ enc y) ByteArray.empty := by
    intro ys
    induction ys with
    | nil => intro acc; simp [ByteArray.append_empty]
    | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons, ByteArray.empty_append]
      rw [ih (acc ++ enc y), ih (enc y), ByteArray.append_assoc]
  unfold foldEncodeList
  simp only [List.foldl_cons, ByteArray.empty_append]
  exact hgen xs (enc x)

def encodeArrayWith {α : Type} (enc : Encoder α) (xs : Array α) : ByteArray :=
  encodeUInt32LE xs.size.toUInt32 ++ foldEncodeList enc xs.toList

private def decodeArrayLoop {α : Type} (dec : Decoder α) (rem : Nat) (acc : Array α) : Decoder (Array α) :=
  fun bytes pos =>
    match rem with
    | 0 => .ok (acc, pos)
    | rem + 1 => do
      let (elem, pos') ← dec bytes pos
      decodeArrayLoop dec rem (acc.push elem) bytes pos'

def decodeArrayAt {α : Type} (dec : Decoder α) : Decoder (Array α) := fun bytes pos => do
  let (count, pos1) ← decodeUInt32LEAt bytes pos
  decodeArrayLoop dec count.toNat (Array.mkEmpty count.toNat) bytes pos1

private theorem decodeArrayLoop_encode_list {α : Type} (enc : Encoder α) (dec : Decoder α)
    (P : α → Prop)
    (hdec : ∀ x pfx rest, P x → dec (pfx ++ enc x ++ rest) pfx.size = .ok (x, pfx.size + (enc x).size)) :
    ∀ (xs : List α) (_hxs : ∀ x ∈ xs, P x) (acc : Array α) (pfx rest : ByteArray),
      decodeArrayLoop dec xs.length acc (pfx ++ foldEncodeList enc xs ++ rest) pfx.size =
        .ok (acc ++ xs.toArray, pfx.size + (foldEncodeList enc xs).size)
  | [], _, acc, pfx, rest => by
    unfold decodeArrayLoop foldEncodeList
    simp only [List.length_nil, List.foldl_nil, Array.append_empty]
    change Except.ok (acc, pfx.size) = Except.ok (acc ++ #[], pfx.size + ByteArray.empty.size)
    have he : ByteArray.empty.size = 0 := rfl
    rw [he, Nat.add_zero, Array.append_empty]
  | x :: xs, hxs, acc, pfx, rest => by
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    rw [hlen]
    unfold decodeArrayLoop
    dsimp only
    rw [foldEncodeList_cons]
    have hx : P x := hxs x (by simp)
    have htail : ∀ y ∈ xs, P y := fun y hy => hxs y (by simp [hy])
    have hxDec := decode_at_first (dec := dec) (ea := enc x) (x := x)
      (fun p r => hdec x p r hx) (enc := enc x ++ foldEncodeList enc xs)
      (post := foldEncodeList enc xs) (pfx := pfx) (rest := rest) rfl
    simp only [Bind.bind, Except.bind]
    rw [hxDec]; dsimp only
    have ih := decodeArrayLoop_encode_list enc dec P hdec xs htail (acc.push x) (pfx ++ enc x) rest
    have hassoc : (pfx ++ enc x) ++ foldEncodeList enc xs ++ rest =
        pfx ++ (enc x ++ foldEncodeList enc xs) ++ rest := by
      simp only [ByteArray.append_assoc]
    rw [hassoc, ByteArray.size_append] at ih
    rw [ih]
    have hpush : acc.push x ++ xs.toArray = acc ++ (x :: xs).toArray := by
      have hlist : (x :: xs).toArray = #[x] ++ xs.toArray := by simp
      rw [hlist, ← Array.append_assoc]
      rfl
    rw [hpush, ByteArray.size_append, Nat.add_assoc]

theorem decodeArrayAt_encode_prefix {α : Type} (enc : Encoder α) (dec : Decoder α)
    (P : α → Prop)
    (hdec : ∀ x pfx rest, P x → dec (pfx ++ enc x ++ rest) pfx.size = .ok (x, pfx.size + (enc x).size))
    (pfx rest : ByteArray) (xs : Array α)
    (hsz : xs.size < u32MaxPlusOne) (hxs : ∀ x ∈ xs, P x) :
    decodeArrayAt dec (pfx ++ encodeArrayWith enc xs ++ rest) pfx.size =
      .ok (xs, pfx.size + (encodeArrayWith enc xs).size) := by
  have hcnt : xs.size.toUInt32.toNat = xs.size := by
    change xs.size % 2 ^ 32 = xs.size
    exact Nat.mod_eq_of_lt hsz
  have h0 := decode_at_first (dec := decodeUInt32LEAt) (ea := encodeUInt32LE xs.size.toUInt32)
    (x := xs.size.toUInt32) (fun p r => decodeUInt32LEAt_encode_prefix p r _)
    (enc := encodeArrayWith enc xs) (post := foldEncodeList enc xs.toList)
    (pfx := pfx) (rest := rest) rfl
  simp only [decodeArrayAt, Bind.bind, Except.bind]
  rw [h0]; dsimp only
  rw [hcnt]
  have hxlist : ∀ x ∈ xs.toList, P x := fun x hx => hxs x (Array.mem_def.mpr hx)
  have hloop := decodeArrayLoop_encode_list enc dec P hdec xs.toList hxlist
    (Array.mkEmpty xs.size) (pfx ++ encodeUInt32LE xs.size.toUInt32) rest
  have hassoc : (pfx ++ encodeUInt32LE xs.size.toUInt32) ++ foldEncodeList enc xs.toList ++ rest =
      pfx ++ encodeArrayWith enc xs ++ rest := by
    simp only [encodeArrayWith, ByteArray.append_assoc]
  rw [hassoc, ByteArray.size_append, Array.length_toList] at hloop
  have hemptyArr : Array.mkEmpty (α := α) xs.size ++ xs.toList.toArray = xs := by
    rw [Array.toArray_toList]
    change #[] ++ xs = xs
    exact Array.empty_append
  rw [hloop, hemptyArr]
  simp only [encodeArrayWith, ByteArray.size_append, Nat.add_assoc]

/-! ### Domain Identifier, Metadata, and Record Codecs -/

def encodePostId (id : PostId) : ByteArray := encodeUInt64LE id.val
def decodePostIdAt : Decoder PostId := fun bytes pos => do
  let (v, pos') ← decodeUInt64LEAt bytes pos
  return (⟨v⟩, pos')

theorem decodePostIdAt_encode_prefix (pfx rest : ByteArray) (id : PostId) :
    decodePostIdAt (pfx ++ encodePostId id ++ rest) pfx.size =
      .ok (id, pfx.size + (encodePostId id).size) := by
  cases id with | mk v =>
  unfold decodePostIdAt encodePostId
  rw [decodeUInt64LEAt_encode_prefix]
  rfl

def encodeTxId (id : TxId) : ByteArray := encodeUInt64LE id.val
def decodeTxIdAt : Decoder TxId := fun bytes pos => do
  let (v, pos') ← decodeUInt64LEAt bytes pos
  return (⟨v⟩, pos')

theorem decodeTxIdAt_encode_prefix (pfx rest : ByteArray) (id : TxId) :
    decodeTxIdAt (pfx ++ encodeTxId id ++ rest) pfx.size =
      .ok (id, pfx.size + (encodeTxId id).size) := by
  cases id with | mk v =>
  unfold decodeTxIdAt encodeTxId
  rw [decodeUInt64LEAt_encode_prefix]
  rfl

def encodeSeqNo (s : SeqNo) : ByteArray := encodeUInt64LE s.val
def decodeSeqNoAt : Decoder SeqNo := fun bytes pos => do
  let (v, pos') ← decodeUInt64LEAt bytes pos
  return (⟨v⟩, pos')

theorem decodeSeqNoAt_encode_prefix (pfx rest : ByteArray) (s : SeqNo) :
    decodeSeqNoAt (pfx ++ encodeSeqNo s ++ rest) pfx.size =
      .ok (s, pfx.size + (encodeSeqNo s).size) := by
  cases s with | mk v =>
  unfold decodeSeqNoAt encodeSeqNo
  rw [decodeUInt64LEAt_encode_prefix]
  rfl

def encodeSegmentId (id : SegmentId) : ByteArray := encodeUInt64LE id.val
def decodeSegmentIdAt : Decoder SegmentId := fun bytes pos => do
  let (v, pos') ← decodeUInt64LEAt bytes pos
  return (⟨v⟩, pos')

theorem decodeSegmentIdAt_encode_prefix (pfx rest : ByteArray) (id : SegmentId) :
    decodeSegmentIdAt (pfx ++ encodeSegmentId id ++ rest) pfx.size =
      .ok (id, pfx.size + (encodeSegmentId id).size) := by
  cases id with | mk v =>
  unfold decodeSegmentIdAt encodeSegmentId
  rw [decodeUInt64LEAt_encode_prefix]
  rfl

def encodeCollisionTag (tag : CollisionTag) : ByteArray := encodeUInt64LE tag.val
def decodeCollisionTagAt : Decoder CollisionTag := fun bytes pos => do
  let (v, pos') ← decodeUInt64LEAt bytes pos
  return (⟨v⟩, pos')

theorem decodeCollisionTagAt_encode_prefix (pfx rest : ByteArray) (tag : CollisionTag) :
    decodeCollisionTagAt (pfx ++ encodeCollisionTag tag ++ rest) pfx.size =
      .ok (tag, pfx.size + (encodeCollisionTag tag).size) := by
  cases tag with | mk v =>
  unfold decodeCollisionTagAt encodeCollisionTag
  rw [decodeUInt64LEAt_encode_prefix]
  rfl

def encodeSha256Digest (d : Sha256Digest) : ByteArray := d.bytes

def decodeSha256DigestAt : Decoder Sha256Digest := fun bytes pos => do
  let (raw, pos') ← decodeSliceAt bytes pos 32
  match Sha256Digest.ofBytes? raw with
  | some d => return (d, pos')
  | none => throw .lengthMismatch

private theorem sha256Digest_ofBytes_self (bs : ByteArray) (hsz : bs.size = 32) :
    Sha256Digest.ofBytes? bs = some ⟨bs, hsz⟩ := by
  unfold Sha256Digest.ofBytes?
  split
  · rfl
  · contradiction

theorem decodeSha256DigestAt_encode_prefix (pfx rest : ByteArray) (d : Sha256Digest) :
    decodeSha256DigestAt (pfx ++ encodeSha256Digest d ++ rest) pfx.size =
      .ok (d, pfx.size + (encodeSha256Digest d).size) := by
  cases d with | mk bs hsz =>
  unfold decodeSha256DigestAt encodeSha256Digest
  have hsl : decodeSliceAt (pfx ++ bs ++ rest) pfx.size 32 = .ok (bs, pfx.size + bs.size) := by
    have h0 := decodeSliceAt_prefix pfx bs rest
    simpa [hsz] using h0
  rw [hsl]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [sha256Digest_ofBytes_self bs hsz]

def encodeObjectKey (k : ObjectKey) : ByteArray :=
  encodeSha256Digest k.digest ++ encodeCollisionTag k.tag

def decodeObjectKeyAt : Decoder ObjectKey := fun bytes pos => do
  let (digest, pos1) ← decodeSha256DigestAt bytes pos
  let (tag, pos2) ← decodeCollisionTagAt bytes pos1
  return ({ digest, tag }, pos2)

theorem decodeObjectKeyAt_encode_prefix (pfx rest : ByteArray) (k : ObjectKey) :
    decodeObjectKeyAt (pfx ++ encodeObjectKey k ++ rest) pfx.size =
      .ok (k, pfx.size + (encodeObjectKey k).size) := by
  cases k with | mk d t =>
  let enc := encodeObjectKey ⟨d, t⟩
  have h0 := decode_at_first (dec := decodeSha256DigestAt) (ea := encodeSha256Digest d) (x := d)
    (fun p r => decodeSha256DigestAt_encode_prefix p r d) (enc := enc)
    (post := encodeCollisionTag t) (pfx := pfx) (rest := rest) rfl
  have h1 := decode_at_last (dec := decodeCollisionTagAt) (ea := encodeCollisionTag t) (x := t)
    (fun p r => decodeCollisionTagAt_encode_prefix p r t) (enc := enc)
    (pre := encodeSha256Digest d) (pfx := pfx) (rest := rest) rfl
  simp only [decodeObjectKeyAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  simp only [encodeObjectKey, ByteArray.size_append, Nat.add_assoc]

def encodeMimeType (m : MimeType) : ByteArray := encodeUInt8 m.toTag

def decodeMimeTypeAt : Decoder MimeType := fun bytes pos => do
  let (tag, pos1) ← decodeUInt8At bytes pos
  match MimeType.fromTag? tag with
  | some m => return (m, pos1)
  | none => throw .invalidTag

theorem decodeMimeTypeAt_encode_prefix (pfx rest : ByteArray) (m : MimeType) :
    decodeMimeTypeAt (pfx ++ encodeMimeType m ++ rest) pfx.size =
      .ok (m, pfx.size + (encodeMimeType m).size) := by
  unfold decodeMimeTypeAt encodeMimeType
  rw [decodeUInt8At_encode_prefix]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [MimeType.fromTag?_toTag m]

def encodeImageRef (r : ImageRef) : ByteArray :=
  encodeObjectKey r.key ++ encodeMimeType r.mime ++ encodeUInt32LE r.byteSize

def decodeImageRefAt : Decoder ImageRef := fun bytes pos => do
  let (key, pos1) ← decodeObjectKeyAt bytes pos
  let (mime, pos2) ← decodeMimeTypeAt bytes pos1
  let (byteSize, pos3) ← decodeUInt32LEAt bytes pos2
  return ({ key, mime, byteSize }, pos3)

theorem decodeImageRefAt_encode_prefix (pfx rest : ByteArray) (r : ImageRef) :
    decodeImageRefAt (pfx ++ encodeImageRef r ++ rest) pfx.size =
      .ok (r, pfx.size + (encodeImageRef r).size) := by
  cases r with | mk key mime byteSize =>
  let enc := encodeImageRef ⟨key, mime, byteSize⟩
  have h0 := decode_at_first (dec := decodeObjectKeyAt) (ea := encodeObjectKey key) (x := key)
    (fun p r => decodeObjectKeyAt_encode_prefix p r key) (enc := enc)
    (post := encodeMimeType mime ++ encodeUInt32LE byteSize) (pfx := pfx) (rest := rest)
    (by simp only [encodeImageRef, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeMimeTypeAt) (ea := encodeMimeType mime) (x := mime)
    (fun p r => decodeMimeTypeAt_encode_prefix p r mime) (enc := enc)
    (pre := encodeObjectKey key) (post := encodeUInt32LE byteSize) (pfx := pfx) (rest := rest) rfl
  have h2 := decode_at_last (dec := decodeUInt32LEAt) (ea := encodeUInt32LE byteSize) (x := byteSize)
    (fun p r => decodeUInt32LEAt_encode_prefix p r byteSize) (enc := enc)
    (pre := encodeObjectKey key ++ encodeMimeType mime) (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2
  simp only [decodeImageRefAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  simp only [encodeImageRef, ByteArray.size_append, Nat.add_assoc]

/-- 32-bit encodability invariant for `Post` fields. -/
def Post.Fits32 (p : Post) : Prop :=
  p.author.toUTF8.size < u32MaxPlusOne ∧
  (∀ t, p.title = some t → t.toUTF8.size < u32MaxPlusOne) ∧
  p.caption.toUTF8.size < u32MaxPlusOne ∧
  p.tags.size < u32MaxPlusOne ∧
  (∀ tg ∈ p.tags, tg.toUTF8.size < u32MaxPlusOne)

def encodePost (p : Post) : ByteArray :=
  encodePostId p.id ++
  encodeString p.author ++
  encodeOptionWith encodeString p.title ++
  encodeString p.caption ++
  encodeArrayWith encodeString p.tags ++
  encodeInt64LE p.createdAt ++
  encodeOptionWith encodeInt64LE p.updatedAt ++
  encodeSeqNo p.version ++
  encodeOptionWith encodeImageRef p.image

def decodePostAt : Decoder Post := fun bytes pos => do
  let (id, pos1) ← decodePostIdAt bytes pos
  let (author, pos2) ← decodeStringAt bytes pos1
  let (title, pos3) ← decodeOptionAt decodeStringAt bytes pos2
  let (caption, pos4) ← decodeStringAt bytes pos3
  let (tags, pos5) ← decodeArrayAt decodeStringAt bytes pos4
  let (createdAt, pos6) ← decodeInt64LEAt bytes pos5
  let (updatedAt, pos7) ← decodeOptionAt decodeInt64LEAt bytes pos6
  let (version, pos8) ← decodeSeqNoAt bytes pos7
  let (image, pos9) ← decodeOptionAt decodeImageRefAt bytes pos8
  return ({ id, author, title, caption, tags, createdAt, updatedAt, version, image }, pos9)

theorem decodePostAt_encode_prefix (pfx rest : ByteArray) (p : Post) (hp : p.Fits32) :
    decodePostAt (pfx ++ encodePost p ++ rest) pfx.size =
      .ok (p, pfx.size + (encodePost p).size) := by
  rcases hp with ⟨hAuth, hTit, hCap, hTagsSz, hTagsMem⟩
  cases p with | mk id author title caption tags createdAt updatedAt version image =>
  dsimp only at hAuth hTit hCap hTagsSz hTagsMem
  let enc := encodePost { id, author, title, caption, tags, createdAt, updatedAt, version, image }
  let f0 := encodePostId id
  let f1 := encodeString author
  let f2 := encodeOptionWith encodeString title
  let f3 := encodeString caption
  let f4 := encodeArrayWith encodeString tags
  let f5 := encodeInt64LE createdAt
  let f6 := encodeOptionWith encodeInt64LE updatedAt
  let f7 := encodeSeqNo version
  let f8 := encodeOptionWith encodeImageRef image
  have h0 := decode_at_first (dec := decodePostIdAt) (ea := f0) (x := id)
    (fun pr rr => decodePostIdAt_encode_prefix pr rr id) (enc := enc)
    (post := f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeStringAt) (ea := f1) (x := author)
    (fun pr rr => decodeStringAt_encode_prefix pr rr author hAuth) (enc := enc)
    (pre := f0) (post := f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h2 := decode_at_slice (dec := decodeOptionAt decodeStringAt) (ea := f2) (x := title)
    (fun pr rr => decodeOptionAt_encode_prefix encodeString decodeStringAt (fun s => s.toUTF8.size < u32MaxPlusOne)
      (fun x px rx hx => decodeStringAt_encode_prefix px rx x hx) pr rr title hTit) (enc := enc)
    (pre := f0 ++ f1) (post := f3 ++ f4 ++ f5 ++ f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h3 := decode_at_slice (dec := decodeStringAt) (ea := f3) (x := caption)
    (fun pr rr => decodeStringAt_encode_prefix pr rr caption hCap) (enc := enc)
    (pre := f0 ++ f1 ++ f2) (post := f4 ++ f5 ++ f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h4 := decode_at_slice (dec := decodeArrayAt decodeStringAt) (ea := f4) (x := tags)
    (fun pr rr => decodeArrayAt_encode_prefix encodeString decodeStringAt (fun s => s.toUTF8.size < u32MaxPlusOne)
      (fun x px rx hx => decodeStringAt_encode_prefix px rx x hx) pr rr tags hTagsSz hTagsMem) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3) (post := f5 ++ f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h5 := decode_at_slice (dec := decodeInt64LEAt) (ea := f5) (x := createdAt)
    (fun pr rr => decodeInt64LEAt_encode_prefix pr rr createdAt) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4) (post := f6 ++ f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h6 := decode_at_slice (dec := decodeOptionAt decodeInt64LEAt) (ea := f6) (x := updatedAt)
    (fun pr rr => decodeOptionAt_encode_prefix encodeInt64LE decodeInt64LEAt (fun _ => True)
      (fun x px rx _ => decodeInt64LEAt_encode_prefix px rx x) pr rr updatedAt (fun _ _ => trivial)) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5) (post := f7 ++ f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h7 := decode_at_slice (dec := decodeSeqNoAt) (ea := f7) (x := version)
    (fun pr rr => decodeSeqNoAt_encode_prefix pr rr version) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6) (post := f8)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  have h8 := decode_at_last (dec := decodeOptionAt decodeImageRefAt) (ea := f8) (x := image)
    (fun pr rr => decodeOptionAt_encode_prefix encodeImageRef decodeImageRefAt (fun _ => True)
      (fun x px rx _ => decodeImageRefAt_encode_prefix px rx x) pr rr image (fun _ _ => trivial)) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ f7)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, enc, ByteArray.append_assoc])
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [decodePostAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  rw [h4]; dsimp only
  rw [h5]; dsimp only
  rw [h6]; dsimp only
  rw [h7]; dsimp only
  rw [h8]; dsimp only
  simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, encodePost, ByteArray.size_append, Nat.add_assoc]

def encodePostChecked (p : Post) : Except DecodeError ByteArray :=
  if _h1 : p.author.toUTF8.size < u32MaxPlusOne then
    if _h2 : (p.title.map (fun t => t.toUTF8.size)).getD 0 < u32MaxPlusOne then
      if _h3 : p.caption.toUTF8.size < u32MaxPlusOne then
        if _h4 : p.tags.size < u32MaxPlusOne then
          if _h5 : p.tags.all (fun t => decide (t.toUTF8.size < u32MaxPlusOne)) then
            .ok (encodePost p)
          else .error .boundsExceeded
        else .error .boundsExceeded
      else .error .boundsExceeded
    else .error .boundsExceeded
  else .error .boundsExceeded

theorem encodePostChecked_ok {p : Post} {enc : ByteArray} (h : encodePostChecked p = .ok enc) :
    p.Fits32 ∧ enc = encodePost p := by
  unfold encodePostChecked at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i h1 h2 h3 h4 h5
  simp only [Except.ok.injEq] at h
  refine ⟨⟨h1, ?_, h3, h4, ?_⟩, h.symm⟩
  · intro t ht; rw [ht] at h2; simpa using h2
  · intro tg hmem
    rw [Array.all_eq_true] at h5
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hmem
    exact of_decide_eq_true (h5 i hi)

def encodeRawObjectLocation (loc : RawObjectLocation) : ByteArray :=
  encodeSegmentId loc.segment ++ encodeUInt64LE loc.offset ++ encodeUInt32LE loc.length

def decodeRawObjectLocationAt : Decoder RawObjectLocation := fun bytes pos => do
  let (segment, pos1) ← decodeSegmentIdAt bytes pos
  let (offset, pos2) ← decodeUInt64LEAt bytes pos1
  let (length, pos3) ← decodeUInt32LEAt bytes pos2
  return ({ segment, offset, length }, pos3)

theorem decodeRawObjectLocationAt_encode_prefix (pfx rest : ByteArray) (loc : RawObjectLocation) :
    decodeRawObjectLocationAt (pfx ++ encodeRawObjectLocation loc ++ rest) pfx.size =
      .ok (loc, pfx.size + (encodeRawObjectLocation loc).size) := by
  cases loc with | mk seg off len =>
  let enc := encodeRawObjectLocation ⟨seg, off, len⟩
  have h0 := decode_at_first (dec := decodeSegmentIdAt) (ea := encodeSegmentId seg) (x := seg)
    (fun p r => decodeSegmentIdAt_encode_prefix p r seg) (enc := enc)
    (post := encodeUInt64LE off ++ encodeUInt32LE len)
    (pfx := pfx) (rest := rest) (by simp only [encodeRawObjectLocation, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeUInt64LEAt) (ea := encodeUInt64LE off) (x := off)
    (fun p r => decodeUInt64LEAt_encode_prefix p r off) (enc := enc)
    (pre := encodeSegmentId seg) (post := encodeUInt32LE len)
    (pfx := pfx) (rest := rest) rfl
  have h2 := decode_at_last (dec := decodeUInt32LEAt) (ea := encodeUInt32LE len) (x := len)
    (fun p r => decodeUInt32LEAt_encode_prefix p r len) (enc := enc)
    (pre := encodeSegmentId seg ++ encodeUInt64LE off)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2
  simp only [decodeRawObjectLocationAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  simp only [encodeRawObjectLocation, ByteArray.size_append, Nat.add_assoc]

def encodeWalBucketEntry (e : WalBucketEntry) : ByteArray :=
  encodeObjectKey e.key ++ encodeRawObjectLocation e.location ++ encodeMimeType e.mime ++ encodeUInt32LE e.crc32

def decodeWalBucketEntryAt : Decoder WalBucketEntry := fun bytes pos => do
  let (key, pos1) ← decodeObjectKeyAt bytes pos
  let (location, pos2) ← decodeRawObjectLocationAt bytes pos1
  let (mime, pos3) ← decodeMimeTypeAt bytes pos2
  let (crc32, pos4) ← decodeUInt32LEAt bytes pos3
  return ({ key, location, mime, crc32 }, pos4)

theorem decodeWalBucketEntryAt_encode_prefix (pfx rest : ByteArray) (e : WalBucketEntry) :
    decodeWalBucketEntryAt (pfx ++ encodeWalBucketEntry e ++ rest) pfx.size =
      .ok (e, pfx.size + (encodeWalBucketEntry e).size) := by
  cases e with | mk key location mime crc32 =>
  let enc := encodeWalBucketEntry ⟨key, location, mime, crc32⟩
  have h0 := decode_at_first (dec := decodeObjectKeyAt) (ea := encodeObjectKey key) (x := key)
    (fun p r => decodeObjectKeyAt_encode_prefix p r key) (enc := enc)
    (post := encodeRawObjectLocation location ++ encodeMimeType mime ++ encodeUInt32LE crc32)
    (pfx := pfx) (rest := rest) (by simp only [encodeWalBucketEntry, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeRawObjectLocationAt) (ea := encodeRawObjectLocation location) (x := location)
    (fun p r => decodeRawObjectLocationAt_encode_prefix p r location) (enc := enc)
    (pre := encodeObjectKey key) (post := encodeMimeType mime ++ encodeUInt32LE crc32)
    (pfx := pfx) (rest := rest) (by simp only [encodeWalBucketEntry, enc, ByteArray.append_assoc])
  have h2 := decode_at_slice (dec := decodeMimeTypeAt) (ea := encodeMimeType mime) (x := mime)
    (fun p r => decodeMimeTypeAt_encode_prefix p r mime) (enc := enc)
    (pre := encodeObjectKey key ++ encodeRawObjectLocation location) (post := encodeUInt32LE crc32)
    (pfx := pfx) (rest := rest) rfl
  have h3 := decode_at_last (dec := decodeUInt32LEAt) (ea := encodeUInt32LE crc32) (x := crc32)
    (fun p r => decodeUInt32LEAt_encode_prefix p r crc32) (enc := enc)
    (pre := encodeObjectKey key ++ encodeRawObjectLocation location ++ encodeMimeType mime)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2 h3
  simp only [decodeWalBucketEntryAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  simp only [encodeWalBucketEntry, ByteArray.size_append, Nat.add_assoc]

/-- 32-bit encodability invariant for `WalOp`. -/
def WalOp.Fits32 : WalOp → Prop
  | .putPost p => p.Fits32
  | .updatePost p => p.Fits32
  | _ => True

def encodeWalOp : WalOp → ByteArray
  | .beginTx => encodeUInt8 0
  | .putPost p => encodeUInt8 1 ++ encodePost p
  | .updatePost p => encodeUInt8 2 ++ encodePost p
  | .deletePost id => encodeUInt8 3 ++ encodePostId id
  | .allocObject e => encodeUInt8 4 ++ encodeWalBucketEntry e
  | .incRef k => encodeUInt8 5 ++ encodeObjectKey k
  | .decRef k => encodeUInt8 6 ++ encodeObjectKey k
  | .commitTx => encodeUInt8 7
  | .abortTx => encodeUInt8 8

def decodeWalOpAt : Decoder WalOp := fun bytes pos => do
  let (tag, pos1) ← decodeUInt8At bytes pos
  match tag with
  | 0 => return (.beginTx, pos1)
  | 1 => let (p, pos2) ← decodePostAt bytes pos1; return (.putPost p, pos2)
  | 2 => let (p, pos2) ← decodePostAt bytes pos1; return (.updatePost p, pos2)
  | 3 => let (id, pos2) ← decodePostIdAt bytes pos1; return (.deletePost id, pos2)
  | 4 => let (e, pos2) ← decodeWalBucketEntryAt bytes pos1; return (.allocObject e, pos2)
  | 5 => let (k, pos2) ← decodeObjectKeyAt bytes pos1; return (.incRef k, pos2)
  | 6 => let (k, pos2) ← decodeObjectKeyAt bytes pos1; return (.decRef k, pos2)
  | 7 => return (.commitTx, pos1)
  | 8 => return (.abortTx, pos1)
  | _ => throw .invalidTag

theorem decodeWalOpAt_encode_prefix (pfx rest : ByteArray) (op : WalOp) (hop : op.Fits32) :
    decodeWalOpAt (pfx ++ encodeWalOp op ++ rest) pfx.size =
      .ok (op, pfx.size + (encodeWalOp op).size) := by
  cases op with
  | beginTx =>
    unfold decodeWalOpAt encodeWalOp; rw [decodeUInt8At_encode_prefix]; rfl
  | commitTx =>
    unfold decodeWalOpAt encodeWalOp; rw [decodeUInt8At_encode_prefix]; rfl
  | abortTx =>
    unfold decodeWalOpAt encodeWalOp; rw [decodeUInt8At_encode_prefix]; rfl
  | putPost p =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 1) (x := 1)
      (fun pr r => decodeUInt8At_encode_prefix pr r 1) (enc := encodeWalOp (.putPost p))
      (post := encodePost p) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodePostAt) (ea := encodePost p) (x := p)
      (fun pr r => decodePostAt_encode_prefix pr r p hop) (enc := encodeWalOp (.putPost p))
      (pre := encodeUInt8 1) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]
  | updatePost p =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 2) (x := 2)
      (fun pr r => decodeUInt8At_encode_prefix pr r 2) (enc := encodeWalOp (.updatePost p))
      (post := encodePost p) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodePostAt) (ea := encodePost p) (x := p)
      (fun pr r => decodePostAt_encode_prefix pr r p hop) (enc := encodeWalOp (.updatePost p))
      (pre := encodeUInt8 2) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]
  | deletePost id =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 3) (x := 3)
      (fun pr r => decodeUInt8At_encode_prefix pr r 3) (enc := encodeWalOp (.deletePost id))
      (post := encodePostId id) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodePostIdAt) (ea := encodePostId id) (x := id)
      (fun pr r => decodePostIdAt_encode_prefix pr r id) (enc := encodeWalOp (.deletePost id))
      (pre := encodeUInt8 3) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]
  | allocObject e =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 4) (x := 4)
      (fun pr r => decodeUInt8At_encode_prefix pr r 4) (enc := encodeWalOp (.allocObject e))
      (post := encodeWalBucketEntry e) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodeWalBucketEntryAt) (ea := encodeWalBucketEntry e) (x := e)
      (fun pr r => decodeWalBucketEntryAt_encode_prefix pr r e) (enc := encodeWalOp (.allocObject e))
      (pre := encodeUInt8 4) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]
  | incRef k =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 5) (x := 5)
      (fun pr r => decodeUInt8At_encode_prefix pr r 5) (enc := encodeWalOp (.incRef k))
      (post := encodeObjectKey k) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodeObjectKeyAt) (ea := encodeObjectKey k) (x := k)
      (fun pr r => decodeObjectKeyAt_encode_prefix pr r k) (enc := encodeWalOp (.incRef k))
      (pre := encodeUInt8 5) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]
  | decRef k =>
    have h0 := decode_at_first (dec := decodeUInt8At) (ea := encodeUInt8 6) (x := 6)
      (fun pr r => decodeUInt8At_encode_prefix pr r 6) (enc := encodeWalOp (.decRef k))
      (post := encodeObjectKey k) (pfx := pfx) (rest := rest) rfl
    have h1 := decode_at_last (dec := decodeObjectKeyAt) (ea := encodeObjectKey k) (x := k)
      (fun pr r => decodeObjectKeyAt_encode_prefix pr r k) (enc := encodeWalOp (.decRef k))
      (pre := encodeUInt8 6) (pfx := pfx) (rest := rest) rfl
    simp only [decodeWalOpAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [h0]; dsimp only; rw [h1]; dsimp only
    simp only [encodeWalOp, ByteArray.size_append, Nat.add_assoc]

def encodeWalOpChecked : WalOp → Except DecodeError ByteArray
  | .putPost p => do let enc ← encodePostChecked p; return (encodeUInt8 1 ++ enc)
  | .updatePost p => do let enc ← encodePostChecked p; return (encodeUInt8 2 ++ enc)
  | op => .ok (encodeWalOp op)

def encodeBucketSegmentRecord (r : BucketSegmentRecord) : ByteArray :=
  encodeObjectKey r.key ++ encodeMimeType r.mime ++ encodeBytes r.payload

def decodeBucketSegmentRecordAt : Decoder BucketSegmentRecord := fun bytes pos => do
  let (key, pos1) ← decodeObjectKeyAt bytes pos
  let (mime, pos2) ← decodeMimeTypeAt bytes pos1
  let (payload, pos3) ← decodeBytesAt bytes pos2
  return ({ key, mime, payload }, pos3)

theorem decodeBucketSegmentRecordAt_encode_prefix (pfx rest : ByteArray) (r : BucketSegmentRecord)
    (hr : r.payload.size < u32MaxPlusOne) :
    decodeBucketSegmentRecordAt (pfx ++ encodeBucketSegmentRecord r ++ rest) pfx.size =
      .ok (r, pfx.size + (encodeBucketSegmentRecord r).size) := by
  cases r with | mk key mime payload =>
  let enc := encodeBucketSegmentRecord ⟨key, mime, payload⟩
  have h0 := decode_at_first (dec := decodeObjectKeyAt) (ea := encodeObjectKey key) (x := key)
    (fun p r => decodeObjectKeyAt_encode_prefix p r key) (enc := enc)
    (post := encodeMimeType mime ++ encodeBytes payload)
    (pfx := pfx) (rest := rest) (by simp only [encodeBucketSegmentRecord, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeMimeTypeAt) (ea := encodeMimeType mime) (x := mime)
    (fun p r => decodeMimeTypeAt_encode_prefix p r mime) (enc := enc)
    (pre := encodeObjectKey key) (post := encodeBytes payload)
    (pfx := pfx) (rest := rest) rfl
  have h2 := decode_at_last (dec := decodeBytesAt) (ea := encodeBytes payload) (x := payload)
    (fun p r => decodeBytesAt_encode_prefix p payload r hr) (enc := enc)
    (pre := encodeObjectKey key ++ encodeMimeType mime)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2
  simp only [decodeBucketSegmentRecordAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  simp only [encodeBucketSegmentRecord, ByteArray.size_append, Nat.add_assoc]

def encodeDbManifest (m : DbManifest) : ByteArray :=
  encodeUInt16LE m.formatVersion ++
  encodeUInt64LE m.latestCheckpointId ++
  encodeUInt64LE m.activeWalId ++
  encodePostId m.nextPostId ++
  encodeTxId m.nextTxId ++
  encodeSeqNo m.lastSeq

def decodeDbManifestAt : Decoder DbManifest := fun bytes pos => do
  let (formatVersion, pos1) ← decodeUInt16LEAt bytes pos
  let (latestCheckpointId, pos2) ← decodeUInt64LEAt bytes pos1
  let (activeWalId, pos3) ← decodeUInt64LEAt bytes pos2
  let (nextPostId, pos4) ← decodePostIdAt bytes pos3
  let (nextTxId, pos5) ← decodeTxIdAt bytes pos4
  let (lastSeq, pos6) ← decodeSeqNoAt bytes pos5
  return ({ formatVersion, latestCheckpointId, activeWalId, nextPostId, nextTxId, lastSeq }, pos6)

theorem decodeDbManifestAt_encode_prefix (pfx rest : ByteArray) (m : DbManifest) :
    decodeDbManifestAt (pfx ++ encodeDbManifest m ++ rest) pfx.size =
      .ok (m, pfx.size + (encodeDbManifest m).size) := by
  cases m with | mk fv lc aw np nt ls =>
  let enc := encodeDbManifest ⟨fv, lc, aw, np, nt, ls⟩
  let f0 := encodeUInt16LE fv
  let f1 := encodeUInt64LE lc
  let f2 := encodeUInt64LE aw
  let f3 := encodePostId np
  let f4 := encodeTxId nt
  let f5 := encodeSeqNo ls
  have h0 := decode_at_first (dec := decodeUInt16LEAt) (ea := f0) (x := fv)
    (fun p r => decodeUInt16LEAt_encode_prefix p r fv) (enc := enc)
    (post := f1 ++ f2 ++ f3 ++ f4 ++ f5)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeUInt64LEAt) (ea := f1) (x := lc)
    (fun p r => decodeUInt64LEAt_encode_prefix p r lc) (enc := enc)
    (pre := f0) (post := f2 ++ f3 ++ f4 ++ f5)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, enc, ByteArray.append_assoc])
  have h2 := decode_at_slice (dec := decodeUInt64LEAt) (ea := f2) (x := aw)
    (fun p r => decodeUInt64LEAt_encode_prefix p r aw) (enc := enc)
    (pre := f0 ++ f1) (post := f3 ++ f4 ++ f5)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, enc, ByteArray.append_assoc])
  have h3 := decode_at_slice (dec := decodePostIdAt) (ea := f3) (x := np)
    (fun p r => decodePostIdAt_encode_prefix p r np) (enc := enc)
    (pre := f0 ++ f1 ++ f2) (post := f4 ++ f5)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, enc, ByteArray.append_assoc])
  have h4 := decode_at_slice (dec := decodeTxIdAt) (ea := f4) (x := nt)
    (fun p r => decodeTxIdAt_encode_prefix p r nt) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3) (post := f5)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, enc, ByteArray.append_assoc])
  have h5 := decode_at_last (dec := decodeSeqNoAt) (ea := f5) (x := ls)
    (fun p r => decodeSeqNoAt_encode_prefix p r ls) (enc := enc)
    (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2 h3 h4 h5
  simp only [decodeDbManifestAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  rw [h4]; dsimp only
  rw [h5]; dsimp only
  simp only [f0, f1, f2, f3, f4, f5, encodeDbManifest, ByteArray.size_append, Nat.add_assoc]

def encodeBucketManifest (m : BucketManifest) : ByteArray :=
  encodeUInt16LE m.formatVersion ++
  encodeUInt64LE m.segmentSize ++
  encodeSegmentId m.activeSegmentId ++
  encodeUInt64LE m.activeSegmentOffset

def decodeBucketManifestAt : Decoder BucketManifest := fun bytes pos => do
  let (formatVersion, pos1) ← decodeUInt16LEAt bytes pos
  let (segmentSize, pos2) ← decodeUInt64LEAt bytes pos1
  let (activeSegmentId, pos3) ← decodeSegmentIdAt bytes pos2
  let (activeSegmentOffset, pos4) ← decodeUInt64LEAt bytes pos3
  return ({ formatVersion, segmentSize, activeSegmentId, activeSegmentOffset }, pos4)

theorem decodeBucketManifestAt_encode_prefix (pfx rest : ByteArray) (m : BucketManifest) :
    decodeBucketManifestAt (pfx ++ encodeBucketManifest m ++ rest) pfx.size =
      .ok (m, pfx.size + (encodeBucketManifest m).size) := by
  cases m with | mk fv ss asid aso =>
  let enc := encodeBucketManifest ⟨fv, ss, asid, aso⟩
  let f0 := encodeUInt16LE fv
  let f1 := encodeUInt64LE ss
  let f2 := encodeSegmentId asid
  let f3 := encodeUInt64LE aso
  have h0 := decode_at_first (dec := decodeUInt16LEAt) (ea := f0) (x := fv)
    (fun p r => decodeUInt16LEAt_encode_prefix p r fv) (enc := enc)
    (post := f1 ++ f2 ++ f3)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, encodeBucketManifest, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeUInt64LEAt) (ea := f1) (x := ss)
    (fun p r => decodeUInt64LEAt_encode_prefix p r ss) (enc := enc)
    (pre := f0) (post := f2 ++ f3)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, encodeBucketManifest, enc, ByteArray.append_assoc])
  have h2 := decode_at_slice (dec := decodeSegmentIdAt) (ea := f2) (x := asid)
    (fun p r => decodeSegmentIdAt_encode_prefix p r asid) (enc := enc)
    (pre := f0 ++ f1) (post := f3)
    (pfx := pfx) (rest := rest) rfl
  have h3 := decode_at_last (dec := decodeUInt64LEAt) (ea := f3) (x := aso)
    (fun p r => decodeUInt64LEAt_encode_prefix p r aso) (enc := enc)
    (pre := f0 ++ f1 ++ f2)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2 h3
  simp only [decodeBucketManifestAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  simp only [f0, f1, f2, f3, encodeBucketManifest, ByteArray.size_append, Nat.add_assoc]

/-- 32-bit encodability invariant for `DbCheckpoint`. -/
def DbCheckpoint.Fits32 (c : DbCheckpoint) : Prop :=
  c.posts.size < u32MaxPlusOne ∧
  (∀ p ∈ c.posts, p.Fits32) ∧
  c.tombstones.size < u32MaxPlusOne

def encodeDbCheckpoint (c : DbCheckpoint) : ByteArray :=
  encodePostId c.nextPostId ++
  encodeSeqNo c.lastSeq ++
  encodeArrayWith encodePost c.posts ++
  encodeArrayWith encodePostId c.tombstones

def decodeDbCheckpointAt : Decoder DbCheckpoint := fun bytes pos => do
  let (nextPostId, pos1) ← decodePostIdAt bytes pos
  let (lastSeq, pos2) ← decodeSeqNoAt bytes pos1
  let (posts, pos3) ← decodeArrayAt decodePostAt bytes pos2
  let (tombstones, pos4) ← decodeArrayAt decodePostIdAt bytes pos3
  return ({ nextPostId, lastSeq, posts, tombstones }, pos4)

theorem decodeDbCheckpointAt_encode_prefix (pfx rest : ByteArray) (c : DbCheckpoint) (hc : c.Fits32) :
    decodeDbCheckpointAt (pfx ++ encodeDbCheckpoint c ++ rest) pfx.size =
      .ok (c, pfx.size + (encodeDbCheckpoint c).size) := by
  rcases hc with ⟨hpSz, hpMem, htSz⟩
  cases c with | mk np ls posts tombstones =>
  dsimp only at hpSz hpMem htSz
  let enc := encodeDbCheckpoint ⟨np, ls, posts, tombstones⟩
  let f0 := encodePostId np
  let f1 := encodeSeqNo ls
  let f2 := encodeArrayWith encodePost posts
  let f3 := encodeArrayWith encodePostId tombstones
  have h0 := decode_at_first (dec := decodePostIdAt) (ea := f0) (x := np)
    (fun p r => decodePostIdAt_encode_prefix p r np) (enc := enc)
    (post := f1 ++ f2 ++ f3)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, encodeDbCheckpoint, enc, ByteArray.append_assoc])
  have h1 := decode_at_slice (dec := decodeSeqNoAt) (ea := f1) (x := ls)
    (fun p r => decodeSeqNoAt_encode_prefix p r ls) (enc := enc)
    (pre := f0) (post := f2 ++ f3)
    (pfx := pfx) (rest := rest) (by simp only [f0, f1, f2, f3, encodeDbCheckpoint, enc, ByteArray.append_assoc])
  have h2 := decode_at_slice (dec := decodeArrayAt decodePostAt) (ea := f2) (x := posts)
    (fun p r => decodeArrayAt_encode_prefix encodePost decodePostAt Post.Fits32
      (fun x px rx hx => decodePostAt_encode_prefix px rx x hx) p r posts hpSz hpMem) (enc := enc)
    (pre := f0 ++ f1) (post := f3)
    (pfx := pfx) (rest := rest) rfl
  have h3 := decode_at_last (dec := decodeArrayAt decodePostIdAt) (ea := f3) (x := tombstones)
    (fun p r => decodeArrayAt_encode_prefix encodePostId decodePostIdAt (fun _ => True)
      (fun x pr' r' _ => decodePostIdAt_encode_prefix pr' r' x) p r tombstones htSz (fun _ _ => trivial)) (enc := enc)
    (pre := f0 ++ f1 ++ f2)
    (pfx := pfx) (rest := rest) rfl
  simp only [ByteArray.size_append, Nat.add_assoc] at h1 h2 h3
  simp only [decodeDbCheckpointAt, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [h0]; dsimp only
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3]; dsimp only
  simp only [f0, f1, f2, f3, encodeDbCheckpoint, ByteArray.size_append, Nat.add_assoc]

end Leaf.Core
