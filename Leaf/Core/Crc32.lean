import Leaf.Core.Bits

namespace Leaf.Core

private def crc32Poly : UInt32 := 0xEDB88320
private def crc32PolyNat : Nat := 0xEDB88320

/-- Single bit step of reflected IEEE 802.3 CRC32. -/
def crc32Step1 (c : UInt32) : UInt32 :=
  (c >>> 1) ^^^ (if (c &&& 1) == 1 then crc32Poly else 0)

/-- `n` bit steps of reflected IEEE 802.3 CRC32. -/
def crc32StepN : Nat → UInt32 → UInt32
  | 0, c => c
  | n + 1, c => crc32Step1 (crc32StepN n c)

def crc32Step8 (c : UInt32) : UInt32 := crc32StepN 8 c

private def crc32SpecLoop (b : ByteArray) (i rem : Nat) (acc : UInt32) : UInt32 :=
  match rem with
  | 0 => acc
  | rem + 1 =>
    let byte := b.get! i
    crc32SpecLoop b (i + 1) rem (crc32Step8 (acc ^^^ byte.toUInt32))

/-- Canonical bitwise IEEE 802.3 CRC32 specification. -/
def crc32Spec (b : ByteArray) : UInt32 :=
  (crc32SpecLoop b 0 b.size 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- Precomputed 256-entry lookup table for byte-wise CRC32. -/
def crc32Table : Array UInt32 :=
  (Array.range 256).map (fun i => crc32Step8 i.toUInt32)

theorem crc32Table_size : crc32Table.size = 256 := by
  simp [crc32Table]

theorem crc32Table_getBang (i : Nat) (hi : i < 256) :
    crc32Table[i]! = crc32Step8 i.toUInt32 := by
  have hlt : i < crc32Table.size := by rw [crc32Table_size]; exact hi
  rw [getElem!_pos crc32Table i hlt]
  simp [crc32Table]

private def crc32FastLoop (b : ByteArray) (i rem : Nat) (acc : UInt32) : UInt32 :=
  match rem with
  | 0 => acc
  | rem + 1 =>
    let byte := b.get! i
    let idx := ((acc ^^^ byte.toUInt32) &&& 0xFF).toNat
    let entry := crc32Table[idx]!
    crc32FastLoop b (i + 1) rem ((acc >>> 8) ^^^ entry)

/-- Fast table-driven IEEE 802.3 CRC32 implementation. -/
def crc32 (b : ByteArray) : UInt32 :=
  (crc32FastLoop b 0 b.size 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-! ### Bit-level Equivalence Proofs -/

private theorem uint32_eq_of_bv {a b : UInt32} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

private theorem uint32_beq_eq_bv (a b : UInt32) : (a == b) = (a.toBitVec == b.toBitVec) := by
  cases a; cases b; rfl

private theorem crc32Step1_bv (c : UInt32) :
    (crc32Step1 c).toBitVec =
      (c.toBitVec >>> 1) ^^^ (if (c.toBitVec &&& 1#32) == 1#32 then crc32Poly.toBitVec else 0#32) := by
  unfold crc32Step1
  have hb : ((c &&& 1) == 1) = (c.toBitVec &&& 1#32 == 1#32) := uint32_beq_eq_bv (c &&& 1) 1
  change (c.toBitVec >>> 1) ^^^ (if ((c &&& 1) == 1) then crc32Poly else 0).toBitVec = _
  rw [hb]
  cases (c.toBitVec &&& 1#32 == 1#32) <;> rfl

private theorem bv_and_one_shiftLeft (q : BitVec 32) (m : Nat) (hm : 0 < m) :
    (q <<< m) &&& 1#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  by_cases hi0 : i = 0
  · subst hi0
    have hlt : ¬ (m ≤ 0) := by omega
    simp [hlt]
  · have h1 : (1#32).getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat]
      have hpow : 2 ≤ 2 ^ i := Nat.le_self_pow hi0 2
      have hval : (1#32).toNat = 1 := rfl
      rw [hval]
      exact Nat.testBit_lt_two_pow (by omega)
    simp [h1]

private theorem bv_shiftLeft_succ_ushiftRight (q : BitVec 32) (m : Nat)
    (hq : q.toNat < 2 ^ 24) (hm : m < 8) :
    (q <<< (m + 1)) >>> 1 = q <<< m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hi1 : i + 1 < 32
  · have hlt1 : 1 + i < 32 := by omega
    have him : (1 + i < m + 1) ↔ (i < m) := by omega
    have hsub : 1 + i - (m + 1) = i - m := by omega
    simp [hi, hlt1, him, hsub]
  · have hi31 : i = 31 := by omega
    subst hi31
    simp only [show ¬ (31 + 1 < 32) by omega, decide_false, Bool.false_and]
    have hge : m ≤ 31 := by omega
    have hlt32 : 31 < 32 := by omega
    have hnot : ¬ (31 < m) := by omega
    simp only [hlt32, hnot, decide_true, decide_false, Bool.true_and, Bool.not_false]
    have hq_bit : q.getLsbD (31 - m) = false := by
      rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat]
      have hpow : 2 ^ 24 ≤ 2 ^ (31 - m) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.testBit_lt_two_pow (by omega)
    exact hq_bit.symm

private theorem bv_step1_shift (q y : BitVec 32) (m : Nat) (hq : q.toNat < 2 ^ 24) (hm : m < 8) :
    let step := fun x : BitVec 32 =>
      (x >>> 1) ^^^ (if (x &&& 1#32) == 1#32 then crc32Poly.toBitVec else 0#32)
    step ((q <<< (m + 1)) ^^^ y) = (q <<< m) ^^^ step y := by
  intro step
  dsimp only [step]
  have hand : (((q <<< (m + 1)) ^^^ y) &&& 1#32) = (y &&& 1#32) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hq0 := congrArg (fun v => v.getLsbD i) (bv_and_one_shiftLeft q (m + 1) (by omega))
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero] at hq0 ⊢
    cases h1 : (1#32).getLsbD i
    · simp
    · simp only [h1, Bool.and_true] at hq0 ⊢
      rw [hq0, Bool.false_xor]
  have hshift : (((q <<< (m + 1)) ^^^ y) >>> 1) = (q <<< m) ^^^ (y >>> 1) := by
    rw [BitVec.ushiftRight_xor_distrib, bv_shiftLeft_succ_ushiftRight q m hq hm]
  rw [hand, hshift, BitVec.xor_assoc]

private theorem crc32StepN_shift (k : Nat) (hk : k ≤ 8) (q y : UInt32) (hq : q.toBitVec.toNat < 2 ^ 24) :
    crc32StepN k (UInt32.ofBitVec ((q.toBitVec <<< 8) ^^^ y.toBitVec)) =
      UInt32.ofBitVec ((q.toBitVec <<< (8 - k)) ^^^ (crc32StepN k y).toBitVec) := by
  induction k with
  | zero =>
    simp [crc32StepN]
  | succ k ih =>
    have hk' : k ≤ 8 := by omega
    have hkm : 7 - k < 8 := by omega
    have h8k : 8 - k = (7 - k) + 1 := by omega
    have h8sk : 8 - (k + 1) = 7 - k := by omega
    rw [crc32StepN, crc32StepN, ih hk']
    apply uint32_eq_of_bv
    rw [crc32Step1_bv, crc32Step1_bv]
    simp only [h8k, h8sk]
    exact bv_step1_shift q.toBitVec (crc32StepN k y).toBitVec (7 - k) hq hkm

private theorem bv_split_8 (x : BitVec 32) :
    x = ((x >>> 8) <<< 8) ^^^ (x &&& 0xFF#32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]
  by_cases hi8 : i < 8
  · have hff : (0xFF#32).getLsbD i = true := by
      rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat]
      have hval : (0xFF#32).toNat = 255 := rfl
      rw [hval]
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
    simp [hi, hi8, hff]
  · have hge : 8 ≤ i := by omega
    have hsub : 8 + (i - 8) = i := by omega
    have hff : (0xFF#32).getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat]
      have hval : (0xFF#32).toNat = 255 := rfl
      rw [hval]
      have hpow : 256 ≤ 2 ^ i := by
        have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hge
        simpa using this
      exact Nat.testBit_lt_two_pow (by omega)
    rw [hff]
    simp [hi, hi8, hsub]

theorem crc32Step8_split (x : UInt32) :
    crc32Step8 x = (x >>> 8) ^^^ crc32Step8 (x &&& 0xFF) := by
  unfold crc32Step8
  have hq : (x >>> 8).toBitVec.toNat < 2 ^ 24 := by
    change (x.toBitVec >>> 8).toNat < 2 ^ 24
    rw [BitVec.toNat_ushiftRight]
    have hlt : x.toBitVec.toNat < 2 ^ 32 := x.toBitVec.isLt
    omega
  have hsplit : x = UInt32.ofBitVec (((x >>> 8).toBitVec <<< 8) ^^^ (x &&& 0xFF).toBitVec) := by
    apply uint32_eq_of_bv
    exact bv_split_8 x.toBitVec
  have hc : crc32StepN 8 x =
      crc32StepN 8 (UInt32.ofBitVec (((x >>> 8).toBitVec <<< 8) ^^^ (x &&& 0xFF).toBitVec)) :=
    congrArg (crc32StepN 8) hsplit
  rw [hc, crc32StepN_shift 8 (by decide) (x >>> 8) (x &&& 0xFF) hq]
  apply uint32_eq_of_bv
  simp only [Nat.sub_self, BitVec.shiftLeft_zero]
  rfl

private theorem crc32Step8_xor_byte (acc b : UInt32) (hb : b.toBitVec.toNat < 256) :
    crc32Step8 (acc ^^^ b) = (acc >>> 8) ^^^ crc32Step8 ((acc ^^^ b) &&& 0xFF) := by
  rw [crc32Step8_split (acc ^^^ b)]
  congr 1
  apply uint32_eq_of_bv
  change ((acc.toBitVec ^^^ b.toBitVec) >>> 8) = (acc.toBitVec >>> 8)
  rw [BitVec.ushiftRight_xor_distrib]
  have hb0 : b.toBitVec >>> 8 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight]
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hb
  rw [hb0, BitVec.xor_zero]

private theorem crc32FastLoop_eq_specLoop (b : ByteArray) (rem i : Nat) (acc : UInt32) :
    crc32FastLoop b i rem acc = crc32SpecLoop b i rem acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    unfold crc32FastLoop crc32SpecLoop
    have hb : ((b.get! i).toUInt32).toBitVec.toNat < 256 := by
      have hlt : (b.get! i).toNat < 256 := (b.get! i).toBitVec.isLt
      exact hlt
    have hstep := crc32Step8_xor_byte acc (b.get! i).toUInt32 hb
    have hidx : ((acc ^^^ (b.get! i).toUInt32) &&& 0xFF).toNat < 256 := by
      change ((acc.toBitVec ^^^ (b.get! i).toUInt32.toBitVec) &&& 0xFF#32).toNat < 256
      rw [BitVec.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have htbl := crc32Table_getBang ((acc ^^^ (b.get! i).toUInt32) &&& 0xFF).toNat hidx
    have hcast : (((acc ^^^ (b.get! i).toUInt32) &&& 0xFF).toNat).toUInt32 =
        ((acc ^^^ (b.get! i).toUInt32) &&& 0xFF) := by
      apply uint32_eq_of_bv
      apply BitVec.eq_of_toNat_eq
      change (((acc ^^^ (b.get! i).toUInt32) &&& 0xFF).toNat) % 2^32 =
        ((acc ^^^ (b.get! i).toUInt32) &&& 0xFF).toNat
      exact Nat.mod_eq_of_lt (Nat.lt_trans hidx (by decide))
    dsimp only
    rw [htbl, hcast, ← hstep]
    exact ih (i + 1) _

/-- Theorem: fast table-driven CRC32 equals the canonical bitwise specification for all byte arrays. -/
theorem crc32_eq_spec (b : ByteArray) : crc32 b = crc32Spec b := by
  simp only [crc32, crc32Spec, crc32FastLoop_eq_specLoop]

/-! ### Pure `Nat` Structural Evaluator for Kernel Test Vector Proof -/

private def crc32Step1Nat (c : Nat) : Nat :=
  if c % 2 == 1 then bitwise4Rec bne 8 (c / 2) crc32PolyNat else c / 2

private theorem crc32Step1Nat_lt (c : Nat) (hc : c < 2 ^ 32) : crc32Step1Nat c < 2 ^ 32 := by
  unfold crc32Step1Nat
  split
  · rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow bne 32 (c / 2) crc32PolyNat
  · omega

private theorem uint32_toNat_ofNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n := by
  change n % 2 ^ 32 = n
  exact Nat.mod_eq_of_lt hn

private theorem crc32Step1Nat_eq (c : UInt32) :
    UInt32.ofNat (crc32Step1Nat c.toNat) = crc32Step1 c := by
  unfold crc32Step1Nat crc32Step1
  have hlt : c.toNat < 2 ^ 32 := c.toBitVec.isLt
  have hsh : UInt32.ofNat (c.toNat / 2) = c >>> 1 := by
    apply UInt32.toNat_inj.mp
    rw [uint32_toNat_ofNat_lt (by omega)]
    change (c.toBitVec >>> 1).toNat = c.toNat / 2
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rfl
  have hbit : (c.toNat % 2 == 1) = ((c &&& 1) == 1) := by
    have h1 : (c &&& 1).toNat = c.toNat % 2 := by
      change (c.toBitVec &&& 1#32).toNat = c.toNat % 2
      rw [BitVec.toNat_and]
      exact Nat.and_one_is_mod c.toNat
    cases h : decide (c.toNat % 2 = 1)
    · have hm : c.toNat % 2 ≠ 1 := of_decide_eq_false h
      have hne : (c &&& 1) ≠ 1 := fun heq => hm (by rw [← h1, heq]; rfl)
      have hbf : ((c &&& 1) == 1) = false := beq_false_of_ne hne
      rw [hbf]
      exact beq_false_of_ne hm
    · have hm : c.toNat % 2 = 1 := of_decide_eq_true h
      have heq : (c &&& 1) = 1 := UInt32.toNat_inj.mp (by rw [h1, hm]; rfl)
      rw [heq]
      simp [hm]
  rw [hbit]
  split
  · have hxor : (c >>> 1) ^^^ crc32Poly = xor32 (c >>> 1) crc32Poly := (xor32_eq _ _).symm
    rw [hxor, ← hsh]
    unfold xor32
    rw [uint32_toNat_ofNat_lt (by omega)]
    rfl
  · rw [hsh]
    change c >>> 1 = c >>> 1 ^^^ 0
    exact (UInt32.xor_zero (a := c >>> 1)).symm

private def crc32Step8Nat : Nat → Nat → Nat
  | 0, c => c
  | n + 1, c => crc32Step1Nat (crc32Step8Nat n c)

private theorem crc32Step8Nat_lt (n c : Nat) (hc : c < 2 ^ 32) : crc32Step8Nat n c < 2 ^ 32 := by
  induction n with
  | zero => exact hc
  | succ n ih => exact crc32Step1Nat_lt _ ih

private theorem crc32Step8Nat_eq (n : Nat) (c : Nat) (hc : c < 2 ^ 32) :
    UInt32.ofNat (crc32Step8Nat n c) = crc32StepN n (UInt32.ofNat c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [crc32Step8Nat, crc32StepN]
    rw [← ih, ← crc32Step1Nat_eq, uint32_toNat_ofNat_lt (crc32Step8Nat_lt n c hc)]

private def crc32LoopListNat (xs : List UInt8) (acc : Nat) : Nat :=
  match xs with
  | [] => acc
  | byte :: rest =>
    crc32LoopListNat rest (crc32Step8Nat 8 (bitwise4Rec bne 8 acc byte.toNat))

private theorem crc32SpecLoop_drop (b : ByteArray) (i rem : Nat) (acc : UInt32)
    (hrem : i + rem = b.size) :
    crc32LoopListNat (b.data.toList.drop i) acc.toNat =
      (crc32SpecLoop b i rem acc).toNat := by
  induction rem generalizing i acc with
  | zero =>
    have hi : i = b.data.size := by change i + 0 = b.data.size at hrem; omega
    have hdrop : b.data.toList.drop i = [] := by
      rw [List.drop_eq_nil_iff, Array.length_toList]
      omega
    rw [hdrop]
    rfl
  | succ rem ih =>
    have hbsize : b.size = b.data.size := rfl
    have hlt : i < b.data.toList.length := by
      rw [Array.length_toList]
      omega
    have hcons : b.data.toList.drop i = b.data.toList[i] :: b.data.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons hlt
    have hget : b.get! i = b.data.toList[i] := by
      cases b with | mk arr =>
      simp only [ByteArray.get!]
      rw [getElem!_pos arr i (by simpa using hlt)]
      rfl
    have hxor : UInt32.ofNat (bitwise4Rec bne 8 acc.toNat (b.get! i).toNat) =
        acc ^^^ (b.get! i).toUInt32 := by
      have hx : UInt32.ofNat (bitwise4Rec bne 8 acc.toNat (b.get! i).toUInt32.toNat) =
          xor32 acc (b.get! i).toUInt32 := rfl
      rw [← xor32_eq]
      exact hx
    have hstep_lt : bitwise4Rec bne 8 acc.toNat (b.get! i).toNat < 2 ^ 32 := by
      rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow bne 32 acc.toNat (b.get! i).toNat
    have hnext : UInt32.ofNat (crc32Step8Nat 8 (bitwise4Rec bne 8 acc.toNat (b.get! i).toNat)) =
        crc32Step8 (acc ^^^ (b.get! i).toUInt32) := by
      rw [crc32Step8Nat_eq 8 _ hstep_lt, hxor]
      rfl
    have hnext_nat : crc32Step8Nat 8 (bitwise4Rec bne 8 acc.toNat (b.get! i).toNat) =
        (crc32Step8 (acc ^^^ (b.get! i).toUInt32)).toNat := by
      rw [← hnext, uint32_toNat_ofNat_lt (crc32Step8Nat_lt 8 _ hstep_lt)]
    rw [hcons, crc32LoopListNat, ← hget, hnext_nat]
    exact ih (i + 1) (crc32Step8 (acc ^^^ (b.get! i).toUInt32)) (by omega)

private theorem crc32LoopListNat_append (xs ys : List UInt8) (acc : Nat) :
    crc32LoopListNat (xs ++ ys) acc = crc32LoopListNat ys (crc32LoopListNat xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, crc32LoopListNat]; exact ih _

def crc32ListEval (xs : List UInt8) : UInt32 :=
  UInt32.ofNat (bitwise4Rec bne 8 (crc32LoopListNat xs 0xFFFFFFFF) 0xFFFFFFFF)

theorem crc32_eq_listEval (b : ByteArray) : crc32 b = crc32ListEval b.data.toList := by
  rw [crc32_eq_spec]
  unfold crc32Spec crc32ListEval
  have hloop := crc32SpecLoop_drop b 0 b.size 0xFFFFFFFF (by omega)
  simp only [List.drop_zero] at hloop
  have hlhs : (crc32SpecLoop b 0 b.size 0xFFFFFFFF) ^^^ 0xFFFFFFFF =
      xor32 (crc32SpecLoop b 0 b.size 0xFFFFFFFF) 0xFFFFFFFF := (xor32_eq _ _).symm
  rw [hlhs]
  unfold xor32
  have hff : (0xFFFFFFFF : UInt32).toNat = 0xFFFFFFFF := rfl
  rw [← hloop, hff]

/-- Standard IEEE CRC32 check value `"123456789"` = `0xCBF43926`. -/
theorem crc32_test_vector :
    crc32 (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) = 0xCBF43926 := by
  rw [crc32_eq_listEval]
  unfold crc32ListEval
  have s1 : crc32Step8Nat 8 (bitwise4Rec bne 8 0xFFFFFFFF (0x31 : UInt8).toNat) = 2082672712 := rfl
  have s2 : crc32Step8Nat 8 (bitwise4Rec bne 8 2082672712 (0x32 : UInt8).toNat) = 2964110130 := rfl
  have s3 : crc32Step8Nat 8 (bitwise4Rec bne 8 2964110130 (0x33 : UInt8).toNat) = 2008521773 := rfl
  have s4 : crc32Step8Nat 8 (bitwise4Rec bne 8 2008521773 (0x34 : UInt8).toNat) = 1679564636 := rfl
  have s5 : crc32Step8Nat 8 (bitwise4Rec bne 8 1679564636 (0x35 : UInt8).toNat) = 873121251 := rfl
  have s6 : crc32Step8Nat 8 (bitwise4Rec bne 8 873121251 (0x36 : UInt8).toNat) = 4136447134 := rfl
  have s7 : crc32Step8Nat 8 (bitwise4Rec bne 8 4136447134 (0x37 : UInt8).toNat) = 2952566368 := rfl
  have s8 : crc32Step8Nat 8 (bitwise4Rec bne 8 2952566368 (0x38 : UInt8).toNat) = 1696539984 := rfl
  have s9 : crc32Step8Nat 8 (bitwise4Rec bne 8 1696539984 (0x39 : UInt8).toNat) = 873187033 := rfl
  change UInt32.ofNat (bitwise4Rec bne 8 (crc32LoopListNat [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] 0xFFFFFFFF) 0xFFFFFFFF) = 0xCBF43926
  rw [crc32LoopListNat, s1, crc32LoopListNat, s2, crc32LoopListNat, s3,
      crc32LoopListNat, s4, crc32LoopListNat, s5, crc32LoopListNat, s6,
      crc32LoopListNat, s7, crc32LoopListNat, s8, crc32LoopListNat, s9]
  rfl

end Leaf.Core
