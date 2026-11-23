namespace Leaf.Core

/-- Structural recursion version of `Nat.bitwise` for bounded `k`-bit values, enabling fast kernel reduction. -/
def bitwiseRec (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b =>
    (if f (decide (a % 2 = 1)) (decide (b % 2 = 1)) then 1 else 0) +
      2 * bitwiseRec f k (a / 2) (b / 2)

theorem bitwiseRec_lt_two_pow (f : Bool → Bool → Bool) (k a b : Nat) :
    bitwiseRec f k a b < 2 ^ k := by
  induction k generalizing a b with
  | zero => simp [bitwiseRec]
  | succ k ih =>
    simp only [bitwiseRec, Nat.pow_succ]
    have h1 := ih (a / 2) (b / 2)
    split <;> omega

private theorem testBit_bitwiseRec (f : Bool → Bool → Bool) (hf : f false false = false)
    (k a b i : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (bitwiseRec f k a b).testBit i = f (a.testBit i) (b.testBit i) := by
  induction k generalizing a b i with
  | zero =>
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0
    simp [bitwiseRec, hf]
  | succ k ih =>
    cases i with
    | zero =>
      simp only [bitwiseRec, Nat.testBit_zero]
      split <;> rename_i h
      · simp [h]
      · simp [Bool.eq_false_iff.mpr h]
    | succ i =>
      have ha' : a / 2 < 2 ^ k := by rw [Nat.pow_succ] at ha; omega
      have hb' : b / 2 < 2 ^ k := by rw [Nat.pow_succ] at hb; omega
      simp only [bitwiseRec, Nat.testBit_succ]
      have hdiv : ((if f (decide (a % 2 = 1)) (decide (b % 2 = 1)) then 1 else 0) +
          2 * bitwiseRec f k (a / 2) (b / 2)) / 2 = bitwiseRec f k (a / 2) (b / 2) := by
        split <;> omega
      rw [hdiv]
      exact ih (a / 2) (b / 2) i ha' hb'

theorem nat_bitwise_eq_bitwiseRec (f : Bool → Bool → Bool) (hf : f false false = false)
    (k a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.bitwise f a b = bitwiseRec f k a b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_bitwise hf, testBit_bitwiseRec f hf k a b i ha hb]

theorem nat_xor_eq_bitwiseRec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b = bitwiseRec bne 32 a b :=
  nat_bitwise_eq_bitwiseRec bne rfl 32 a b ha hb

theorem nat_land_eq_bitwiseRec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a &&& b = bitwiseRec and 32 a b :=
  nat_bitwise_eq_bitwiseRec and rfl 32 a b ha hb

theorem nat_lor_eq_bitwiseRec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ||| b = bitwiseRec or 32 a b :=
  nat_bitwise_eq_bitwiseRec or rfl 32 a b ha hb

/-- Four-bit step of `bitwiseRec`, reducing recursion depth 4x for kernel evaluation. -/
def bitwise4Step (f : Bool → Bool → Bool) (a b : Nat) : Nat :=
  (if f (a % 2 == 1) (b % 2 == 1) then 1 else 0) +
  (if f ((a / 2) % 2 == 1) ((b / 2) % 2 == 1) then 2 else 0) +
  (if f ((a / 4) % 2 == 1) ((b / 4) % 2 == 1) then 4 else 0) +
  (if f ((a / 8) % 2 == 1) ((b / 8) % 2 == 1) then 8 else 0)

/-- Depth-8 structural recursion for 32-bit bitwise operations (`k = 8` gives 32 bits). -/
def bitwise4Rec (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => bitwise4Step f a b + 16 * bitwise4Rec f k (a / 16) (b / 16)

private theorem decide_mod_two_eq_beq (n : Nat) : decide (n % 2 = 1) = (n % 2 == 1) := by
  cases h : n % 2 == 1
  · have : n % 2 ≠ 1 := by simp_all
    simp [this]
  · have : n % 2 = 1 := by simp_all
    simp [this]

private theorem bitwiseRec_four (f : Bool → Bool → Bool) (m a b : Nat) :
    bitwiseRec f (m + 4) a b = bitwise4Step f a b + 16 * bitwiseRec f m (a / 16) (b / 16) := by
  simp only [bitwiseRec, bitwise4Step, decide_mod_two_eq_beq]
  have ha2 : (a / 2) / 2 = a / 4 := by omega
  have ha3 : ((a / 2) / 2) / 2 = a / 8 := by omega
  have ha4 : (((a / 2) / 2) / 2) / 2 = a / 16 := by omega
  have hb2 : (b / 2) / 2 = b / 4 := by omega
  have hb3 : ((b / 2) / 2) / 2 = b / 8 := by omega
  have hb4 : (((b / 2) / 2) / 2) / 2 = b / 16 := by omega
  rw [ha4, ha3, ha2, hb4, hb3, hb2]
  cases f (a / 2 % 2 == 1) (b / 2 % 2 == 1) <;>
  cases f (a / 4 % 2 == 1) (b / 4 % 2 == 1) <;>
  cases f (a / 8 % 2 == 1) (b / 8 % 2 == 1) <;>
  simp <;> omega

theorem bitwise4Rec_eq_bitwiseRec (f : Bool → Bool → Bool) (k a b : Nat) :
    bitwise4Rec f k a b = bitwiseRec f (4 * k) a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have h4 : 4 * (k + 1) = 4 * k + 4 := by omega
    rw [h4, bitwiseRec_four, bitwise4Rec, ih (a / 16) (b / 16)]

theorem bitwise4Rec_32_eq (f : Bool → Bool → Bool) (a b : Nat) :
    bitwise4Rec f 8 a b = bitwiseRec f 32 a b :=
  bitwise4Rec_eq_bitwiseRec f 8 a b

theorem nat_xor_eq_bitwise4Rec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b = bitwise4Rec bne 8 a b := by
  rw [nat_xor_eq_bitwiseRec32 ha hb, ← bitwise4Rec_32_eq]

theorem nat_land_eq_bitwise4Rec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a &&& b = bitwise4Rec and 8 a b := by
  rw [nat_land_eq_bitwiseRec32 ha hb, ← bitwise4Rec_32_eq]

theorem nat_lor_eq_bitwise4Rec32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ||| b = bitwise4Rec or 8 a b := by
  rw [nat_lor_eq_bitwiseRec32 ha hb, ← bitwise4Rec_32_eq]

/-- Structural 32-bit XOR on `UInt32` proven equal to `a ^^^ b`. -/
def xor32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (bitwise4Rec bne 8 a.toNat b.toNat)

/-- Structural 32-bit AND on `UInt32` proven equal to `a &&& b`. -/
def and32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (bitwise4Rec and 8 a.toNat b.toNat)

/-- Structural 32-bit OR on `UInt32` proven equal to `a ||| b`. -/
def or32 (a b : UInt32) : UInt32 :=
  UInt32.ofNat (bitwise4Rec or 8 a.toNat b.toNat)

theorem xor32_eq (a b : UInt32) : xor32 a b = a ^^^ b := by
  apply UInt32.toNat_inj.mp
  have ha : a.toNat < 2 ^ 32 := a.toBitVec.isLt
  have hb : b.toNat < 2 ^ 32 := b.toBitVec.isLt
  have hlt : bitwise4Rec bne 8 a.toNat b.toNat < 2 ^ 32 := by
    rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow bne 32 a.toNat b.toNat
  have hl : (xor32 a b).toNat = bitwise4Rec bne 8 a.toNat b.toNat := by
    change (bitwise4Rec bne 8 a.toNat b.toNat) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt hlt
  have hr : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := by
    change (a.toBitVec ^^^ b.toBitVec).toNat = _
    rw [BitVec.toNat_xor]; rfl
  rw [hl, hr, ← nat_xor_eq_bitwise4Rec32 ha hb]

theorem and32_eq (a b : UInt32) : and32 a b = a &&& b := by
  apply UInt32.toNat_inj.mp
  have ha : a.toNat < 2 ^ 32 := a.toBitVec.isLt
  have hb : b.toNat < 2 ^ 32 := b.toBitVec.isLt
  have hlt : bitwise4Rec and 8 a.toNat b.toNat < 2 ^ 32 := by
    rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow and 32 a.toNat b.toNat
  have hl : (and32 a b).toNat = bitwise4Rec and 8 a.toNat b.toNat := by
    change (bitwise4Rec and 8 a.toNat b.toNat) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt hlt
  have hr : (a &&& b).toNat = a.toNat &&& b.toNat := by
    change (a.toBitVec &&& b.toBitVec).toNat = _
    rw [BitVec.toNat_and]; rfl
  rw [hl, hr, ← nat_land_eq_bitwise4Rec32 ha hb]

theorem or32_eq (a b : UInt32) : or32 a b = a ||| b := by
  apply UInt32.toNat_inj.mp
  have ha : a.toNat < 2 ^ 32 := a.toBitVec.isLt
  have hb : b.toNat < 2 ^ 32 := b.toBitVec.isLt
  have hlt : bitwise4Rec or 8 a.toNat b.toNat < 2 ^ 32 := by
    rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow or 32 a.toNat b.toNat
  have hl : (or32 a b).toNat = bitwise4Rec or 8 a.toNat b.toNat := by
    change (bitwise4Rec or 8 a.toNat b.toNat) % 2 ^ 32 = _
    exact Nat.mod_eq_of_lt hlt
  have hr : (a ||| b).toNat = a.toNat ||| b.toNat := by
    change (a.toBitVec ||| b.toBitVec).toNat = _
    rw [BitVec.toNat_or]; rfl
  rw [hl, hr, ← nat_lor_eq_bitwise4Rec32 ha hb]

end Leaf.Core
