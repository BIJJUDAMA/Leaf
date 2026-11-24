import Leaf.Core.Sha256

namespace Leaf.Core

private theorem uint32_toNat_ofNat_lt_s {n : Nat} (hn : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n := by
  change n % 2 ^ 32 = n
  exact Nat.mod_eq_of_lt hn

@[inline] def xorN (a b : Nat) : Nat := bitwise4Rec bne 8 a b
@[inline] def andN (a b : Nat) : Nat := bitwise4Rec and 8 a b
@[inline] def orN (a b : Nat) : Nat := bitwise4Rec or 8 a b
@[inline] def addN (a b : Nat) : Nat := (a + b) % 2 ^ 32
@[inline] def shrN (x n : Nat) : Nat := x / 2 ^ n

private theorem xorN_lt (a b : Nat) : xorN a b < 2 ^ 32 := by
  unfold xorN; rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow bne 32 a b

private theorem andN_lt (a b : Nat) : andN a b < 2 ^ 32 := by
  unfold andN; rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow and 32 a b

private theorem orN_lt (a b : Nat) : orN a b < 2 ^ 32 := by
  unfold orN; rw [bitwise4Rec_32_eq]; exact bitwiseRec_lt_two_pow or 32 a b

private theorem addN_lt (a b : Nat) : addN a b < 2 ^ 32 :=
  Nat.mod_lt _ (by decide)

private theorem shrN_lt (x n : Nat) (hx : x < 2 ^ 32) : shrN x n < 2 ^ 32 := by
  unfold shrN
  have hp : 0 < 2 ^ n := Nat.pow_pos (by decide)
  exact Nat.lt_of_le_of_lt (Nat.div_le_self x (2 ^ n)) hx

private theorem xorN_eq (a b : UInt32) : UInt32.ofNat (xorN a.toNat b.toNat) = a ^^^ b :=
  xor32_eq a b

private theorem andN_eq (a b : UInt32) : UInt32.ofNat (andN a.toNat b.toNat) = a &&& b :=
  and32_eq a b

private theorem orN_eq (a b : UInt32) : UInt32.ofNat (orN a.toNat b.toNat) = a ||| b :=
  or32_eq a b

private theorem xorN_ofNat_eq (a b : Nat) (xa xb : UInt32)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (ea : UInt32.ofNat a = xa) (eb : UInt32.ofNat b = xb) :
    UInt32.ofNat (xorN a b) = xa ^^^ xb := by
  have h := xorN_eq (UInt32.ofNat a) (UInt32.ofNat b)
  rw [uint32_toNat_ofNat_lt_s ha, uint32_toNat_ofNat_lt_s hb, ea, eb] at h
  exact h

private theorem andN_ofNat_eq (a b : Nat) (xa xb : UInt32)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (ea : UInt32.ofNat a = xa) (eb : UInt32.ofNat b = xb) :
    UInt32.ofNat (andN a b) = xa &&& xb := by
  have h := andN_eq (UInt32.ofNat a) (UInt32.ofNat b)
  rw [uint32_toNat_ofNat_lt_s ha, uint32_toNat_ofNat_lt_s hb, ea, eb] at h
  exact h

private theorem orN_ofNat_eq (a b : Nat) (xa xb : UInt32)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (ea : UInt32.ofNat a = xa) (eb : UInt32.ofNat b = xb) :
    UInt32.ofNat (orN a b) = xa ||| xb := by
  have h := orN_eq (UInt32.ofNat a) (UInt32.ofNat b)
  rw [uint32_toNat_ofNat_lt_s ha, uint32_toNat_ofNat_lt_s hb, ea, eb] at h
  exact h

private theorem addN_eq (a b : UInt32) : UInt32.ofNat (addN a.toNat b.toNat) = a + b := by
  apply UInt32.toNat_inj.mp
  rw [uint32_toNat_ofNat_lt_s (addN_lt a.toNat b.toNat)]
  exact (UInt32.toNat_add a b).symm

private theorem shrN_eq (x : UInt32) (n : Nat) (hn : n < 32) :
    UInt32.ofNat (shrN x.toNat n) = x >>> n.toUInt32 := by
  apply UInt32.toNat_inj.mp
  have hx : x.toNat < 2 ^ 32 := x.toBitVec.isLt
  rw [uint32_toNat_ofNat_lt_s (shrN_lt x.toNat n hx), UInt32.toNat_shiftRight]
  have hn32 : n < 2 ^ 32 := by omega
  have hm : n.toUInt32.toNat % 32 = n := by
    change (n % 2 ^ 32) % 32 = n
    rw [Nat.mod_eq_of_lt hn32, Nat.mod_eq_of_lt hn]
  rw [hm, Nat.shiftRight_eq_div_pow]
  rfl

@[inline] def rotrN (x n : Nat) : Nat :=
  orN (x / 2 ^ n) ((x * 2 ^ (32 - n)) % 2 ^ 32)

private theorem rotrN_lt (x n : Nat) : rotrN x n < 2 ^ 32 :=
  orN_lt _ _

private theorem rotrN_eq (x : UInt32) (n : Nat) (hn0 : 0 < n) (hn : n < 32) :
    UInt32.ofNat (rotrN x.toNat n) = rotr32 x n.toUInt32 := by
  unfold rotr32 rotrN
  have hx : x.toNat < 2 ^ 32 := x.toBitVec.isLt
  have h1 : UInt32.ofNat (x.toNat / 2 ^ n) = x >>> n.toUInt32 := shrN_eq x n hn
  have hm_eq : (32 - n.toUInt32).toNat = 32 - n := by
    have hle : n.toUInt32 ≤ (32 : UInt32) := by
      apply UInt32.le_iff_toNat_le.mpr
      have hn32 : n < 2 ^ 32 := by omega
      change n % 2 ^ 32 ≤ 32 % 2 ^ 32
      rw [Nat.mod_eq_of_lt hn32, Nat.mod_eq_of_lt (by decide)]
      omega
    rw [UInt32.toNat_sub_of_le 32 n.toUInt32 hle]
    have hn32 : n < 2 ^ 32 := by omega
    change 32 % 2 ^ 32 - n % 2 ^ 32 = 32 - n
    rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt hn32]
  have h2 : UInt32.ofNat ((x.toNat * 2 ^ (32 - n)) % 2 ^ 32) = x <<< (32 - n.toUInt32) := by
    apply UInt32.toNat_inj.mp
    rw [uint32_toNat_ofNat_lt_s (Nat.mod_lt _ (by decide)), UInt32.toNat_shiftLeft, hm_eq]
    have hmod32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega)
    rw [hmod32, Nat.shiftLeft_eq]
  exact orN_ofNat_eq (x.toNat / 2 ^ n) ((x.toNat * 2 ^ (32 - n)) % 2 ^ 32) _ _
    (shrN_lt x.toNat n hx) (Nat.mod_lt _ (by decide)) h1 h2

def shaChN (x y z : Nat) : Nat :=
  xorN (andN x y) (andN (xorN x 0xFFFFFFFF) z)

def shaMajN (x y z : Nat) : Nat :=
  xorN (xorN (andN x y) (andN x z)) (andN y z)

def shaBSig0N (x : Nat) : Nat :=
  xorN (xorN (rotrN x 2) (rotrN x 13)) (rotrN x 22)

def shaBSig1N (x : Nat) : Nat :=
  xorN (xorN (rotrN x 6) (rotrN x 11)) (rotrN x 25)

def shaSSig0N (x : Nat) : Nat :=
  xorN (xorN (rotrN x 7) (rotrN x 18)) (shrN x 3)

def shaSSig1N (x : Nat) : Nat :=
  xorN (xorN (rotrN x 17) (rotrN x 19)) (shrN x 10)

private theorem shaSSig0N_lt (x : Nat) : shaSSig0N x < 2 ^ 32 := xorN_lt _ _
private theorem shaSSig1N_lt (x : Nat) : shaSSig1N x < 2 ^ 32 := xorN_lt _ _

section EvalProofs

attribute [local irreducible] xorN andN orN addN shrN rotrN

private theorem shaChN_eq (x y z : UInt32) :
    UInt32.ofNat (shaChN x.toNat y.toNat z.toNat) = shaCh x y z := by
  unfold shaChN shaCh
  have h1 := andN_eq x y
  have h2 := xorN_eq x 0xFFFFFFFF
  have h3 := andN_ofNat_eq (xorN x.toNat 0xFFFFFFFF) z.toNat _ z (xorN_lt _ _) z.toBitVec.isLt h2 UInt32.ofNat_toNat
  exact xorN_ofNat_eq _ _ _ _ (andN_lt _ _) (andN_lt _ _) h1 h3

private theorem shaMajN_eq (x y z : UInt32) :
    UInt32.ofNat (shaMajN x.toNat y.toNat z.toNat) = shaMaj x y z := by
  unfold shaMajN shaMaj
  have hl := xorN_ofNat_eq _ _ _ _ (andN_lt _ _) (andN_lt _ _) (andN_eq x y) (andN_eq x z)
  exact xorN_ofNat_eq _ _ _ _ (xorN_lt _ _) (andN_lt _ _) hl (andN_eq y z)

private theorem xor3_ofNat_eq (a b c : Nat) (xa xb xc : UInt32)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32)
    (ea : UInt32.ofNat a = xa) (eb : UInt32.ofNat b = xb) (ec : UInt32.ofNat c = xc) :
    UInt32.ofNat (xorN (xorN a b) c) = xa ^^^ xb ^^^ xc := by
  have hl := xorN_ofNat_eq a b xa xb ha hb ea eb
  exact xorN_ofNat_eq (xorN a b) c (xa ^^^ xb) xc (xorN_lt _ _) hc hl ec

private theorem shaBSig0N_eq (x : UInt32) :
    UInt32.ofNat (shaBSig0N x.toNat) = shaBSig0 x :=
  xor3_ofNat_eq _ _ _ _ _ _ (rotrN_lt _ _) (rotrN_lt _ _) (rotrN_lt _ _)
    (rotrN_eq x 2 (by decide) (by decide))
    (rotrN_eq x 13 (by decide) (by decide))
    (rotrN_eq x 22 (by decide) (by decide))

private theorem shaBSig1N_eq (x : UInt32) :
    UInt32.ofNat (shaBSig1N x.toNat) = shaBSig1 x :=
  xor3_ofNat_eq _ _ _ _ _ _ (rotrN_lt _ _) (rotrN_lt _ _) (rotrN_lt _ _)
    (rotrN_eq x 6 (by decide) (by decide))
    (rotrN_eq x 11 (by decide) (by decide))
    (rotrN_eq x 25 (by decide) (by decide))

private theorem shaSSig0N_eq (x : UInt32) :
    UInt32.ofNat (shaSSig0N x.toNat) = shaSSig0 x :=
  xor3_ofNat_eq _ _ _ _ _ _ (rotrN_lt _ _) (rotrN_lt _ _) (shrN_lt _ _ x.toBitVec.isLt)
    (rotrN_eq x 7 (by decide) (by decide))
    (rotrN_eq x 18 (by decide) (by decide))
    (shrN_eq x 3 (by decide))

private theorem shaSSig1N_eq (x : UInt32) :
    UInt32.ofNat (shaSSig1N x.toNat) = shaSSig1 x :=
  xor3_ofNat_eq _ _ _ _ _ _ (rotrN_lt _ _) (rotrN_lt _ _) (shrN_lt _ _ x.toBitVec.isLt)
    (rotrN_eq x 17 (by decide) (by decide))
    (rotrN_eq x 19 (by decide) (by decide))
    (shrN_eq x 10 (by decide))

structure Sha256NatState where
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat
  h5 : Nat
  h6 : Nat
  h7 : Nat
  deriving DecidableEq, Repr

def Sha256NatState.init : Sha256NatState :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def Sha256NatState.toUInt32 (s : Sha256NatState) : Sha256State :=
  ⟨UInt32.ofNat s.h0, UInt32.ofNat s.h1, UInt32.ofNat s.h2, UInt32.ofNat s.h3,
   UInt32.ofNat s.h4, UInt32.ofNat s.h5, UInt32.ofNat s.h6, UInt32.ofNat s.h7⟩

def Sha256NatState.wf (s : Sha256NatState) : Prop :=
  s.h0 < 2 ^ 32 ∧ s.h1 < 2 ^ 32 ∧ s.h2 < 2 ^ 32 ∧ s.h3 < 2 ^ 32 ∧
  s.h4 < 2 ^ 32 ∧ s.h5 < 2 ^ 32 ∧ s.h6 < 2 ^ 32 ∧ s.h7 < 2 ^ 32

theorem Sha256NatState.init_wf : Sha256NatState.init.wf := by
  unfold Sha256NatState.wf Sha256NatState.init
  decide

theorem Sha256NatState.init_eq : Sha256NatState.init.toUInt32 = Sha256State.init := rfl

def sha256RoundN (st : Sha256NatState) (kVal wVal : Nat) : Sha256NatState :=
  let t1 := addN (addN (addN (addN st.h7 (shaBSig1N st.h4)) (shaChN st.h4 st.h5 st.h6)) kVal) wVal
  let t2 := addN (shaBSig0N st.h0) (shaMajN st.h0 st.h1 st.h2)
  ⟨addN t1 t2, st.h0, st.h1, st.h2, addN st.h3 t1, st.h4, st.h5, st.h6⟩

theorem sha256RoundN_wf (st : Sha256NatState) (k w : Nat) (hst : st.wf) :
    (sha256RoundN st k w).wf := by
  rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨addN_lt _ _, h0, h1, h2, addN_lt _ _, h4, h5, h6⟩

private theorem addN_ofNat_eq (a b : Nat) (xa xb : UInt32)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (ea : UInt32.ofNat a = xa) (eb : UInt32.ofNat b = xb) :
    UInt32.ofNat (addN a b) = xa + xb := by
  rw [← ea, ← eb, ← addN_eq]
  congr 1
  rw [uint32_toNat_ofNat_lt_s ha, uint32_toNat_ofNat_lt_s hb]

theorem sha256RoundN_eq (st : Sha256NatState) (kVal wVal : Nat)
    (hst : st.wf) (hk : kVal < 2 ^ 32) (hw : wVal < 2 ^ 32) :
    (sha256RoundN st kVal wVal).toUInt32 =
      sha256Round st.toUInt32 (UInt32.ofNat kVal) (UInt32.ofNat wVal) := by
  rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  unfold sha256RoundN sha256Round Sha256NatState.toUInt32
  dsimp only
  have hbs1 : UInt32.ofNat (shaBSig1N st.h4) = shaBSig1 (UInt32.ofNat st.h4) := by
    have he := shaBSig1N_eq (UInt32.ofNat st.h4)
    rw [uint32_toNat_ofNat_lt_s h4] at he; exact he
  have hch : UInt32.ofNat (shaChN st.h4 st.h5 st.h6) =
      shaCh (UInt32.ofNat st.h4) (UInt32.ofNat st.h5) (UInt32.ofNat st.h6) := by
    have he := shaChN_eq (UInt32.ofNat st.h4) (UInt32.ofNat st.h5) (UInt32.ofNat st.h6)
    rw [uint32_toNat_ofNat_lt_s h4, uint32_toNat_ofNat_lt_s h5, uint32_toNat_ofNat_lt_s h6] at he
    exact he
  have hbs0 : UInt32.ofNat (shaBSig0N st.h0) = shaBSig0 (UInt32.ofNat st.h0) := by
    have he := shaBSig0N_eq (UInt32.ofNat st.h0)
    rw [uint32_toNat_ofNat_lt_s h0] at he; exact he
  have hmaj : UInt32.ofNat (shaMajN st.h0 st.h1 st.h2) =
      shaMaj (UInt32.ofNat st.h0) (UInt32.ofNat st.h1) (UInt32.ofNat st.h2) := by
    have he := shaMajN_eq (UInt32.ofNat st.h0) (UInt32.ofNat st.h1) (UInt32.ofNat st.h2)
    rw [uint32_toNat_ofNat_lt_s h0, uint32_toNat_ofNat_lt_s h1, uint32_toNat_ofNat_lt_s h2] at he
    exact he
  have hs1 := addN_ofNat_eq st.h7 (shaBSig1N st.h4) _ _ h7 (xorN_lt _ _) rfl hbs1
  have hs2 := addN_ofNat_eq _ (shaChN st.h4 st.h5 st.h6) _ _ (addN_lt _ _) (xorN_lt _ _) hs1 hch
  have hs3 := addN_ofNat_eq _ kVal _ _ (addN_lt _ _) hk hs2 rfl
  have ht1 := addN_ofNat_eq _ wVal _ _ (addN_lt _ _) hw hs3 rfl
  have ht2 := addN_ofNat_eq (shaBSig0N st.h0) (shaMajN st.h0 st.h1 st.h2) _ _ (xorN_lt _ _) (xorN_lt _ _) hbs0 hmaj
  have hnew0 := addN_ofNat_eq _ _ _ _ (addN_lt _ _) (addN_lt _ _) ht1 ht2
  have hnew4 := addN_ofNat_eq st.h3 _ _ _ h3 (addN_lt _ _) rfl ht1
  rw [hnew0, hnew4]

attribute [local irreducible] shaChN shaMajN shaBSig0N shaBSig1N shaSSig0N shaSSig1N sha256RoundN

private theorem nat_mul_pow2_or (u v k : Nat) (hv : v < 2 ^ k) :
    (u * 2 ^ k) ||| v = u * 2 ^ k + v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hik : i < k
  · have hmul : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hdiv : (u * 2 ^ k) / 2 ^ i = u * 2 ^ (k - i) := by
      rw [hmul, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
    have heven : (u * 2 ^ (k - i)) % 2 = 0 := by
      have hsub : k - i = (k - i - 1) + 1 := by omega
      rw [hsub, Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ 2
    have hm : (u * 2 ^ k).testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hdiv, heven]; rfl
    have hsum : (u * 2 ^ k + v).testBit i = v.testBit i := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv2 : (u * 2 ^ k + v) / 2 ^ i = u * 2 ^ (k - i) + v / 2 ^ i := by
        rw [hmul, ← Nat.mul_assoc, Nat.mul_comm (u * 2 ^ (k - i)) (2 ^ i),
            Nat.mul_add_div (Nat.pow_pos (by decide))]
      rw [hdiv2, Nat.add_mod, heven, Nat.zero_add, Nat.mod_mod]
    rw [hm, Bool.false_or, hsum]
  · have hge : k ≤ i := by omega
    have hvf : v.testBit i = false := by
      have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hge
      exact Nat.testBit_lt_two_pow (by omega)
    have hsum : (u * 2 ^ k + v).testBit i = (u * 2 ^ k).testBit i := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hmul : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
      have hdiv1 : (u * 2 ^ k + v) / 2 ^ i = u / 2 ^ (i - k) := by
        rw [hmul, ← Nat.div_div_eq_div_mul, Nat.mul_comm u (2 ^ k),
            Nat.mul_add_div (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hv, Nat.add_zero]
      have hdiv2 : (u * 2 ^ k) / 2 ^ i = u / 2 ^ (i - k) := by
        rw [hmul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
      rw [hdiv1, hdiv2]
    rw [hvf, Bool.or_false, hsum]

def readWordBENat (byteAt : Nat → UInt8) (off : Nat) : Nat :=
  ((byteAt off).toNat * 16777216) +
  ((byteAt (off + 1)).toNat * 65536) +
  ((byteAt (off + 2)).toNat * 256) +
  (byteAt (off + 3)).toNat

theorem readWordBENat_lt (byteAt : Nat → UInt8) (off : Nat) :
    readWordBENat byteAt off < 2 ^ 32 := by
  unfold readWordBENat
  have h0 : (byteAt off).toNat < 256 := (byteAt off).toBitVec.isLt
  have h1 : (byteAt (off + 1)).toNat < 256 := (byteAt (off + 1)).toBitVec.isLt
  have h2 : (byteAt (off + 2)).toNat < 256 := (byteAt (off + 2)).toBitVec.isLt
  have h3 : (byteAt (off + 3)).toNat < 256 := (byteAt (off + 3)).toBitVec.isLt
  omega

private theorem readWordBENat_eq (byteAt : Nat → UInt8) (off : Nat) :
    UInt32.ofNat (readWordBENat byteAt off) = readWordBEAt byteAt off := by
  apply UInt32.toNat_inj.mp
  rw [uint32_toNat_ofNat_lt_s (readWordBENat_lt byteAt off)]
  unfold readWordBENat readWordBEAt
  let b0 := (byteAt off).toNat
  let b1 := (byteAt (off + 1)).toNat
  let b2 := (byteAt (off + 2)).toNat
  let b3 := (byteAt (off + 3)).toNat
  have hb0 : b0 < 256 := (byteAt off).toBitVec.isLt
  have hb1 : b1 < 256 := (byteAt (off + 1)).toBitVec.isLt
  have hb2 : b2 < 256 := (byteAt (off + 2)).toBitVec.isLt
  have hb3 : b3 < 256 := (byteAt (off + 3)).toBitVec.isLt
  have hk24 : (24 : UInt32).toNat % 32 = 24 := by decide
  have hk16 : (16 : UInt32).toNat % 32 = 16 := by decide
  have hk8 : (8 : UInt32).toNat % 32 = 8 := by decide
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
      UInt32.toNat_shiftLeft, UInt32.toNat_shiftLeft, UInt32.toNat_shiftLeft,
      UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
      hk24, hk16, hk8, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  change b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 =
    (b0 * 16777216 % 2 ^ 32) ||| (b1 * 65536 % 2 ^ 32) ||| (b2 * 256 % 2 ^ 32) ||| b3
  have hm0 : b0 * 16777216 % 2 ^ 32 = b0 * 16777216 := Nat.mod_eq_of_lt (by omega)
  have hm1 : b1 * 65536 % 2 ^ 32 = b1 * 65536 := Nat.mod_eq_of_lt (by omega)
  have hm2 : b2 * 256 % 2 ^ 32 = b2 * 256 := Nat.mod_eq_of_lt (by omega)
  rw [hm0, hm1, hm2]
  have hor01 : (b0 * 16777216) ||| (b1 * 65536) = b0 * 16777216 + b1 * 65536 := by
    have hmul : b0 * 16777216 = b0 * 2 ^ 24 := by omega
    rw [hmul, nat_mul_pow2_or b0 (b1 * 65536) 24 (by omega)]
  have hor012 : (b0 * 16777216 + b1 * 65536) ||| (b2 * 256) = b0 * 16777216 + b1 * 65536 + b2 * 256 := by
    have hmul : b0 * 16777216 + b1 * 65536 = (b0 * 256 + b1) * 2 ^ 16 := by omega
    rw [hmul, nat_mul_pow2_or (b0 * 256 + b1) (b2 * 256) 16 (by omega)]
  have hor0123' : (b0 * 16777216 + b1 * 65536 + b2 * 256) ||| b3 =
      b0 * 16777216 + b1 * 65536 + b2 * 256 + b3 := by
    have hmul : b0 * 16777216 + b1 * 65536 + b2 * 256 = (b0 * 65536 + b1 * 256 + b2) * 2 ^ 8 := by omega
    rw [hmul, nat_mul_pow2_or _ b3 8 (by omega)]
  rw [hor01, hor012, hor0123']

def expandScheduleNatLoop (t rem : Nat) (w : Array Nat) : Array Nat :=
  match rem with
  | 0 => w
  | rem + 1 =>
    let wt := addN (addN (addN (shaSSig1N w[t - 2]!) w[t - 7]!) (shaSSig0N w[t - 15]!)) w[t - 16]!
    expandScheduleNatLoop (t + 1) rem (w.push wt)

theorem expandScheduleNatLoop_add (t n₁ n₂ : Nat) (w : Array Nat) :
    expandScheduleNatLoop t (n₁ + n₂) w =
      expandScheduleNatLoop (t + n₁) n₂ (expandScheduleNatLoop t n₁ w) := by
  induction n₁ generalizing t w with
  | zero => simp [expandScheduleNatLoop]
  | succ n₁ ih =>
    have hadd : (n₁ + 1) + n₂ = (n₁ + n₂) + 1 := by omega
    rw [hadd, expandScheduleNatLoop, expandScheduleNatLoop]
    simpa [Nat.add_assoc, Nat.add_comm 1 n₁] using ih (t + 1) _

def buildScheduleNat (byteAt : Nat → UInt8) : Array Nat :=
  let w0 := (Array.range 16).map (fun i => readWordBENat byteAt (i * 4))
  expandScheduleNatLoop 16 48 w0

private theorem array_getBang_map_ofNat (w : Array Nat) (i : Nat) :
    UInt32.ofNat w[i]! = (w.map UInt32.ofNat)[i]! := by
  by_cases hi : i < w.size
  · have hm : i < (w.map UInt32.ofNat).size := by simpa using hi
    rw [getElem!_pos w i hi, getElem!_pos (w.map UInt32.ofNat) i hm, Array.getElem_map]
  · have hm : ¬ (i < (w.map UInt32.ofNat).size) := by simpa using hi
    rw [getElem!_neg w i hi, getElem!_neg (w.map UInt32.ofNat) i hm]
    rfl

private theorem expandScheduleNatLoop_eq (t rem : Nat) (w : Array Nat)
    (ht : 16 ≤ t) (hw : w.size = t) (hb : ∀ x ∈ w, x < 2 ^ 32) :
    (expandScheduleNatLoop t rem w).map UInt32.ofNat =
      expandScheduleLoop t rem (w.map UInt32.ofNat) ∧
    (expandScheduleNatLoop t rem w).size = t + rem ∧
    (∀ x ∈ expandScheduleNatLoop t rem w, x < 2 ^ 32) := by
  induction rem generalizing t w with
  | zero =>
    unfold expandScheduleNatLoop expandScheduleLoop
    exact ⟨rfl, hw, hb⟩
  | succ rem ih =>
    unfold expandScheduleNatLoop expandScheduleLoop
    dsimp only
    let wt := addN (addN (addN (shaSSig1N w[t - 2]!) w[t - 7]!) (shaSSig0N w[t - 15]!)) w[t - 16]!
    have hlt2 : t - 2 < w.size := by omega
    have hlt7 : t - 7 < w.size := by omega
    have hlt15 : t - 15 < w.size := by omega
    have hlt16 : t - 16 < w.size := by omega
    have hb2 : w[t - 2]! < 2 ^ 32 := hb _ (by rw [getElem!_pos w _ hlt2]; exact Array.getElem_mem _)
    have hb7 : w[t - 7]! < 2 ^ 32 := hb _ (by rw [getElem!_pos w _ hlt7]; exact Array.getElem_mem _)
    have hb15 : w[t - 15]! < 2 ^ 32 := hb _ (by rw [getElem!_pos w _ hlt15]; exact Array.getElem_mem _)
    have hb16 : w[t - 16]! < 2 ^ 32 := hb _ (by rw [getElem!_pos w _ hlt16]; exact Array.getElem_mem _)
    have hs1 : UInt32.ofNat (shaSSig1N w[t - 2]!) = shaSSig1 (w.map UInt32.ofNat)[t - 2]! := by
      have he := shaSSig1N_eq (UInt32.ofNat w[t - 2]!)
      rw [uint32_toNat_ofNat_lt_s hb2, array_getBang_map_ofNat w (t - 2)] at he
      exact he
    have hs0 : UInt32.ofNat (shaSSig0N w[t - 15]!) = shaSSig0 (w.map UInt32.ofNat)[t - 15]! := by
      have he := shaSSig0N_eq (UInt32.ofNat w[t - 15]!)
      rw [uint32_toNat_ofNat_lt_s hb15, array_getBang_map_ofNat w (t - 15)] at he
      exact he
    have hw7 : UInt32.ofNat w[t - 7]! = (w.map UInt32.ofNat)[t - 7]! :=
      array_getBang_map_ofNat w (t - 7)
    have hw16 : UInt32.ofNat w[t - 16]! = (w.map UInt32.ofNat)[t - 16]! :=
      array_getBang_map_ofNat w (t - 16)
    have ha1 := addN_ofNat_eq (shaSSig1N w[t - 2]!) w[t - 7]! _ _ (shaSSig1N_lt _) hb7 hs1 hw7
    have ha2 := addN_ofNat_eq _ (shaSSig0N w[t - 15]!) _ _ (addN_lt _ _) (shaSSig0N_lt _) ha1 hs0
    have hwt : UInt32.ofNat wt =
        shaSSig1 (w.map UInt32.ofNat)[t - 2]! + (w.map UInt32.ofNat)[t - 7]! +
        shaSSig0 (w.map UInt32.ofNat)[t - 15]! + (w.map UInt32.ofNat)[t - 16]! :=
      addN_ofNat_eq _ w[t - 16]! _ _ (addN_lt _ _) hb16 ha2 hw16
    have hb' : ∀ x ∈ w.push wt, x < 2 ^ 32 := by
      intro x hx
      rcases Array.mem_push.mp hx with hx | rfl
      · exact hb x hx
      · exact addN_lt _ _
    have hrec := ih (t + 1) (w.push wt) (by omega) (by simp [hw]) hb'
    rw [Array.map_push, hwt] at hrec
    have hsz : t + 1 + rem = t + (rem + 1) := by omega
    exact ⟨hrec.1, hrec.2.1.trans hsz, hrec.2.2⟩

theorem buildScheduleNat_eq (byteAt : Nat → UInt8) :
    (buildScheduleNat byteAt).map UInt32.ofNat = buildSchedule byteAt ∧
    (buildScheduleNat byteAt).size = 64 ∧
    (∀ x ∈ buildScheduleNat byteAt, x < 2 ^ 32) := by
  unfold buildScheduleNat buildSchedule
  dsimp only
  let w0 := (Array.range 16).map (fun i => readWordBENat byteAt (i * 4))
  have hw0_size : w0.size = 16 := by simp [w0]
  have hw0_b : ∀ x ∈ w0, x < 2 ^ 32 := by
    intro x hx
    simp only [w0, Array.mem_map, Array.mem_range] at hx
    rcases hx with ⟨i, _, rfl⟩
    exact readWordBENat_lt byteAt (i * 4)
  have hmap : w0.map UInt32.ofNat = (Array.range 16).map (fun i => readWordBEAt byteAt (i * 4)) := by
    simp only [w0, Array.map_map]
    apply Array.map_congr_left
    intro i _
    exact readWordBENat_eq byteAt (i * 4)
  have hrec := expandScheduleNatLoop_eq 16 48 w0 (by decide) hw0_size hw0_b
  rw [hmap] at hrec
  exact hrec

def compressRoundsNatLoop (t rem : Nat) (w : Array Nat) (st : Sha256NatState) : Sha256NatState :=
  match rem with
  | 0 => st
  | rem + 1 =>
    compressRoundsNatLoop (t + 1) rem w (sha256RoundN st sha256K[t]!.toNat w[t]!)

theorem compressRoundsNatLoop_wf (t rem : Nat) (w : Array Nat) (st : Sha256NatState)
    (hst : st.wf) : (compressRoundsNatLoop t rem w st).wf := by
  induction rem generalizing t st with
  | zero => exact hst
  | succ rem ih =>
    unfold compressRoundsNatLoop
    exact ih (t + 1) _ (sha256RoundN_wf st _ _ hst)

theorem compressRoundsNatLoop_add (t n₁ n₂ : Nat) (w : Array Nat) (st : Sha256NatState) :
    compressRoundsNatLoop t (n₁ + n₂) w st =
      compressRoundsNatLoop (t + n₁) n₂ w (compressRoundsNatLoop t n₁ w st) := by
  induction n₁ generalizing t st with
  | zero => simp [compressRoundsNatLoop]
  | succ n₁ ih =>
    have hadd : (n₁ + 1) + n₂ = (n₁ + n₂) + 1 := by omega
    rw [hadd, compressRoundsNatLoop, compressRoundsNatLoop]
    simpa [Nat.add_assoc, Nat.add_comm 1 n₁] using ih (t + 1) _

theorem compressRoundsNatLoop_eq (t rem : Nat) (w : Array Nat) (st : Sha256NatState)
    (hst : st.wf) (hw : ∀ x ∈ w, x < 2 ^ 32) (hw_size : w.size = 64) (ht : t + rem ≤ 64) :
    (compressRoundsNatLoop t rem w st).toUInt32 =
      compressRoundsLoop t rem (w.map UInt32.ofNat) st.toUInt32 := by
  induction rem generalizing t st with
  | zero =>
    unfold compressRoundsNatLoop compressRoundsLoop
    rfl
  | succ rem ih =>
    unfold compressRoundsNatLoop compressRoundsLoop
    have htk : t < sha256K.size := by rw [sha256K_size]; omega
    have hk_lt : sha256K[t]!.toNat < 2 ^ 32 := sha256K[t]!.toBitVec.isLt
    have htw : t < w.size := by omega
    have hw_lt : w[t]! < 2 ^ 32 := hw _ (by rw [getElem!_pos w t htw]; exact Array.getElem_mem _)
    have hr := sha256RoundN_eq st sha256K[t]!.toNat w[t]! hst hk_lt hw_lt
    have hk_eq : UInt32.ofNat sha256K[t]!.toNat = sha256K[t]! := by
      apply UInt32.toNat_inj.mp
      exact uint32_toNat_ofNat_lt_s hk_lt
    have hw_eq : UInt32.ofNat w[t]! = (w.map UInt32.ofNat)[t]! :=
      array_getBang_map_ofNat w t
    rw [hk_eq, hw_eq] at hr
    rw [ih (t + 1) _ (sha256RoundN_wf st _ _ hst) (by omega), hr]

def compressBlockNat (st : Sha256NatState) (byteAt : Nat → UInt8) : Sha256NatState :=
  let w := buildScheduleNat byteAt
  let r := compressRoundsNatLoop 0 64 w st
  ⟨addN st.h0 r.h0, addN st.h1 r.h1, addN st.h2 r.h2, addN st.h3 r.h3,
   addN st.h4 r.h4, addN st.h5 r.h5, addN st.h6 r.h6, addN st.h7 r.h7⟩

theorem compressBlockNat_wf (st : Sha256NatState) (byteAt : Nat → UInt8) :
    (compressBlockNat st byteAt).wf :=
  ⟨addN_lt _ _, addN_lt _ _, addN_lt _ _, addN_lt _ _,
   addN_lt _ _, addN_lt _ _, addN_lt _ _, addN_lt _ _⟩

theorem compressBlockNat_eq (st : Sha256NatState) (byteAt : Nat → UInt8) (hst : st.wf) :
    (compressBlockNat st byteAt).toUInt32 = compressBlockSpec st.toUInt32 byteAt := by
  have ⟨hw_map, hw_size, hw_b⟩ := buildScheduleNat_eq byteAt
  have hr_wf := compressRoundsNatLoop_wf 0 64 (buildScheduleNat byteAt) st hst
  have hr_eq := compressRoundsNatLoop_eq 0 64 (buildScheduleNat byteAt) st hst hw_b hw_size (by decide)
  rw [hw_map] at hr_eq
  rcases hst with ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩
  rcases hr_wf with ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  unfold compressBlockNat compressBlockSpec Sha256NatState.toUInt32
  dsimp only
  let r := compressRoundsNatLoop 0 64 (buildScheduleNat byteAt) st
  let rs := compressRoundsLoop 0 64 (buildSchedule byteAt) st.toUInt32
  have e0 : UInt32.ofNat r.h0 = rs.h0 := congrArg Sha256State.h0 hr_eq
  have e1 : UInt32.ofNat r.h1 = rs.h1 := congrArg Sha256State.h1 hr_eq
  have e2 : UInt32.ofNat r.h2 = rs.h2 := congrArg Sha256State.h2 hr_eq
  have e3 : UInt32.ofNat r.h3 = rs.h3 := congrArg Sha256State.h3 hr_eq
  have e4 : UInt32.ofNat r.h4 = rs.h4 := congrArg Sha256State.h4 hr_eq
  have e5 : UInt32.ofNat r.h5 = rs.h5 := congrArg Sha256State.h5 hr_eq
  have e6 : UInt32.ofNat r.h6 = rs.h6 := congrArg Sha256State.h6 hr_eq
  have e7 : UInt32.ofNat r.h7 = rs.h7 := congrArg Sha256State.h7 hr_eq
  have a0 := addN_ofNat_eq st.h0 r.h0 _ _ s0 r0 rfl e0
  have a1 := addN_ofNat_eq st.h1 r.h1 _ _ s1 r1 rfl e1
  have a2 := addN_ofNat_eq st.h2 r.h2 _ _ s2 r2 rfl e2
  have a3 := addN_ofNat_eq st.h3 r.h3 _ _ s3 r3 rfl e3
  have a4 := addN_ofNat_eq st.h4 r.h4 _ _ s4 r4 rfl e4
  have a5 := addN_ofNat_eq st.h5 r.h5 _ _ s5 r5 rfl e5
  have a6 := addN_ofNat_eq st.h6 r.h6 _ _ s6 r6 rfl e6
  have a7 := addN_ofNat_eq st.h7 r.h7 _ _ s7 r7 rfl e7
  rw [a0, a1, a2, a3, a4, a5, a6, a7]
  rfl

def sha256BlocksNat (padded : ByteArray) (nBlocks : Nat) (st : Sha256NatState) : Sha256NatState :=
  Nat.rec st (fun k acc => compressBlockNat acc (fun j => padded.get! (k * 64 + j))) nBlocks

private theorem sha256BlocksNat_succ (padded : ByteArray) (n : Nat) (st : Sha256NatState) :
    sha256BlocksNat padded n.succ st =
      compressBlockNat (sha256BlocksNat padded n st) (fun j => padded.get! (n * 64 + j)) := by
  unfold sha256BlocksNat; rfl

private theorem sha256SpecBlocks_succ_eval (padded : ByteArray) (n : Nat) (st : Sha256State) :
    sha256SpecBlocks padded n.succ st =
      compressBlockSpec (sha256SpecBlocks padded n st) (fun j => padded.get! (n * 64 + j)) := by
  unfold sha256SpecBlocks; rfl

attribute [local irreducible] compressBlockNat sha256BlocksNat sha256SpecBlocks

theorem sha256BlocksNat_eq (padded : ByteArray) (nBlocks : Nat) (st : Sha256NatState)
    (hst : st.wf) :
    (sha256BlocksNat padded nBlocks st).toUInt32 =
      sha256SpecBlocks padded nBlocks st.toUInt32 := by
  induction nBlocks with
  | zero =>
    unfold sha256BlocksNat sha256SpecBlocks
    rfl
  | succ n ih =>
    have hwf : (sha256BlocksNat padded n st).wf := by
      clear ih
      induction n with
      | zero =>
        unfold sha256BlocksNat; exact hst
      | succ m _ =>
        rw [sha256BlocksNat_succ]
        exact compressBlockNat_wf _ _
    rw [sha256BlocksNat_succ, sha256SpecBlocks_succ_eval, compressBlockNat_eq _ _ hwf, ih]

def sha256NatEval (b : ByteArray) : Sha256Digest :=
  let padded := sha256PadBytes b
  let nBlocks := padded.size / 64
  (sha256BlocksNat padded nBlocks Sha256NatState.init).toUInt32.toDigest

theorem sha256_eq_natEval (b : ByteArray) : sha256 b = sha256NatEval b := by
  rw [sha256_eq_spec]
  unfold sha256Spec sha256NatEval
  dsimp only
  rw [sha256BlocksNat_eq _ _ Sha256NatState.init Sha256NatState.init_wf, Sha256NatState.init_eq]

end EvalProofs

end Leaf.Core
