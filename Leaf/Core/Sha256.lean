import Leaf.Core.Bits
import Leaf.Core.Sha256Spec

namespace Leaf.Core

/-- Processes `nBlocks` full 64-byte blocks starting at offset 0 of `b`. -/
def sha256PrefixBlocks (b : ByteArray) (nBlocks : Nat) (st : Sha256State) : Sha256State :=
  Nat.rec st (fun k acc => compressBlockSpec acc (fun j => b.get! (k * 64 + j))) nBlocks

/-- Chunked pure-Lean SHA-256 implementation avoiding whole-buffer padding copies. -/
def sha256 (b : ByteArray) : Sha256Digest :=
  let fullBlocks := b.size / 64
  let st1 := sha256PrefixBlocks b fullBlocks Sha256State.init
  let tail := b.extract (fullBlocks * 64) b.size
  let zeros := ByteArray.mk (Array.replicate (sha256ZeroCount b.size) 0)
  let tailPadded := tail ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8)
  let tailBlocks := tailPadded.size / 64
  let st2 := sha256SpecBlocks tailPadded tailBlocks st1
  st2.toDigest

/-! ### Equivalence Proof: `sha256 b = sha256Spec b` -/

private theorem byteArray_getBang_eq_get {a : ByteArray} {i : Nat} (h : i < a.size) :
    a.get! i = a[i]'h := by
  cases a with | mk arr =>
  simp only [ByteArray.get!]
  rw [getElem!_pos arr i h]
  rfl

private theorem byteArray_getBang_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have hab : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [byteArray_getBang_eq_get hab, byteArray_getBang_eq_get h]
  exact ByteArray.getElem_append_left h

private theorem byteArray_getBang_append_right {a b : ByteArray} {k : Nat} (hk : k < b.size) :
    (a ++ b).get! (a.size + k) = b.get! k := by
  have hab : a.size + k < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [byteArray_getBang_eq_get hab, byteArray_getBang_eq_get hk]
  rw [ByteArray.getElem_append_right (by omega)]
  congr 1
  omega

private theorem readWordBEAt_congr {f g : Nat → UInt8} {off : Nat}
    (h : ∀ j, j < 4 → f (off + j) = g (off + j)) :
    readWordBEAt f off = readWordBEAt g off := by
  unfold readWordBEAt
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

private theorem compressBlockSpec_congr {st : Sha256State} {f g : Nat → UInt8}
    (h : ∀ j, j < 64 → f j = g j) :
    compressBlockSpec st f = compressBlockSpec st g := by
  have hsched : buildSchedule f = buildSchedule g := by
    unfold buildSchedule
    have hw : (Array.range 16).map (fun i => readWordBEAt f (i * 4)) =
        (Array.range 16).map (fun i => readWordBEAt g (i * 4)) := by
      apply Array.map_congr_left
      intro i hi
      have hlt : i < 16 := by simpa [Array.mem_range] using hi
      exact readWordBEAt_congr (fun j hj => h (i * 4 + j) (by omega))
    rw [hw]
  unfold compressBlockSpec
  rw [hsched]

private theorem sha256SpecBlocks_zero (p : ByteArray) (st : Sha256State) :
    sha256SpecBlocks p 0 st = st := rfl

private theorem sha256SpecBlocks_succ (p : ByteArray) (n : Nat) (st : Sha256State) :
    sha256SpecBlocks p n.succ st =
      compressBlockSpec (sha256SpecBlocks p n st) (fun j => p.get! (n * 64 + j)) := by
  unfold sha256SpecBlocks; rfl

private theorem sha256PrefixBlocks_succ (b : ByteArray) (n : Nat) (st : Sha256State) :
    sha256PrefixBlocks b n.succ st =
      compressBlockSpec (sha256PrefixBlocks b n st) (fun j => b.get! (n * 64 + j)) := by
  unfold sha256PrefixBlocks; rfl

section
attribute [local irreducible] sha256PrefixBlocks sha256SpecBlocks sha256PadBytes

private theorem sha256SpecBlocks_add_tail (pfx tail : ByteArray) (q m : Nat) (st : Sha256State)
    (hpfx : pfx.size = q * 64) (hm : m * 64 ≤ tail.size) :
    sha256SpecBlocks (pfx ++ tail) (q + m) st =
      sha256SpecBlocks tail m (sha256SpecBlocks (pfx ++ tail) q st) := by
  induction m with
  | zero =>
    rw [Nat.add_zero, sha256SpecBlocks_zero]
  | succ m ih =>
    have hq_succ : q + m.succ = (q + m).succ := rfl
    rw [hq_succ, sha256SpecBlocks_succ, sha256SpecBlocks_succ, ih (by omega)]
    apply compressBlockSpec_congr
    intro j hj
    have hidx : (q + m) * 64 + j = pfx.size + (m * 64 + j) := by
      rw [Nat.add_mul, ← hpfx, Nat.add_assoc]
    have hlt : m * 64 + j < tail.size := by omega
    rw [hidx, byteArray_getBang_append_right hlt]

private theorem sha256PrefixBlocks_eq_spec (b rest : ByteArray) (q : Nat) (st : Sha256State)
    (hq : q * 64 ≤ b.size) :
    sha256PrefixBlocks b q st = sha256SpecBlocks (b ++ rest) q st := by
  induction q with
  | zero =>
    unfold sha256PrefixBlocks
    rw [sha256SpecBlocks_zero]
    rfl
  | succ q ih =>
    rw [sha256PrefixBlocks_succ, sha256SpecBlocks_succ, ih (by omega)]
    apply compressBlockSpec_congr
    intro j hj
    have hlt : q * 64 + j < b.size := by omega
    exact (byteArray_getBang_append_left hlt).symm

private theorem byteArray_split_at (b : ByteArray) (k : Nat) (hk : k ≤ b.size) :
    b.extract 0 k ++ b.extract k b.size = b := by
  rw [← ByteArray.extract_eq_extract_append_extract k (Nat.zero_le k) hk]
  exact ByteArray.extract_zero_size

private theorem sha256PadBytes_split (b : ByteArray) :
    let q := b.size / 64
    let pfx := b.extract 0 (q * 64)
    let tail := b.extract (q * 64) b.size
    let zeros := ByteArray.mk (Array.replicate (sha256ZeroCount b.size) 0)
    let tailPadded := tail ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8)
    sha256PadBytes b = pfx ++ tailPadded ∧
    (sha256PadBytes b).size / 64 = q + tailPadded.size / 64 ∧
    pfx.size = q * 64 := by
  intro q pfx tail zeros tailPadded
  have hq : q * 64 ≤ b.size := Nat.div_mul_le_self b.size 64
  have hpfx : pfx.size = q * 64 := by
    simp only [pfx, ByteArray.size_extract]; omega
  have hsplit : pfx ++ tail = b := byteArray_split_at b (q * 64) hq
  have hpad : sha256PadBytes b = pfx ++ tailPadded := by
    unfold sha256PadBytes
    change b ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8) =
      pfx ++ (tail ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8))
    rw [← hsplit]
    simp only [ByteArray.append_assoc]
  have hdiv : (sha256PadBytes b).size / 64 = q + tailPadded.size / 64 := by
    rw [hpad, ByteArray.size_append, hpfx, Nat.mul_comm q 64, Nat.mul_add_div (by decide)]
  exact ⟨hpad, hdiv, hpfx⟩

/-- Formal conformance theorem: chunked `sha256` equals FIPS 180-4 `sha256Spec` on all inputs. -/
theorem sha256_eq_spec (b : ByteArray) : sha256 b = sha256Spec b := by
  unfold sha256 sha256Spec
  apply congrArg Sha256State.toDigest
  let q := b.size / 64
  let pfx := b.extract 0 (q * 64)
  let tail := b.extract (q * 64) b.size
  let zeros := ByteArray.mk (Array.replicate (sha256ZeroCount b.size) 0)
  let suffix := ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8)
  let tailPadded := tail ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes ((b.size.toUInt64) * 8)
  have ⟨hpad, hdiv, hpfx⟩ := sha256PadBytes_split b
  have hq : q * 64 ≤ b.size := Nat.div_mul_le_self b.size 64
  have hfull_eq : sha256PrefixBlocks b q Sha256State.init =
      sha256SpecBlocks (sha256PadBytes b) q Sha256State.init := by
    have hs := sha256PrefixBlocks_eq_spec b suffix q Sha256State.init hq
    have hpad_eq : b ++ suffix = sha256PadBytes b := by
      unfold sha256PadBytes
      simp only [suffix, zeros, ByteArray.append_assoc]
    rw [← hpad_eq]
    exact hs
  have htail_bound : (tailPadded.size / 64) * 64 ≤ tailPadded.size :=
    Nat.div_mul_le_self tailPadded.size 64
  have hadd := sha256SpecBlocks_add_tail pfx tailPadded q (tailPadded.size / 64) Sha256State.init hpfx htail_bound
  have hrhs : sha256SpecBlocks (sha256PadBytes b) ((sha256PadBytes b).size / 64) Sha256State.init =
      sha256SpecBlocks tailPadded (tailPadded.size / 64) (sha256PrefixBlocks b q Sha256State.init) := by
    rw [hdiv, hpad, hadd, ← hpad, ← hfull_eq]
  change sha256SpecBlocks tailPadded (tailPadded.size / 64) (sha256PrefixBlocks b q Sha256State.init) = _
  exact hrhs.symm

end

theorem sha256_deterministic {a b : ByteArray} (h : a = b) : sha256 a = sha256 b :=
  congrArg sha256 h

theorem sha256_digest_size (b : ByteArray) : (sha256 b).bytes.size = 32 :=
  (sha256 b).size_eq

end Leaf.Core
