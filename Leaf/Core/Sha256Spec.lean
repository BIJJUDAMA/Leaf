import Leaf.Core.Types

namespace Leaf.Core

/-- FIPS 180-4 initial hash values `H^(0)`. -/
def sha256H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-- FIPS 180-4 64 round constants `K_0 .. K_63`. -/
def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

theorem sha256K_size : sha256K.size = 64 := by decide

/-- Right-rotation of a 32-bit word by `n` (`0 < n < 32`). -/
@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] def shaCh (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((x ^^^ 0xFFFFFFFF) &&& z)

@[inline] def shaMaj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] def shaBSig0 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

@[inline] def shaBSig1 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

@[inline] def shaSSig0 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)

@[inline] def shaSSig1 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

/-- Eight 32-bit state registers for SHA-256. -/
structure Sha256State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32
  deriving DecidableEq, BEq, Repr

def Sha256State.init : Sha256State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- Number of zero bytes needed for FIPS 180-4 SHA-256 padding of a message of `len` bytes. -/
def sha256ZeroCount (len : Nat) : Nat :=
  (64 + 56 - ((len + 1) % 64)) % 64

/-- Total padded byte length (always a positive multiple of 64). -/
def sha256PaddedLen (len : Nat) : Nat :=
  len + 1 + sha256ZeroCount len + 8

theorem sha256PaddedLen_mod (len : Nat) : sha256PaddedLen len % 64 = 0 := by
  unfold sha256PaddedLen sha256ZeroCount
  omega

theorem sha256PaddedLen_eq_blocks (len : Nat) :
    sha256PaddedLen len = 64 * ((len + 9 + 63) / 64) := by
  unfold sha256PaddedLen sha256ZeroCount
  omega

/-- Encodes a 64-bit unsigned integer as 8 big-endian bytes. -/
def uint64ToBEBytes (n : UInt64) : ByteArray :=
  ByteArray.mk #[
    (n >>> 56).toUInt8,
    (n >>> 48).toUInt8,
    (n >>> 40).toUInt8,
    (n >>> 32).toUInt8,
    (n >>> 24).toUInt8,
    (n >>> 16).toUInt8,
    (n >>> 8).toUInt8,
    n.toUInt8
  ]

theorem uint64ToBEBytes_size (n : UInt64) : (uint64ToBEBytes n).size = 8 := rfl

/-- Appends FIPS 180-4 padding (`0x80`, zero bytes, 64-bit BE bit length) to `b`. -/
def sha256PadBytes (b : ByteArray) : ByteArray :=
  let zeros := ByteArray.mk (Array.replicate (sha256ZeroCount b.size) 0)
  let bitLen := (b.size.toUInt64) * 8
  b ++ ByteArray.mk #[0x80] ++ zeros ++ uint64ToBEBytes bitLen

theorem sha256PadBytes_size (b : ByteArray) :
    (sha256PadBytes b).size = sha256PaddedLen b.size := by
  have h1 : (ByteArray.mk #[0x80]).size = 1 := rfl
  have hz : (ByteArray.mk (Array.replicate (sha256ZeroCount b.size) 0)).size = sha256ZeroCount b.size :=
    Array.size_replicate (n := sha256ZeroCount b.size) (v := (0 : UInt8))
  simp only [sha256PadBytes, sha256PaddedLen, ByteArray.size_append, uint64ToBEBytes_size, h1, hz]

/-- Reads 4 bytes at byte offset `off` in big-endian order as a `UInt32`. -/
@[inline] def readWordBEAt (byteAt : Nat → UInt8) (off : Nat) : UInt32 :=
  ((byteAt off).toUInt32 <<< 24) |||
  ((byteAt (off + 1)).toUInt32 <<< 16) |||
  ((byteAt (off + 2)).toUInt32 <<< 8) |||
  (byteAt (off + 3)).toUInt32

def expandScheduleLoop (t rem : Nat) (w : Array UInt32) : Array UInt32 :=
  match rem with
  | 0 => w
  | rem + 1 =>
    let wt := shaSSig1 w[t - 2]! + w[t - 7]! + shaSSig0 w[t - 15]! + w[t - 16]!
    expandScheduleLoop (t + 1) rem (w.push wt)

/-- Builds the 64-word message schedule `W[0..63]` from a block byte accessor. -/
def buildSchedule (byteAt : Nat → UInt8) : Array UInt32 :=
  let w0 := (Array.range 16).map (fun i => readWordBEAt byteAt (i * 4))
  expandScheduleLoop 16 48 w0

/-- Single SHA-256 compression round step. -/
@[inline] def sha256Round (st : Sha256State) (kVal wVal : UInt32) : Sha256State :=
  let t1 := st.h7 + shaBSig1 st.h4 + shaCh st.h4 st.h5 st.h6 + kVal + wVal
  let t2 := shaBSig0 st.h0 + shaMaj st.h0 st.h1 st.h2
  ⟨t1 + t2, st.h0, st.h1, st.h2, st.h3 + t1, st.h4, st.h5, st.h6⟩

def compressRoundsLoop (t rem : Nat) (w : Array UInt32) (st : Sha256State) : Sha256State :=
  match rem with
  | 0 => st
  | rem + 1 =>
    compressRoundsLoop (t + 1) rem w (sha256Round st sha256K[t]! w[t]!)

/-- Compresses a single 64-byte block given by `byteAt : Nat → UInt8`. -/
def compressBlockSpec (st : Sha256State) (byteAt : Nat → UInt8) : Sha256State :=
  let w := buildSchedule byteAt
  let r := compressRoundsLoop 0 64 w st
  ⟨st.h0 + r.h0, st.h1 + r.h1, st.h2 + r.h2, st.h3 + r.h3,
   st.h4 + r.h4, st.h5 + r.h5, st.h6 + r.h6, st.h7 + r.h7⟩

attribute [irreducible] expandScheduleLoop buildSchedule sha256Round compressRoundsLoop compressBlockSpec

def sha256SpecBlocks (padded : ByteArray) (nBlocks : Nat) (st : Sha256State) : Sha256State :=
  Nat.rec st (fun k acc => compressBlockSpec acc (fun j => padded.get! (k * 64 + j))) nBlocks

/-- Serializes the 8 state words into a 32-byte `Sha256Digest`. -/
def Sha256State.toDigest (st : Sha256State) : Sha256Digest :=
  ⟨ByteArray.mk #[
    (st.h0 >>> 24).toUInt8, (st.h0 >>> 16).toUInt8, (st.h0 >>> 8).toUInt8, st.h0.toUInt8,
    (st.h1 >>> 24).toUInt8, (st.h1 >>> 16).toUInt8, (st.h1 >>> 8).toUInt8, st.h1.toUInt8,
    (st.h2 >>> 24).toUInt8, (st.h2 >>> 16).toUInt8, (st.h2 >>> 8).toUInt8, st.h2.toUInt8,
    (st.h3 >>> 24).toUInt8, (st.h3 >>> 16).toUInt8, (st.h3 >>> 8).toUInt8, st.h3.toUInt8,
    (st.h4 >>> 24).toUInt8, (st.h4 >>> 16).toUInt8, (st.h4 >>> 8).toUInt8, st.h4.toUInt8,
    (st.h5 >>> 24).toUInt8, (st.h5 >>> 16).toUInt8, (st.h5 >>> 8).toUInt8, st.h5.toUInt8,
    (st.h6 >>> 24).toUInt8, (st.h6 >>> 16).toUInt8, (st.h6 >>> 8).toUInt8, st.h6.toUInt8,
    (st.h7 >>> 24).toUInt8, (st.h7 >>> 16).toUInt8, (st.h7 >>> 8).toUInt8, st.h7.toUInt8
  ], rfl⟩

/-- Canonical FIPS 180-4 SHA-256 specification over `ByteArray`. -/
def sha256Spec (b : ByteArray) : Sha256Digest :=
  let padded := sha256PadBytes b
  let nBlocks := padded.size / 64
  (sha256SpecBlocks padded nBlocks Sha256State.init).toDigest

end Leaf.Core
