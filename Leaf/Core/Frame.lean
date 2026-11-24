import Leaf.Core.Policy
import Leaf.Core.Crc32
import Leaf.Core.Codec

namespace Leaf.Core

/-- Discriminated magic kinds for framed storage files. -/
inductive FrameKind where
  | wal
  | segment
  | checkpoint
  | manifest
  deriving DecidableEq, BEq, Repr, Inhabited

namespace FrameKind

/-- Four-byte ASCII magic prefix identifying the file kind. -/
def magic : FrameKind → ByteArray
  | .wal        => "LFW1".toUTF8
  | .segment    => "LFS1".toUTF8
  | .checkpoint => "LFC1".toUTF8
  | .manifest   => "LFM1".toUTF8

theorem magic_size (k : FrameKind) : k.magic.size = 4 := by
  cases k <;> decide

end FrameKind

/-- Current binary framing version. -/
def frameFormatVersion : UInt16 := 1

/-- Fixed size of the unencrypted frame header (`magic..payloadLen`). -/
def frameHeaderSize : Nat := 28

/-- Total frame envelope overhead (28-byte header + 4-byte CRC32 trailer). -/
def frameOverhead : Nat := 32

/-- 28-byte record frame header. -/
structure FrameHeader where
  kind          : FrameKind
  formatVersion : UInt16 := frameFormatVersion
  recordType    : UInt8
  flags         : UInt8 := 0
  txId          : TxId
  seqNo         : SeqNo
  payloadLen    : UInt32
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Versioned, CRC32-authenticated framed binary record. -/
structure Frame where
  header  : FrameHeader
  payload : ByteArray
  deriving DecidableEq, BEq, Repr, Inhabited

namespace Frame

/-- Policy and structural validity predicate for encoding frames. -/
def Valid (policy : StoragePolicy) (f : Frame) : Prop :=
  f.header.formatVersion = frameFormatVersion ∧
  f.payload.size ≤ policy.maxFramePayloadBytes ∧
  f.header.payloadLen.toNat = f.payload.size

end Frame

/-- Encodes a 28-byte `FrameHeader`. -/
def encodeFrameHeader (h : FrameHeader) : ByteArray :=
  h.kind.magic ++
  encodeUInt16LE h.formatVersion ++
  encodeUInt8 h.recordType ++
  encodeUInt8 h.flags ++
  encodeTxId h.txId ++
  encodeSeqNo h.seqNo ++
  encodeUInt32LE h.payloadLen

theorem encodeFrameHeader_size (h : FrameHeader) : (encodeFrameHeader h).size = 28 := by
  unfold encodeFrameHeader
  have hm : h.kind.magic.size = 4 := h.kind.magic_size
  have hb : ∀ x : UInt8, (encodeUInt8 x).size = 1 := fun _ => rfl
  have hv : (encodeUInt16LE h.formatVersion).size = 2 := by
    simp only [encodeUInt16LE, ByteArray.size_append, hb]
  have ht : (encodeTxId h.txId).size = 8 := by
    simp only [encodeTxId, encodeUInt64LE, encodeUInt32LE, encodeUInt16LE, ByteArray.size_append, hb]
  have hs : (encodeSeqNo h.seqNo).size = 8 := by
    simp only [encodeSeqNo, encodeUInt64LE, encodeUInt32LE, encodeUInt16LE, ByteArray.size_append, hb]
  have hp : (encodeUInt32LE h.payloadLen).size = 4 := by
    simp only [encodeUInt32LE, encodeUInt16LE, ByteArray.size_append, hb]
  simp only [ByteArray.size_append, hm, hv, hb, ht, hs, hp]

/-- Encodes a frame unconditionally (`header ++ payload ++ crc32(header ++ payload)`). -/
def encodeFrameRaw (f : Frame) : ByteArray :=
  let body := encodeFrameHeader f.header ++ f.payload
  body ++ encodeUInt32LE (crc32 body)

/-- Policy-checked frame encoder verifying version, bounds, and length match. -/
def encodeFrame (policy : StoragePolicy) (f : Frame) : Except DecodeError ByteArray :=
  if f.header.formatVersion != frameFormatVersion then
    .error .unsupportedVersion
  else if f.payload.size > policy.maxFramePayloadBytes then
    .error .boundsExceeded
  else if f.header.payloadLen.toNat != f.payload.size then
    .error .lengthMismatch
  else
    .ok (encodeFrameRaw f)

theorem encodeFrame_ok {policy : StoragePolicy} {f : Frame} {out : ByteArray}
    (h : encodeFrame policy f = .ok out) :
    f.Valid policy ∧ out = encodeFrameRaw f := by
  unfold encodeFrame at h
  unfold Frame.Valid
  by_cases hfv : f.header.formatVersion == frameFormatVersion
  · simp only [bne_iff_ne, ne_eq, beq_iff_eq.mp hfv, not_true_eq_false, ↓reduceIte] at h
    by_cases hsz : f.payload.size > policy.maxFramePayloadBytes
    · simp [hsz] at h
    · simp only [hsz, ↓reduceIte] at h
      by_cases hlen : f.header.payloadLen.toNat == f.payload.size
      · simp only [beq_iff_eq.mp hlen, not_true_eq_false, ↓reduceIte, Except.ok.injEq] at h
        exact ⟨⟨beq_iff_eq.mp hfv, Nat.le_of_not_lt hsz, beq_iff_eq.mp hlen⟩, h.symm⟩
      · have hne : f.header.payloadLen.toNat ≠ f.payload.size := by
          simpa [beq_iff_eq] using hlen
        simp [hne] at h
  · have hne : f.header.formatVersion ≠ frameFormatVersion := by
      simpa [beq_iff_eq] using hfv
    simp [bne_iff_ne, hne] at h

/-- Total cursor-indexed frame decoder checking magic, version, policy bounds, truncation, and CRC32. -/
def decodeFrameAt (policy : StoragePolicy) (expectedKind : FrameKind) : Decoder Frame :=
  fun bytes pos => do
    let (magicBytes, pos1) ← decodeSliceAt bytes pos 4
    if magicBytes != expectedKind.magic then throw .invalidMagic
    let (formatVersion, pos2) ← decodeUInt16LEAt bytes pos1
    if formatVersion != frameFormatVersion then throw .unsupportedVersion
    let (recordType, pos3) ← decodeUInt8At bytes pos2
    let (flags, pos4) ← decodeUInt8At bytes pos3
    let (txId, pos5) ← decodeTxIdAt bytes pos4
    let (seqNo, pos6) ← decodeSeqNoAt bytes pos5
    let (payloadLen, pos7) ← decodeUInt32LEAt bytes pos6
    if payloadLen.toNat > policy.maxFramePayloadBytes then throw .boundsExceeded
    let (payload, pos8) ← decodeSliceAt bytes pos7 payloadLen.toNat
    let (storedCrc, pos9) ← decodeUInt32LEAt bytes pos8
    let computedCrc := crc32 (bytes.extract pos pos8)
    if computedCrc != storedCrc then throw .checksumMismatch
    let header : FrameHeader :=
      { kind := expectedKind, formatVersion, recordType, flags, txId, seqNo, payloadLen }
    return ({ header, payload }, pos9)

theorem decodeFrameAt_encodeFrameRaw_prefix (policy : StoragePolicy) (pfx rest : ByteArray)
    (f : Frame) (hf : f.Valid policy) :
    decodeFrameAt policy f.header.kind (pfx ++ encodeFrameRaw f ++ rest) pfx.size =
      .ok (f, pfx.size + (encodeFrameRaw f).size) := by
  rcases hf with ⟨hfv, hmax, hpl⟩
  cases f with | mk hdr payload =>
  cases hdr with | mk kind fv recType flags txId seqNo payLen =>
  dsimp only at hfv hmax hpl
  subst hfv
  let f0 := kind.magic
  let f1 := encodeUInt16LE frameFormatVersion
  let f2 := encodeUInt8 recType
  let f3 := encodeUInt8 flags
  let f4 := encodeTxId txId
  let f5 := encodeSeqNo seqNo
  let f6 := encodeUInt32LE payLen
  let hdr : FrameHeader :=
    ⟨kind, frameFormatVersion, recType, flags, txId, seqNo, payLen⟩
  let hdrEnc := encodeFrameHeader hdr
  let body := hdrEnc ++ payload
  let crcEnc := encodeUInt32LE (crc32 body)
  let enc := encodeFrameRaw ⟨hdr, payload⟩
  have hEncEq : enc = body ++ crcEnc := rfl
  have hHdrEq : hdrEnc = f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 := rfl
  have hEncExpand : enc = f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ payload ++ crcEnc := by
    dsimp only [enc, encodeFrameRaw, body, hdrEnc, encodeFrameHeader, hdr, crcEnc,
      f0, f1, f2, f3, f4, f5, f6]
  have hmg := decode_at_first (dec := fun bs p => decodeSliceAt bs p 4) (ea := f0) (x := f0)
    (fun p r => by simpa [f0, FrameKind.magic_size] using decodeSliceAt_prefix p f0 r)
    (enc := enc) (post := f1 ++ f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hfvD := decode_at_slice (dec := decodeUInt16LEAt) (ea := f1) (x := frameFormatVersion)
    (fun p r => decodeUInt16LEAt_encode_prefix p r frameFormatVersion)
    (enc := enc) (pre := f0) (post := f2 ++ f3 ++ f4 ++ f5 ++ f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hrec := decode_at_slice (dec := decodeUInt8At) (ea := f2) (x := recType)
    (fun p r => decodeUInt8At_encode_prefix p r recType)
    (enc := enc) (pre := f0 ++ f1) (post := f3 ++ f4 ++ f5 ++ f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hflg := decode_at_slice (dec := decodeUInt8At) (ea := f3) (x := flags)
    (fun p r => decodeUInt8At_encode_prefix p r flags)
    (enc := enc) (pre := f0 ++ f1 ++ f2) (post := f4 ++ f5 ++ f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have htx := decode_at_slice (dec := decodeTxIdAt) (ea := f4) (x := txId)
    (fun p r => decodeTxIdAt_encode_prefix p r txId)
    (enc := enc) (pre := f0 ++ f1 ++ f2 ++ f3) (post := f5 ++ f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hsq := decode_at_slice (dec := decodeSeqNoAt) (ea := f5) (x := seqNo)
    (fun p r => decodeSeqNoAt_encode_prefix p r seqNo)
    (enc := enc) (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4) (post := f6 ++ payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hlen := decode_at_slice (dec := decodeUInt32LEAt) (ea := f6) (x := payLen)
    (fun p r => decodeUInt32LEAt_encode_prefix p r payLen)
    (enc := enc) (pre := f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5) (post := payload ++ crcEnc)
    (pfx := pfx) (rest := rest) (by simpa [ByteArray.append_assoc] using hEncExpand)
  have hpay := decode_at_slice (dec := fun bs p => decodeSliceAt bs p payLen.toNat) (ea := payload) (x := payload)
    (fun p r => by simpa [hpl] using decodeSliceAt_prefix p payload r)
    (enc := enc) (pre := hdrEnc) (post := crcEnc)
    (pfx := pfx) (rest := rest) (by dsimp only [enc, encodeFrameRaw, body, hdrEnc, crcEnc])
  have hcrc := decode_at_last (dec := decodeUInt32LEAt) (ea := crcEnc) (x := crc32 body)
    (fun p r => decodeUInt32LEAt_encode_prefix p r (crc32 body))
    (enc := enc) (pre := body) (pfx := pfx) (rest := rest) hEncEq
  have hextract : (pfx ++ enc ++ rest).extract pfx.size (pfx.size + body.size) = body := by
    have hassoc : pfx ++ enc ++ rest = pfx ++ body ++ (crcEnc ++ rest) := by
      dsimp only [enc, encodeFrameRaw, body, hdrEnc, crcEnc]
      simp only [ByteArray.append_assoc]
    rw [hassoc]
    exact extract_append_middle pfx body (crcEnc ++ rest)
  have hnotGt : ¬ (payLen.toNat > policy.maxFramePayloadBytes) := by omega
  simp only [ByteArray.size_append, Nat.add_assoc] at hfvD hrec hflg htx hsq hlen hpay hcrc
  simp only [decodeFrameAt, Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw, MonadExcept.throw, MonadExceptOf.throw, throwThe]
  rw [hmg]; dsimp only
  simp only [f0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hfvD]; dsimp only
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hrec]; dsimp only
  rw [hflg]; dsimp only
  rw [htx]; dsimp only
  rw [hsq]; dsimp only
  rw [hlen]; dsimp only
  simp only [hnotGt, ↓reduceIte]
  have hpayPos : pfx.size + (f0.size + (f1.size + (f2.size + (f3.size + (f4.size + (f5.size + f6.size)))))) =
      pfx.size + hdrEnc.size := by
    simp only [hHdrEq, ByteArray.size_append, Nat.add_assoc]
  rw [hpayPos, hpay]; dsimp only
  have hbodyPos : pfx.size + (hdrEnc.size + payload.size) = pfx.size + body.size := by
    simp only [body, ByteArray.size_append]
  rw [hbodyPos, hcrc]; dsimp only
  rw [hextract]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  dsimp only [hdrEnc, hdr, crcEnc, body]
  simp only [encodeFrameRaw, ByteArray.size_append, Nat.add_assoc]

theorem decodeFrameAt_encodeFrame_prefix (policy : StoragePolicy) (pfx rest : ByteArray)
    (f : Frame) (enc : ByteArray) (henc : encodeFrame policy f = .ok enc) :
    decodeFrameAt policy f.header.kind (pfx ++ enc ++ rest) pfx.size =
      .ok (f, pfx.size + enc.size) := by
  have ⟨hfValid, hEq⟩ := encodeFrame_ok henc
  subst hEq
  exact decodeFrameAt_encodeFrameRaw_prefix policy pfx rest f hfValid

private theorem decodeUInt8At_eof_of_ge {bytes : ByteArray} {pos : Nat} (h : bytes.size ≤ pos) :
    decodeUInt8At bytes pos = .error .unexpectedEof := by
  unfold decodeUInt8At
  have hn : ¬ pos < bytes.size := by omega
  simp [hn]

private theorem decodeUInt16LEAt_eof_of_short {bytes : ByteArray} {pos : Nat} (h : bytes.size < pos + 2) :
    decodeUInt16LEAt bytes pos = .error .unexpectedEof := by
  unfold decodeUInt16LEAt decodeUInt8At
  by_cases h0 : pos < bytes.size
  · have h1 : ¬ pos + 1 < bytes.size := by omega
    simp [h0, h1, Bind.bind, Except.bind]
  · simp [h0, Bind.bind, Except.bind]

theorem decodeUInt32LEAt_eof_of_short {bytes : ByteArray} {pos : Nat} (h : bytes.size < pos + 4) :
    decodeUInt32LEAt bytes pos = .error .unexpectedEof := by
  unfold decodeUInt32LEAt
  by_cases h2 : bytes.size < pos + 2
  · rw [decodeUInt16LEAt_eof_of_short h2]; rfl
  · have h16 : ∃ lo, decodeUInt16LEAt bytes pos = .ok (lo, pos + 2) := by
      unfold decodeUInt16LEAt decodeUInt8At
      have h0 : pos < bytes.size := by omega
      have h1 : pos + 1 < bytes.size := by omega
      simp only [h0, h1, ↓reduceDIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨_, rfl⟩
    rcases h16 with ⟨lo, hlo⟩
    rw [hlo]; dsimp only [Bind.bind, Except.bind]
    rw [decodeUInt16LEAt_eof_of_short (by omega)]

theorem decodeFrameAt_short_header_error (policy : StoragePolicy) (kind : FrameKind)
    (bytes : ByteArray) (pos : Nat) (h : bytes.size < pos + 4) :
    decodeFrameAt policy kind bytes pos = .error .unexpectedEof := by
  unfold decodeFrameAt decodeSliceAt
  have hn : ¬ (pos + 4 ≤ bytes.size) := by omega
  simp [hn, Bind.bind, Except.bind]

theorem decodeFrameAt_truncated_payload_or_crc_error (policy : StoragePolicy) (kind : FrameKind)
    (bytes : ByteArray) (pos : Nat)
    (magicBytes : ByteArray) (pos1 : Nat)
    (hmDec : decodeSliceAt bytes pos 4 = .ok (magicBytes, pos1))
    (hmOk : magicBytes = kind.magic)
    (fv : UInt16) (pos2 : Nat)
    (hfvDec : decodeUInt16LEAt bytes pos1 = .ok (fv, pos2))
    (hfvOk : fv = frameFormatVersion)
    (recType : UInt8) (pos3 : Nat) (hrDec : decodeUInt8At bytes pos2 = .ok (recType, pos3))
    (flags : UInt8) (pos4 : Nat) (hflDec : decodeUInt8At bytes pos3 = .ok (flags, pos4))
    (txId : TxId) (pos5 : Nat) (htxDec : decodeTxIdAt bytes pos4 = .ok (txId, pos5))
    (seqNo : SeqNo) (pos6 : Nat) (hsqDec : decodeSeqNoAt bytes pos5 = .ok (seqNo, pos6))
    (payLen : UInt32) (pos7 : Nat) (hplDec : decodeUInt32LEAt bytes pos6 = .ok (payLen, pos7))
    (hplMax : payLen.toNat ≤ policy.maxFramePayloadBytes)
    (hPos7 : pos7 = pos + 28)
    (hTrunc : bytes.size < pos + 32 + payLen.toNat) :
    decodeFrameAt policy kind bytes pos = .error .unexpectedEof := by
  have hnotGt : ¬ (payLen.toNat > policy.maxFramePayloadBytes) := by omega
  simp only [decodeFrameAt, Bind.bind, Except.bind, hmDec, hmOk, bne_self_eq_false, ↓reduceIte,
    hfvDec, hfvOk, hrDec, hflDec, htxDec, hsqDec, hplDec, hnotGt]
  unfold decodeSliceAt
  by_cases hPay : pos7 + payLen.toNat ≤ bytes.size
  · simp only [hPay, ↓reduceIte]
    rw [decodeUInt32LEAt_eof_of_short (by omega)]
    rfl
  · simp only [hPay, ↓reduceIte]
    rfl

theorem decodeFrameAt_badCrc_error (policy : StoragePolicy) (kind : FrameKind)
    (bytes : ByteArray) (pos : Nat)
    (magicBytes : ByteArray) (pos1 : Nat)
    (hmDec : decodeSliceAt bytes pos 4 = .ok (magicBytes, pos1))
    (hmOk : magicBytes = kind.magic)
    (fv : UInt16) (pos2 : Nat)
    (hfvDec : decodeUInt16LEAt bytes pos1 = .ok (fv, pos2))
    (hfvOk : fv = frameFormatVersion)
    (recType : UInt8) (pos3 : Nat) (hrDec : decodeUInt8At bytes pos2 = .ok (recType, pos3))
    (flags : UInt8) (pos4 : Nat) (hflDec : decodeUInt8At bytes pos3 = .ok (flags, pos4))
    (txId : TxId) (pos5 : Nat) (htxDec : decodeTxIdAt bytes pos4 = .ok (txId, pos5))
    (seqNo : SeqNo) (pos6 : Nat) (hsqDec : decodeSeqNoAt bytes pos5 = .ok (seqNo, pos6))
    (payLen : UInt32) (pos7 : Nat) (hplDec : decodeUInt32LEAt bytes pos6 = .ok (payLen, pos7))
    (hplMax : payLen.toNat ≤ policy.maxFramePayloadBytes)
    (payload : ByteArray) (pos8 : Nat)
    (hpayDec : decodeSliceAt bytes pos7 payLen.toNat = .ok (payload, pos8))
    (storedCrc : UInt32) (pos9 : Nat)
    (hcrcDec : decodeUInt32LEAt bytes pos8 = .ok (storedCrc, pos9))
    (hMismatch : crc32 (bytes.extract pos pos8) ≠ storedCrc) :
    decodeFrameAt policy kind bytes pos = .error .checksumMismatch := by
  have hnotGt : ¬ (payLen.toNat > policy.maxFramePayloadBytes) := by omega
  simp only [decodeFrameAt, Bind.bind, Except.bind, hmDec, hmOk, bne_self_eq_false, ↓reduceIte,
    hfvDec, hfvOk, hrDec, hflDec, htxDec, hsqDec, hplDec, hnotGt, hpayDec, hcrcDec,
    Bool.false_eq_true, bne_iff_ne, ne_eq, hMismatch, not_false_eq_true, ↓reduceIte,
    throw, MonadExcept.throw, MonadExceptOf.throw, throwThe]

end Leaf.Core
