import Leaf.Core.Frame

namespace Leaf.Storage

open Leaf.Core

/-- Formats a 64-bit sequence number as a zero-padded 6-digit string (e.g. `1 -> "000001"`). -/
def zeroPad6 (n : UInt64) : String :=
  let s := toString n
  if s.length >= 6 then s
  else String.ofList (List.replicate (6 - s.length) '0') ++ s

def walFileName (walId : UInt64) : String :=
  s!"wal-{zeroPad6 walId}.bin"

def checkpointFileName (ckptId : UInt64) : String :=
  s!"checkpoint-{zeroPad6 ckptId}.bin"

def packFileName (segId : SegmentId) : String :=
  s!"pack-{zeroPad6 segId.val}.bin"

/-- Sequentially reads and discards `n` bytes from an open handle without allocating an `n`-byte buffer. -/
partial def discardBytes (h : IO.FS.Handle) (n : Nat) (chunkSize : USize := 65536) : IO Bool := do
  let mut rem := n
  while rem > 0 do
    let want : USize := if rem < chunkSize.toNat then rem.toUSize else chunkSize
    let buf ← h.read want
    if buf.isEmpty then
      return false
    rem := rem - buf.size
  return true

/-- Sequentially reads up to `n` bytes from an open handle. -/
partial def readExact (h : IO.FS.Handle) (n : Nat) (chunkSize : USize := 65536) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut rem := n
  while rem > 0 do
    let want : USize := if rem < chunkSize.toNat then rem.toUSize else chunkSize
    let buf ← h.read want
    if buf.isEmpty then
      break
    acc := acc ++ buf
    rem := rem - buf.size
  return acc

/-- Opens `path` sequentially, skips `offset` bytes, and reads `length` bytes. -/
def readAtOffset (path : System.FilePath) (offset length : Nat) : IO (Except String ByteArray) := do
  try
    let h ← IO.FS.Handle.mk path .read
    let skipped ← discardBytes h offset
    if !skipped then
      return .error s!"unexpected EOF while skipping {offset} bytes in {path}"
    let bytes ← readExact h length
    if bytes.size != length then
      return .error s!"short read in {path}: expected {length} bytes, got {bytes.size}"
    return .ok bytes
  catch e =>
    return .error s!"readAtOffset({path}) failed: {e}"

/-- Encodes and appends a frame to `path`, flushing the handle, and returns `(startOffset, frameByteLength)`. -/
def appendFrame (path : System.FilePath) (currentSize : Nat) (pol : StoragePolicy)
    (kind : FrameKind) (recordType : UInt8) (txId : TxId) (seqNo : SeqNo)
    (payload : ByteArray) : IO (Except String (Nat × Nat)) := do
  if payload.size ≥ 2 ^ 32 then
    return .error "frame payload exceeds UInt32"
  let hdr : FrameHeader :=
    { kind := kind
      formatVersion := frameFormatVersion
      recordType := recordType
      flags := 0
      txId := txId
      seqNo := seqNo
      payloadLen := payload.size.toUInt32 }
  let frame : Frame := ⟨hdr, payload⟩
  match encodeFrame pol frame with
  | .error e => return .error s!"encodeFrame failed: {repr e}"
  | .ok bytes =>
    try
      let h ← IO.FS.Handle.mk path .append
      h.write bytes
      h.flush
      return .ok (currentSize, bytes.size)
    catch e =>
      return .error s!"appendFrame({path}) failed: {e}"

/-- Writes a single-frame file atomically via `tmpPath`, flush, and `IO.FS.rename`. -/
def writeFramedFileAtomic (tmpPath finalPath : System.FilePath) (pol : StoragePolicy)
    (kind : FrameKind) (recordType : UInt8) (txId : TxId) (seqNo : SeqNo)
    (payload : ByteArray) : IO (Except String Unit) := do
  if payload.size ≥ 2 ^ 32 then
    return .error "framed file payload exceeds UInt32"
  let hdr : FrameHeader :=
    { kind := kind
      formatVersion := frameFormatVersion
      recordType := recordType
      flags := 0
      txId := txId
      seqNo := seqNo
      payloadLen := payload.size.toUInt32 }
  let frame : Frame := ⟨hdr, payload⟩
  match encodeFrame pol frame with
  | .error e => return .error s!"encodeFrame failed: {repr e}"
  | .ok bytes =>
    try
      do
        let h ← IO.FS.Handle.mk tmpPath .write
        h.write bytes
        h.flush
      IO.FS.rename tmpPath finalPath
      return .ok ()
    catch e =>
      return .error s!"writeFramedFileAtomic({finalPath}) failed: {e}"

/-- Reads and verifies a single-frame file (`manifest.bin`, `checkpoint-XXXXXX.bin`). -/
def readFramedFile (path : System.FilePath) (pol : StoragePolicy)
    (expectedKind : FrameKind) : IO (Except String Frame) := do
  try
    let bytes ← IO.FS.readBinFile path
    match decodeFrameAt pol expectedKind bytes 0 with
    | .error e => return .error s!"decodeFrameAt({path}) failed: {repr e}"
    | .ok (frame, _) => return .ok frame
  catch e =>
    return .error s!"readFramedFile({path}) failed: {e}"

/-- Atomically rewrites `finalPath` with `bytes` via `tmpPath` + flush + `IO.FS.rename`.
    Used to truncate corrupt/partial trailing bytes during crash recovery. -/
def rewritePrefixAtomic (tmpPath finalPath : System.FilePath) (bytes : ByteArray) :
    IO (Except String Unit) := do
  try
    do
      let h ← IO.FS.Handle.mk tmpPath .write
      h.write bytes
      h.flush
    IO.FS.rename tmpPath finalPath
    return .ok ()
  catch e =>
    return .error s!"rewritePrefixAtomic({finalPath}) failed: {e}"

end Leaf.Storage
