namespace Leaf.Core

/-- Configurable policy parameters and static segment capacity invariants. -/
structure StoragePolicy where
  maxAuthorChars       : Nat := 80
  maxTitleChars        : Nat := 160
  maxCaptionChars      : Nat := 2000
  maxTags              : Nat := 16
  maxTagChars          : Nat := 32
  maxImageBytes        : Nat := 10 * 1024 * 1024
  segmentSize          : Nat := 16 * 1024 * 1024
  maxFramePayloadBytes : Nat := 15 * 1024 * 1024
  segmentCacheCapacity : Nat := 4
  imageFitsSegment     : maxImageBytes + 128 ≤ segmentSize := by decide
  frameFitsUInt32      : maxFramePayloadBytes + 128 ≤ 4294967295 := by decide

namespace StoragePolicy

/-- Default policy: 10 MiB max image, 16 MiB segments, 2000-char captions. -/
def default : StoragePolicy := {}

/-- Total byte overhead of a framed segment entry (`Frame` 32B + `ObjectKey` 40B + `MimeType` 1B + `len` 4B). -/
def segmentEntryOverhead : Nat := 77

theorem segmentEntryOverhead_le_reserve : segmentEntryOverhead ≤ 128 := by decide

end StoragePolicy

end Leaf.Core
