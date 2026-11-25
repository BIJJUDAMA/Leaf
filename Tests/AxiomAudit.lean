import Leaf.Core

open Leaf.Core

-- CRC32
#print axioms crc32_eq_spec
#print axioms crc32_test_vector

-- SHA-256
#print axioms sha256_eq_spec
#print axioms sha256_digest_size
#print axioms sha256_deterministic
#print axioms sha256_empty_vec
#print axioms sha256_abc_vec
#print axioms sha256_448bit_vec

-- Codec
#print axioms decodePostAt_encode_prefix
#print axioms decodeWalOpAt_encode_prefix
#print axioms decodeBucketSegmentRecordAt_encode_prefix
#print axioms decodeDbManifestAt_encode_prefix
#print axioms decodeBucketManifestAt_encode_prefix
#print axioms decodeDbCheckpointAt_encode_prefix

-- Frame
#print axioms encodeFrameHeader_size
#print axioms encodeFrame_ok
#print axioms decodeFrameAt_encodeFrame_prefix
#print axioms decodeFrameAt_short_header_error
#print axioms decodeFrameAt_truncated_payload_or_crc_error
#print axioms decodeFrameAt_badCrc_error

-- DbModel
#print axioms DbState.empty_invariant
#print axioms DbState.createPost_preserves_invariant
#print axioms DbState.updatePost_preserves_invariant
#print axioms DbState.deletePost_preserves_invariant
#print axioms DbState.compactDb_preserves_invariant
#print axioms DbState.createPost_getPost_self
#print axioms DbState.updatePost_getPost_self
#print axioms DbState.deletePost_getPost_self
#print axioms DbState.pk_uniqueness
#print axioms DbState.queryFeed_pairwise_desc
#print axioms DbState.queryFeed_nodup_ids
#print axioms DbState.queryFeed_excludes_deleted
#print axioms DbState.queryFeed_cursor_partition
#print axioms DbState.compactDb_equiv

-- BucketModel
#print axioms BucketState.empty_invariant
#print axioms BucketState.putObject_preserves_invariant
#print axioms BucketState.incRef_preserves_invariant
#print axioms BucketState.decRef_preserves_invariant
#print axioms BucketState.gcStep_preserves_invariant
#print axioms BucketState.compactBucket_preserves_invariant
#print axioms BucketState.alloc_disjoint
#print axioms BucketState.putObject_dedup_sound
#print axioms BucketState.putObjectWithHash_collision_safe
#print axioms BucketState.putObjectWithHash_preserves_blobs
#print axioms BucketState.gcStep_preserves_live
#print axioms BucketState.gcStep_reclaims_unreferenced
#print axioms BucketState.compactBucket_equiv

-- StoreModel
#print axioms StoreState.empty_invariant
#print axioms StoreState.beginTx_preserves_invariant
#print axioms StoreState.stageImage_preserves_invariant
#print axioms StoreState.commitCreate_preserves_invariant
#print axioms StoreState.commitUpdate_preserves_invariant
#print axioms StoreState.commitDelete_preserves_invariant
#print axioms StoreState.abortTx_preserves_invariant
#print axioms StoreState.abortTx_preserves_committed
#print axioms StoreState.runGC_preserves_invariant
#print axioms StoreState.runCompact_preserves_invariant

-- WalLog & BoundedCache
#print axioms DbState.applyCommittedWalOp_preserves_invariant
#print axioms DbState.replayWalOps_preserves_invariant
#print axioms DbState.replayWalOps_uncommitted_ignored
#print axioms BoundedCache.insert_length_le
#print axioms BoundedCache.insert_lookup_self
#print axioms filterPinnedObjects_preserves_live_or_pinned
