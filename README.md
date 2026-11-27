# Leaf

Leaf is a social journal and media application built entirely in **Lean 4 (`v4.37.0-rc1`)**, featuring a custom log-structured database engine, a content-addressed segmented object storage engine, a shared transaction manager, crash recovery, snapshot isolation, and machine-checked formal correctness proofs—with zero C/C++ shims, FFI, or external storage engines.

## Running Leaf

```sh
lake build
lake exe leaf
```

Open [http://127.0.0.1:8080/](http://127.0.0.1:8080/) to create, edit, delete, and paginate entries with JPEG, PNG, WebP, or GIF images (up to 10 MiB). On first startup against an existing `data/posts.db` + `data/images/` directory, Leaf automatically migrates legacy entries into the binary WAL and pack segments while keeping the legacy files intact as a read-only backup.

## Render Free deployment

The root `render.yaml` defines one Free Docker web service. When ready to deploy, push the project to a Git repository accessible to Render and select that repository when creating a Blueprint. The container uses Render's `PORT` and stores posts and images on the instance's ephemeral filesystem. Restarts, redeploys, and spin-downs erase that data. The Docker build excludes your local journal.

Point your external monitor at `GET https://<your-service>.onrender.com/healthz`. It returns HTTP 200 with the body `ok` once the store opens. A single continuously running instance uses at most 744 hours in a 31-day month. Render shares the 750 monthly Free instance hours across the workspace, so include any other Free web services when budgeting uptime. [Render Free service limits](https://render.com/docs/free)

## Storage Architecture

```text
data/
├── database/
│   ├── manifest.bin
│   ├── wal/
│   │   └── wal-000001.bin
│   └── checkpoints/
│       └── checkpoint-000001.bin
└── bucket/
    ├── manifest.bin
    └── segments/
        └── pack-000001.bin
```

- **Sequential `IO.FS` Design:** Because Lean's `IO.FS.Handle` does not expose arbitrary-offset `seek` or `fsync`, all writes are sequential appends + `flush` (with atomic temp-file + `IO.FS.rename` swaps for manifests, checkpoints, and recovery tail truncation). Object reads either hit the bounded in-memory segment cache (`segmentCacheCapacity = 4`, 16 MiB segments) or sequentially skip `offset` bytes before reading the exact frame.
- **Process-Crash vs. Power-Loss Durability:** Frame CRC32 checksums, SHA-256 + byte-equality verification, uncommitted-transaction filtering, and tail truncation protect against mid-write process crashes and file corruption. Because `IO.FS.Handle.flush` flushes user-space buffers without OS `fsync` or directory sync, sudden hardware power loss can still lose recently flushed writes.
- **Joint Transaction Manager & Snapshot Isolation:** Post mutations and object allocations share a single `Std.Mutex`-coordinated WAL (`beginTx`, `allocObject`, `putPost`/`updatePost`/`deletePost`, `incRef`/`decRef`, `commitTx`, `abortTx`). Readers run under `withSnapshot`, pinning referenced `ObjectKey`s so concurrent `runGC` or `compact` cannot reclaim objects while a reader is active.

## Formal Verification & Axiom Audit

Machine-checked proofs in `Leaf/Core/` verify the executable storage algorithms directly against their invariants with **no `sorry`, `admit`, custom axioms, or `native_decide`**:

- **Cryptography & Framing:** `Leaf/Core/Crc32.lean`, `Leaf/Core/Sha256.lean`, `Leaf/Core/Codec.lean`, `Leaf/Core/Frame.lean` (codec prefix-roundtrip proofs, frame CRC/EOF/version error proofs, NIST SHA-256 test vectors).
- **Database Correctness:** `Leaf/Core/DbModel.lean`, `Leaf/Core/WalLog.lean` (invariant preservation, read-after-write, primary-key uniqueness, descending `Pairwise`/`Nodup` feed ordering, cursor partition, compaction equivalence, uncommitted WAL transaction isolation).
- **Object Storage & Joint Store:** `Leaf/Core/BucketModel.lean`, `Leaf/Core/StoreModel.lean` (segment bounds safety, disjoint span allocation, deduplication & hash-collision safety, pin-aware GC soundness, cross-engine reference-count & abort isolation).

Run the axiom audit and all test suites:

```sh
lake build Tests.AxiomAudit
lake build core_tests storage_tests recovery_tests app_tests
lake exe core_tests
lake exe storage_tests
lake exe recovery_tests
lake exe app_tests
```

## HTTP & JSON Endpoints

| Route | Description |
| --- | --- |
| `GET /` | SSR journal feed (`?cursor=<ts>:<id>&limit=<n>`) |
| `GET /api/posts` | JSON paginated feed (`posts`, `nextCursor`) |
| `GET /api/posts/{id}` | JSON single post |
| `POST /posts` | Multipart create post + optional image |
| `POST /posts/{id}/edit` | Multipart update post / replace or remove image |
| `POST /posts/{id}/delete` | Delete post & decrement image refcount |
| `DELETE /api/posts/{id}` | JSON delete post |
| `GET /objects/{digestHex}/{tag}` | Content-addressed verified image stream |
| `GET /images/{id}` | Legacy image route by post ID |
| `POST /admin/{checkpoint,gc,compact}` | Manual checkpoint, GC, and compaction triggers |
