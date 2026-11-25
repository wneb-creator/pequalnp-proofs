# Independent reserve audit — 2026-11-25 UTC

Scope: read-only inspection of the unchanged checker, reviewed storage helpers,
existing small metadata, and checker008 logs. No production configuration or
artifact changed. This report is a conditional operating recommendation, not an
unconditional filesystem guarantee or a checker acceptance claim.

## Recommendation and gates

A 24 MiB internal guard (25,165,824 bytes) is reasonable **only if** a fresh model
from actual idle free space, all final packs/configuration/metadata already in
place, and a measured enter/restore smoke confirm the budget. Keep the original
transaction implementation and restore order, permit no unrelated disk writer,
and stop the resource monitor on checker completion or the six-hour task
deadline. Do not infer activation approval from this report alone.

32 MiB is not established by the currently reported deltas. Starting with
checker008's VERIFY free space gives this illustrative estimate:

    114,647,040 + 27,745,112 - 107,255,813 - 1,843,618
    = 33,292,721 bytes

This is 261,711 bytes below 32 MiB, before additional metadata/study costs and
block rounding. It is not a substitute for the fresh idle-based model.

The archive accounting matters: checker008's 114,647,040-byte VERIFY measurement
already included its active 11,598,035-byte journal. Archiving that journal frees
space while idle, but the next enter recreates a journal while keeping the
1,843,618-byte archive. Relative to the old VERIFY measurement, the archive is
an additional cost, not an idle-space gain that can be credited again.

## Writes at the low-space point

Paths below are relative to `/tmp/oec/pequalnp-pilot-45`, except the repository
checker path.

* `resource-wrapper/storage_phase.py:34` writes one `.new` JSON file, fsyncs it,
  replaces its destination, and fsyncs the parent. Existing destination bytes are
  already included in the free-space measurement. The temporary adds one JSON
  serialization, not two.
* `storage_phase.py:419` prepares first, writes the plan, removes backed-up build
  files, finishes backups, and only then evacuates RAM files. The 14,495,296-byte
  prepared manifest is rewritten before evacuation, while space is ample.
  `storage_phase.py:246` and `:249` perform journal/prepared replacements
  sequentially; they do not leave both temporary files resident.
* The final enter journal rewrite follows evacuation. The checker008 journal
  measured 11,598,035 bytes; use 12 MiB for this transient write, and recheck the
  new generation's serialized size. The prepared metadata had 28,998 rows and
  zero pending backups. The helper's existing pending-backup budget check at
  `storage_phase.py:431` remains necessary.
* `core-phase/core_phase.py:11`, `:99`, `:109`, and `:152` use one sequential
  atomic core-journal replacement. Current prepared metadata is 1,722,507 bytes;
  current transaction is 1,722,531 bytes. These temporary writes occur after
  the base enter temporary is gone, and are smaller than the 12 MiB allowance.
* `core_phase.py:110` restores raw core bytes directly to the owned memfds,
  then recreates symlinks. It does not write a raw disk copy. The 2,322 existing
  symlinks have zero allocated data blocks and target lengths at most20 bytes.
  Their77 existing parent directories occupy479,232 bytes in total. The new
  filename suffix is15 bytes; the longest original basename is38 bytes.
* `storage_phase.py:359` restores evacuated RAM copies before build artifacts;
  `storage_phase.py:461` selects RAM first, then build. Checker008's plan frees
  1,678,912,128 bytes of evacuated disk copies before rebuilding687,141,800 raw
  bytes. Raw reconstruction of the largest build artifact,238,458,224 bytes,
  therefore occurs after the low-space window. The final base journal rewrite
  likewise occurs after that restoration.

## Output and monitor growth

`tools/check-lean.mjs:146` uses synchronous captured subprocess output with a
64 MiB maxBuffer. At`:192` the caller is blocked in the verifier handoff.
`resource-wrapper/worker.py:61` runs enter, verifier, and then restore in a
finally block;`:77` waits for restore before returning the child result.
The handoff sends completion only afterward. `check-lean.mjs:199` forwards the
captured stdout/stderr only after this call returns. Thus normal native/helper
output does not grow the disk log while disk is tight. Initial checker progress
lines, the private statement copy, and fixed control files are small. A failed
restoration is not assumed to have completed; its fault output must remain
within the operating margin while recovery is performed.

`monitor-checker-loop.py:45` optionally includes Node memory fields, and`:57`
sleeps five seconds. Use a1 KiB/sample ceiling, rather than the observed421-byte
maximum from checker008. Six hours allows at most4,321 samples including the
initial sample:4,424,704 bytes, approximately4.22 MiB. Allocate4.25 MiB. The
monitor itself has no timeout; if its exit sentinel never appears and nobody
stops it, there is no finite unconditional log-growth bound. The six-hour
deadline/explicit monitor stop is part of this recommendation.

## Conservative simultaneous operating allowance

    12.00 MiB  largest low-space journal temporary
     4.25 MiB  bounded six-hour monitor, including optional Node fields
     6.00 MiB  filesystem metadata, directory/control files, rounding, fault text
    ---------
    22.25 MiB  total, leaving1.75 MiB below the proposed24 MiB guard

This deliberately adds the whole monitoring allowance to the largest journal
write, although the largest write occurs before native verification and later
core writes are much smaller. The6 MiB filesystem/control allowance exceeds the
observed core-directory allocation by more than12 times, but it is an explicit
engineering margin, **not a proved worst-case overlayfs metadata bound**. The
fresh transition smoke and its measured minimum free space are mandatory gates.
Account separately, before that smoke, for new packs, archived journals,
retained snapshots, new prepared/configuration files, and other completed
diagnostic output. No further writer should consume that margin during VERIFY.

Evidence read: checker-008.stderr, checker-008-resources.jsonl, the archived
checker008 journal metadata sidecar, current base/core prepared metadata and
current core journal. checker008's sampled minimum free space was114,642,944
bytes; its monitor contained37 samples. These are historical observations, not
measurements of the proposed new layout.
