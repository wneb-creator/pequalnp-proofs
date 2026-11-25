# Shared-library storage fallback: review candidate

This candidate has not been activated against installed artifacts. Tests use
only tiny temporary files and new memfds owned by the test process. A standalone
entry point is available for independent review; no live configuration exists.

`storage_phase_base.py` is an unchanged copy of the previously reviewed storage
implementation, pinned by SHA256 in the subclass. `storage_phase.py` subclasses
that implementation and reuses its durable backup, journal, evacuation and
restoration methods.

The ordinary base configuration is extended with:

- `fallback_schema: 1`, mandatory.
- `shared_library_whitelist`: either empty or exactly two records naming
  `<toolchain_root>/lib/lean/libleanshared.so` and
  `<toolchain_root>/lib/lean/libLake_shared.so`. Each record contains `path`,
  `size`, `sha256`, `mode`, and `mtime_ns`. Paths must be normalized absolute
  paths and actual artifacts must be regular files with those bytes/metadata.
- `retained_core_whitelist`: selected runtime records with the same content
  fields plus `pid`, `fd`, `target`, `fd_dev`, `fd_ino`, and
  `symlink_mtime_ns`. Each must occur
  consistently in the base `ram_manifests`, remain an exact original memfd
  symlink, and have a unique backing identity. No extra core path is eligible.
- `retained_core_source_manifest`: one `{path, sha256}` pin for an audited JSON
  object with a `files` array of canonical retained-core records. It may contain
  a candidate superset; every selected whitelist row must agree with its source
  record. The manifest hash is checked again during planning.
- `excluded_core_manifests`: a list of `{path, sha256}` pins for audited JSON
  manifests. Their `files` records must carry `path` and either
  `fd_dev`/`fd_ino` or `device`/`inode`. Any selected path/backing overlap fails
  before a storage transaction is entered.

The external handoff supervisor remains responsible for capturing the unchanged
native invocation and restoring artifacts before any later build. This code
also refuses enter/restore while Lean, Lake, or checklemma is live, and compares
owned-process mapping device/inode pairs before deleting either selected shared
library or truncating/restoring selected core memfds. It rejects inaccessible
owned-process maps instead of assuming they are safe. It captures shared-library
inodes during preparation and checks them again before deletion. Added core
symlinks regain their pinned own mtime after restoration. A shared exclusive
`phase_lock` may be supplied in configuration; otherwise the state-directory lock
is used. The supervisor must use the same lock to prevent another build starting
between the guard and mutation.

No checker, proof, library bytes or Lean environment settings are modified.
Runtime artifacts are evacuated as exact regular disk copies and subsequently
restored through the original memfd mechanism. Selected shared libraries use
the original durable compressed-backup mechanism and exact restoration checks.

Run the harmless tests with `python3 test_fallback.py` from this directory.
The full updated test output is in `tests-003.stdout` and `tests-003.stderr`. Cases include
including complete and partial transactions, idempotent restoration, exact
path/pin enforcement, excluded backing aliases, corrupt-backup refusal, real
tiny mmap guards, same-byte inode substitution, and the standalone config pin.

The command shape is:

```
python3 storage_phase.py --config /absolute/reviewed/config.json --config-sha256 HASH prepare
python3 storage_phase.py --config /absolute/reviewed/config.json --config-sha256 HASH enter
python3 storage_phase.py --config /absolute/reviewed/config.json --config-sha256 HASH restore
```

The two shared libraries must retain their audited size, hash, mode and target
mtime. Their original inode number is checked before removal but naturally
changes when a regular file is recreated from backup; the next prepare captures
the new identity. The original source copy remains byte-for-byte unchanged.

Independent source review and a separately authorized integration plan are
still required before any production activation.
