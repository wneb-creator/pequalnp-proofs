# Reversible cache compaction

This scratch tool preserves all runtime artifacts and stages an inactive storage generation. It never changes the production handoff or storage configuration, and never deletes an old backup pack. The selected rows are only Mathlib source and build cache files outside the independently validated compiled dependency closure of CheckLemma, PEqualNP.Defs, the candidate reduction, and Init.

The input settings, graphs, candidate census, source config, and storage implementation are pinned. The immutable transaction plan records every selected original byte hash, size, permission mode, and modification time. Before any unlink, both the current regular file and its existing compressed backup must match. Every old pack remains available for exact rollback.

Run each approved action separately with:

```
python3 -B /tmp/oec/pequalnp-pilot-45/build-cache-compaction/compact_cache.py --settings /tmp/oec/pequalnp-pilot-45/build-cache-compaction/settings.json ACTION
```

1. `snapshot`: copy-only preparation and full selected source/backup validation.
2. `prune`: remove only the exact planned cache paths; interrupted pruning is resumable.
3. `gate-prune`: run `lake build --no-build checklemma`, then `lake build --no-build +PEqualNP.Outside.R_meta_1768_45 +PEqualNP.Defs`. A failure restores all original selected files automatically.
4. `compact`: copy retained compressed frames into a new generation, rebuild both baseline inputs and prepared rows, and verify every retained decoded frame. Original compressed frame bytes are copied unchanged. The new lock is a hardlink to the original lock inode.
5. `verify`: rerun the generation's exact retained-set, metadata, decoded-frame, baseline, and lock checks.
6. `gate-stage`: rerun the exact two no-build commands.

`rollback` restores the exact original selected file bytes, mode, and mtime while preserving already matching files. It refuses changed originals and unsafe temporary files. It works after interrupted pruning or restoration, provided the original packs and config remain intact. An inactive staged generation does not affect this rollback.

The setup owner must separately validate `Storage.prepare` against the inactive generation and coordinate the core phase's `base_journal` reference with the base config. Activate a coherent new launcher/config pair by one atomic handoff change under the same lock. All original configs remain available for reverting that switch.

Actual reclamation is a separate, explicit decision after the no-build gates, independent complete new-pack verification, and coherent integration review. Deleting old packs ends the local exact rollback guarantee for discarded public cache files; no such deletion is implemented here. Preserve recovery provenance and all local-unique cache data. The projected generation saving excludes transaction snapshots, config copies, and later journals.

The twelve fixture tests cover complete compaction/rollback, partial prune, changed source, corrupt backup, failing no-build, safely regenerated cache files, protected runtime files, lock exclusion, interrupted rollback and metadata writes, unsafe temporary symlinks, and pinned inputs. Independent extra fixtures cover hardlinks and interrupted directory fsync.

## Separate retirement transition

`retire_generation.py` performs the explicitly authorized end of local rollback for discarded reproducible cache data. It derives exactly five obsolete paths from the pinned original config: both old packs, old prepared metadata, and old editor index/manifest. It never removes locks, original configs, or any replacement-generation data.

Its `prepare` action verifies pinned independent audits, no-build evidence, every replacement backup frame, all five old file identities/hashes, and the coherent replacement config pair. It preserves exact old index/manifest bytes as verified gzip, verifies the prepared gzip reconstructs the exact original bytes (otherwise making a separate exact snapshot), and atomically preserves the old handoff bytes. Preparation does not activate or delete anything.

After independent archive review, `run` repeats the guards under the shared phase lock, requires all runtime journals absent or restored, atomically installs the exact staged coherent handoff, and only then unlinks the five old files. A durable intent record precedes every unlink; interruptions before/after activation and before/after unlink can be retried with the same pinned settings. Unexpected old-file identities, changed replacement bytes, or changed recovery snapshots stop the operation.

Invoke either action with `--settings retirement-settings.json --settings-sha256 <the independently reviewed current SHA256>`. The setup owner serializes this transition with all Lean/native activity and runs the final no-build audit afterward. The helper's eleven fixture cases plus independent destructive-edge tests exercise complete and interrupted transitions, corrupted originals/replacements/recovery copies, wrong lock identity, active journals, and unsafe backup links.
