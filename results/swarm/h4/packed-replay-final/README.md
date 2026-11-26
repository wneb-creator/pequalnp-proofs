# H4 packed-checker replay artifacts

These Lean modules certify the exact node intervals listed in `manifest.json` and
`receipts/accepted-ranges.json`. The original assignment was 2304 through 3071, inclusive; the final
assigned interval ends at 2851 because another worker owns 2852 through 3071.
Only recorded accepted intervals are certified. The aggregate theorem
states the precise contiguous interval covered by those chunk lemmas.

The checker is frozen at commit
`36375ce3bb56c227c81ecae98f6641800006b8c2`, directory
`results/swarm/h8/certificate18`, in `wneb-creator/pequalnp-proofs`.
`checker-import-hashes.json` pins its required Lean sources and repository
dependencies; `checker-SHA256SUMS` preserves the original checkpoint manifest.
The entire forest has 5,230 nodes. Its closure still requires all other nodes.
These are research modules importing the frozen checker, not a complete gap proof.

Node assertions use `decide +kernel`. Compact chunks use `listPieces_all` to
partition the interval into leaves of at most four nodes. The aggregate theorem
uses accepted chunk lemmas, `List.mem_range'_1`, and the explicit identity
`Fin.ofNat 5230 i.val = i` for `i : Fin 5230`; it performs no new node evaluation.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted in the recorded
axiom audits.

## Rebuild

Use the pinned Lean toolchain and repository sources matching the recorded hashes.
Run `lake exe cache get` in the repository's `lean/` directory before the first
build. Do not build Mathlib from source or run `lake update`. Then build:

```sh
lake build PEqualNP.Outside.L_meta_6581
```

Extract the frozen h8 checker directory and run its reviewed `build.py` with
`--repo`, `--output` (a separate scratch basis directory), and `--lean` arguments.
Then run this bundle's serial builder:

```sh
python3 rebuild.py --repo '/path/to/repo' --basis '/tmp/packed-basis' --output '/tmp/h4-replay' --lean '/path/to/lean' --memory 6000
```

`--check-only` verifies the frozen source hashes without compiling. `--modules`
selects specific modules; otherwise the manifest supplies dependency order. The
last audit module prints the axioms of all delivered range and aggregate lemmas.
The builder writes complete stdout, stderr and resource JSON files for every
module. Compiled libraries are omitted from this bundle; recorded `.olean` hashes
identify the artifacts actually audited in the original run.

## Measurements

`logs/` retains complete compiler and axiom-audit output. `receipts/` records exit
statuses, wall/user/system time, memory caps and peak child RSS in KiB. The first
4-node and 32-node pilots ran with a 9,000 MB Lean cap. Subsequent replay workers
used the exact caps recorded in their receipts. Parallel runs were bounded by the
container's four-CPU and 16 GiB limits. The dependency and checker-basis measurements
are separate from node replay.

The publisher adds overall job timing and sub-agent measurements in `validation.txt`.
That run metadata is intentionally outside `SHA256SUMS`. Run `python3 verify.py`
to verify the immutable artifact hashes and exact interval metadata. The checksum
list is not a complete file census; publisher review metadata may be added without
changing the checked proof artifacts. The builder validates source identity and
expects checker libraries to have been freshly compiled from those sources.
