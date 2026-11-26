# Compact signed certificate work in progress

This modular research bundle does **not** prove L-meta-2373 or the unconditional
18-binary-gate lower bound. The complete 5,230-node forest still needs kernel
verification. The initial named helper file is separate and unchanged.

The following modules compiled successfully in this job:

- `Checker.lean`: one-step enumeration, collision cuts, paid-prefix projection
  cuts, all ten native cofactor maps, source bounds, symmetry transport and
  conditional forest soundness. Its 60-lemma pre-optimization snapshot passed
  an independent recursive axiom audit; subsequent fast table conversion has
  a checked equality proof and independent semantic review.
- `Half.lean`: soundness of checking only one operand order.
- `Initial.lean`: all ten inputs are necessary, plus the conditional bridge
  from a closed budget-17 forest to an 18-binary-gate floor.
- `PreparedLinks.lean`, `Coordinates.lean`, `SameSet.lean`: proved optimizations
  for symmetry links and Boolean set comparisons.
- `Replay.lean`: the complete assembled checker and compact data, including
  all 120 automorphism checks and conditional closure soundness. It compiles;
  the complete 5,230-node family remains to be established.
- `CheckNode.lean`: the original Boolean entry point for individual nodes.
- `BlockReplay.lean`, `DirectDecode.lean`, `DirectReplay.lean`: compiled block32
  projection-hint decoding and direct state decoding, with a conditional
  closure theorem for the resulting checker.
- `FullDataBlock0.lean`: an actual kernel proof of the root node using block32
  hints and the original state decoder.
- `DecodeHom.lean`, `LinkedReplay.lean`, `PreparedReplayLinks.lean`: optional
  proved symmetry-link replay tools. One measured node showed no speed gain.
- `Probe16.lean`: an actual kernel check of all first moves at budget 16.
  It is a smaller sanity check, not the budget-17 certificate.

`ReadyData.lean` is the 180,972-byte compact payload. Independent native
reconstruction checked all 5,230 states, 21,243 links, 29,197 projection hints
and 419 collision pairs. Component data files elaborate in Lean; that is
separate from accepting every forest node. Data and hints are untrusted inputs:
the generic proofs require the resulting Boolean checks to return true.

The original `manifest.json` pins the frozen, built core and its full logs.
`optimized-manifest.json` pins the subsequent direct-state/block32 modules and
complete build logs. `fast-manifest.json` pins the later cofactor/profile
optimization and its separate node measurements. All published files are listed in `SHA256SUMS`.
Large native traces and compiled libraries are deliberately absent.

## Reproduce the modular builds

Use the repository's pinned Lean version and its cached Mathlib dependencies.
Run `lake exe cache get` before the first build; do not build Mathlib from source.
From the repository's `lean/` directory, first build the existing dependency:

```sh
lake build PEqualNP.Outside.L_meta_6581
```

Then, from any working directory, use a separate scratch directory:

```sh
python3 /path/to/pequalnp-proofs/results/swarm/h8/certificate18/build.py --repo /path/to/pequalnp-proofs --output /tmp/cert18 --lean /path/to/lean
```

The builder invokes Lean directly using the existing library directories and
saves complete stdout/stderr per module. It serializes builds and defaults to
a 9,000 MB Lean limit because this job's container has 16 GiB total memory.
`--modules Probe16` reruns the smaller finite sanity check after the default
modules have been built in that same scratch directory. `--modules FullDataBlock0`
checks the compressed root. The optional symmetry modules must be built in order:
`--modules DecodeHom LinkedReplay PreparedReplayLinks`.

These are research modules: they import an existing Outside file and currently
use a small `State` structure. A final submission must inline its dependencies,
replace that structure with ordinary product types, satisfy the 512 KiB limit,
and prove the exact posted statement in the required single file.

## Individual node checks

After building the modules, create a small Lean file in the scratch directory:

```lean
import DirectReplay
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : checkNode 0 = true := by decide +kernel
```

All 5,230 directly decoded states and block32 hint rows match the native source
data in independent preflights. This is data validation, not a forest proof.
The actual compressed root check in `FullDataBlock0.lean` passed with about
49 seconds of kernel time. The direct-state checker compiles, but its complete
finite node family has not been proved.

Save the example as `/tmp/cert18/Node0.lean`. From the repository `lean/`
directory, run it with both library locations available:

```sh
lake env sh -c 'LEAN_PATH="/tmp/cert18:$LEAN_PATH" lean -M 11000 /tmp/cert18/Node0.lean' > /tmp/cert18/Node0.stdout 2> /tmp/cert18/Node0.stderr
```

A separate root-node check with literal projection hints and links passed in
52.97 seconds, with 8,324,364 KiB peak resident memory (about 7.94 GiB). This establishes one
node only. Checks using the compressed data also include decoder costs, and
large batches have not yet been benchmarked. Compile serially within a 16 GiB
container until representative checks establish a safe batch size.

## Measured cofactor and collision optimizations

The default build also includes `FastCofactorPools.lean`, `CollisionProfiles.lean`
and `FastDirect.lean`. Fast cofactor materialization is proved equal to the old
implementation; cached collision supports have their own soundness proof.
The resulting `profileClosed` still requires every one of the 5,230 node checks.

Actual compressed-data node 292 passed with fast cofactors in 23.52 seconds
(5,939,032 KiB peak RSS), and with collision profiles as well in 17.15 seconds
(5,075,116 KiB). Root node 0 also passed with both optimizations in 27.87 seconds
(5,576,916 KiB peak RSS). Additional nodes 2000, 4000 and 5229 passed in
6.68, 12.72 and 3.90 seconds respectively. These are individual serialized
measurements, not an estimate
of the entire forest. Sources and complete stdout/stderr are included. To
repeat the faster check after the default modules build, use
`--modules ProfileDirectNode292`. Its entry point is:

```lean
import FastDirect
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Fast
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : profileCheckNode 292 = true := by decide +kernel
```

## Packed collision signatures

The latest default checker adds `GenericDecodeHom.lean`, `PackedCollision.lean`,
`PackedRows.lean` and `PackedDirect.lean`. It evaluates collision coverage with
two 419-bit signatures per wire and replays those signatures from ten literal
input pairs. Lean verifies every target row pair and every literal input
signature. The generic proofs preserve the default reads and indexed removal
of the original state decoder; the child checker validates its new gate value.

`packed-manifest.json` pins this source and all build/benchmark logs. Five
individual compressed-data checks passed:

| Node | Wall time (seconds) |
| --- | ---: |
| 0 | 8.99 |
| 292 | 4.59 |
| 2000 | 3.60 |
| 4000 | 4.07 |
| 5229 | 2.44 |

The complete 5,230-node family remains unproved. The conditional theorem
`Packed.closed` requires that entire family. After the default build,
`--modules PackedDirect292` repeats the measured node check. The entry point is:

```lean
import PackedDirect
open PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : checkNode 292 = true := by decide +kernel
```

## Optional lookup experiment

`ArrayLookup.lean` and `ArrayDataLookup.lean` prove that list-based reads of
existing arrays preserve the packed checker exactly, including out-of-range
defaults. The latter covers pool block/row reads and parent block reads as well
as links. The pool atom dictionary already uses a packed integer and is
unchanged. These variants are optional; distributed replay uses the frozen
`PackedDirect` checker above.

One serialized comparison on node 292 measured 4.53 seconds for the baseline,
4.24 seconds for link lookups, and 4.19 seconds for all covered lookups.
This single comparison does not establish a general speedup. Source, complete
logs and metrics are pinned by `lookup-manifest.json`. After the default build,
use `--modules ArrayLookup ArrayDataLookup`, then choose one of
`PackedLookupBaseline292`, `ArrayLookupNode292` or `ArrayDataLookupNode292`.

## Verified helper range

`H8Range.lean` now proves every packed node check from 4608 through 5229,
inclusive: 622 nodes. All five bounded block proofs and the aggregate theorem
built successfully and use only `propext`, `Classical.choice` and `Quot.sound`.
The other nodes and the exact posted gap remain outside this result.

The replay took 657.16 seconds wall time with up to two proof processes; the
peak individual process RSS was 4,186,404 KiB. Full sources, logs, hashes and
per-process timing receipts are pinned in `range-manifest.json`; see also
`range-README.md`. The historical runner records job-specific scratch paths.
For portable reproduction, first use the default builder, then:

```sh
python3 /path/to/pequalnp-proofs/results/swarm/h8/certificate18/build.py --repo /path/to/pequalnp-proofs --output /tmp/cert18 --lean /path/to/lean --modules RangeAssembly H8Chunk4608 H8Chunk4736 H8Chunk4864 H8Parallel4992 H8Chunk4992 H8Parallel5120 H8Chunk5120 H8Range H8Axioms
```

The aggregate API is:

```lean
PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8.checked
  (i : Fin 5230) (lower : 4608 ≤ i.val) :
  PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.checkNode i = true
```
