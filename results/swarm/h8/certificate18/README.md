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
  the 5,230 individual node checks remain to be established.
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
