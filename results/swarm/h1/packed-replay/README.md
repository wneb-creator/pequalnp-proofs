# Helper 1 packed certificate replay

This is a partial research checkpoint for L-meta-2373. It does not prove the
full gap or close the complete 5,230-node forest. `manifest.json` records the
exact accepted interval and individual build receipts. Only batches with an
exit-zero build and permitted recursive axiom reports are included.

All 768 assigned states, indices 768 through 1535, are now checked. The
aggregate theorem in `PackedH1Aggregate.lean` is
`PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks.Aggregate.checked`:
for `i : Fin 5230`, hypotheses `768 ≤ i.val` and `i.val < 1536` imply
`checkNode i = true`. It imports the 24 accepted chunk proofs; its build and
axiom audit also passed. This is still only part of the complete forest.

The checker dependency is pinned to helper 8 commit
`36375ce3bb56c227c81ecae98f6641800006b8c2`, directory
`results/swarm/h8/certificate18`. Its entry point is
`PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.checkNode`.
The dependency is not duplicated here. Its complete forest closure theorem
still requires every node from 0 through 5229.

Each published chunk proves both a Boolean check of its literal interval and
the corresponding bounded theorem for `i : Fin 5230`. The range wrapper proves
that the modular `Fin.ofNat` expression equals `i` under the stated bounds.
The chunks use `decide +kernel`, split into leaves of at most four nodes.
They use no native decision axiom. Sources retain their `#print axioms`
commands because this is a research bundle, not a single-file submission.

## Reproduce

Use the repository's pinned Lean 4.36.0 toolchain and cached Mathlib. Run
`lake exe cache get` before the first build, then build the existing
`PEqualNP.Outside.L_meta_6581` dependency from the repository's `lean/`
directory. Do not build Mathlib from source.

Obtain the pinned helper 8 directory from that exact Git commit and build its
19 default modules into a separate scratch directory with its `build.py`:

```sh
python3 /path/to/pinned/certificate18/build.py --repo /path/to/pequalnp-proofs --output /tmp/cert18 --lean /path/to/lean --memory 9000
```

Then replay these published sources serially in that same scratch directory:

```sh
python3 /path/to/packed-replay/replay.py --repo /path/to/pequalnp-proofs --build /tmp/cert18 --lean /path/to/lean --memory 7000
```

The script verifies published and dependency source hashes, builds the shared range wrapper,
and rebuilds every included chunk. It saves complete stdout and stderr and a
new replay receipt in the scratch directory. Build the imported checker modules
fresh from their pinned sources first: this script does not authenticate existing
dependency binaries. `--modules` can select specific
published chunk names. Existing scratch outputs with these names are replaced.
Add `--verify-only` to check the toolchain and source pins without writing or
starting a build.

After all chunks have been rebuilt, copy the aggregate source into the same
scratch directory and compile it. Run the `lake` command from the repository's
`lean/` directory, with the pinned toolchain available on `PATH`:

```sh
cp /path/to/packed-replay/PackedH1Aggregate.lean /tmp/cert18/PackedH1Aggregate.lean
lake env sh -c 'cd /tmp/cert18 && LEAN_PATH="/tmp/cert18:$LEAN_PATH" lean -j 1 -M 7000 -o PackedH1Aggregate.olean PackedH1Aggregate.lean' > /tmp/cert18/PackedH1Aggregate.replay.stdout 2> /tmp/cert18/PackedH1Aggregate.replay.stderr
```

`replay.py` rebuilds the wrapper and chunks; the command above performs the
separate aggregate step. Its source and recorded outputs are pinned in the
manifest's `aggregate` entry and in `SHA256SUMS`.

The shared 19-module checker build passed using a 9,000 MB Lean setting. Its
peak RSS was not measured, and rebuilding it with a 7,000 MB setting has not
been tested. Use sufficient memory for that separate dependency build.

The original worker has an enforced 8 GiB memory limit and two CPUs. Replay
was serial; the first three accepted batches used Lean's 9,000 MB setting,
then the setting was reduced to 7,000 MB. Actual peak RSS and per-batch limits
are recorded in the manifest. The manifest's top-level elapsed time measures
only its latest resumed segment; sum the batch times for cumulative build
time. Local `.olean` hashes identify the observed outputs; binaries are not
included, and reproducibility depends on rebuilding from source.

The separate helper theorem file remains at
`lean/PEqualNP/Outside/L_meta_2373.lean`. Its named build and independent
reviews passed. Neither that auxiliary library nor these partial replay
receipts have an official full-gap checker acceptance.
