# CNF and LRAT preservation audit

Audited 2026-11-25 15:32 UTC at committed archive `406230d2`. The missing small reproduction inputs identified below were then copied exactly at the coordinator's request and passed its independent byte/hash review; the preservation commit follows. Preservation only: no new proof, compilation, or solver run.

## Preserved checked sources

All ten final sources below are tracked and byte-identical to their frozen, previously checked scratch originals. Complete successful stdout/stderr logs are tracked under `results/orch/validation/`.

| Archive source, relative to `results/orch/lemmas/` | Role | Validation log stem |
| --- | --- | --- |
| `checked/CompleteCNF.lean` | Arbitrary fan-in-two circuit to NOT-capable CNF | `complete-cnf` |
| `checked/PetersenCNF.lean` | Exact Petersen statement conditional on CNF unsatisfiability | `petersen-cnf` |
| `checked/PetersenReplay.lean` | Same statement conditional on successful packed LRAT replay | `petersen-replay` |
| `checked/AtMostThree.lean` | NOT-count preservation and at-most-three clauses | `at-most-three` |
| `checked/AtMostK.lean` | Conditional generic at-most-k completeness | `at-most-k-03` |
| `checked/ExactTwo.lean` | Conditional exactly-two completeness | `exact-two-01` |
| `checked/ReplayControls.lean` | Initial replay controls | `replay-controls` |
| `checked/ReplayKernelControls.lean` | Kernel-evaluated tiny positive/negative/sliced controls | `replay-kernel-controls` |
| `checked2590/NormalizedCNF.lean` | Arbitrary Monotone2 circuit normalization and exact enc2 completeness | `2590-normalized-cnf-01` |
| `checked2590/NormalizedReplay.lean` | Exact monotone Petersen statement conditional on successful replay | `2590-normalized-replay-01` |

The three reviewed Python tools are tracked byte-identically under `results/orch/tools/`: `lrat_pack.py`, `lrat_restart.py`, and `restart_tests.py`. The archive includes complete checkpoint/stitch/pack and restart-test logs, including an independent reviewer rerun.

These Lean sources are standalone snapshots, not an import chain: compile one directly from the repository's `lean/` directory with its pinned Lean 4.36.0 toolchain and cached Mathlib/Defs dependencies. For example:

```sh
lake env lean ../results/orch/lemmas/checked/PetersenReplay.lean > /tmp/petersen-replay.stdout 2> /tmp/petersen-replay.stderr
lake env lean ../results/orch/lemmas/checked/ReplayKernelControls.lean > /tmp/replay-controls.stdout 2> /tmp/replay-controls.stderr
lake env lean ../results/orch/lemmas/checked2590/NormalizedReplay.lean > /tmp/normalized-replay.stdout 2> /tmp/normalized-replay.stderr
```

No `lake update` or Mathlib source rebuild is required. An eventual acceptance computation must use kernel evaluation, such as the archived `decide +kernel` controls; `native_decide` and `bv_decide` are forbidden for this task. The snapshots prove conditional bridges, not the final gap statements without their remaining hypotheses.

## Small reproduction inputs restored after the audited commit

All 14 files (321,594 bytes) have exact source/archive paths, sizes, and SHA256 hashes in `results/orch/tools/fixtures/preservation-manifest.json`. They are frozen copies of existing inputs. Scratch base is `/tmp/oec/pequalnp-pilot-99/`.

* **Required for the archived Python test:** `sat_encoding/chain.cnf` and `sat_encoding/chain.lrat`, 33 bytes each, now copied beside `restart_tests.py` in `results/orch/tools/`.
* Tiny parser controls: `sat_encoding/toy.cnf`, `toy.lrat`, `toy-binary.lrat`, `toy-bad.lrat`, and `chain-binary.lrat`, 64 bytes total, now under `results/orch/tools/fixtures/`.
* Completed genuine restart fixture: `counterexample/restart-fixture/php8-7.cnf`, `prefix.lrat`, and `resumed.blrat`, now under `results/orch/tools/fixtures/restart/`; `sat_encoding/restart-fixture.cnf` and `.json` are preserved there as `checkpoint.cnf` and `.json`. These reproduce the logged 204-clause pigeonhole checkpoint, 27 retained learned clauses, 6,823 resumed additions, and 279,684 packed tokens. The full pigeonhole certificate was processed by untrusted Python tools; the archived Lean kernel controls are the tiny toy/chain fixtures.
* Exact Lean-to-DIMACS diagnostic: `gap2590/sat_encoding/DumpEncoding.lean` (1,154 bytes) and its empty `lean-enc2.stderr`, now under `results/orch/search_artifacts/gap2590/sat_encoding/`. Run it with `lake env lean --run PATH/TO/DumpEncoding.lean > OUTPUT.cnf 2> OUTPUT.stderr` from `lean/`. Its IO/string declarations belong in diagnostic artifacts, never in the proof PR file.

The diagnostic's previously produced bytes exactly matched the already tracked `results/orch/search_artifacts/gap2590/counterexample/petersen19-enc2.cnf`: 138,019 clauses, maximum variable 166,533, SHA256 `c34d684c7fd7ee2a38a0e3f205639b7be8fe762771a72781ffca28c84810f96d`. A second copy of the 5.6 MB generated CNF is unnecessary.

## Tool reproduction and limitations

Run `PYTHONDONTWRITEBYTECODE=1 python3 results/orch/tools/restart_tests.py` from the repository root. It creates only temporary test files and exercises rejected corrupt proofs as well as successful transport. The coordinator independently reran the restored archive: exit 0, ALL RESTART CONTROLS PASSED. Complete output is in validation/reproduction-restart-tests.stdout and .stderr; stderr is empty.

The interfaces below were confirmed using each tool's `--help`; output paths must be new. Substitute explicit input paths and save complete stdout/stderr:

```sh
python3 results/orch/tools/lrat_restart.py checkpoint ORIGINAL.cnf STOPPED_PREFIX.lrat CHECKPOINT.cnf MANIFEST.json
python3 results/orch/tools/lrat_restart.py stitch ORIGINAL.cnf STOPPED_PREFIX.lrat CHECKPOINT.cnf MANIFEST.json RESUMED.blrat STITCHED.blrat
python3 results/orch/tools/lrat_pack.py ORIGINAL.cnf COMPLETED.blrat PACKED.json --emit-lean PACKED.lean
```

The parser supports text/gzip and binary LRAT records. Restart transport validates the retained learned clauses and reconnects their IDs to the original proof; learned clauses never become additional assumptions of the final theorem. It rejects RAT/negative hints. The packer slices a completed refutation, validates RUP, remaps IDs, and packs tokens for the archived Lean checker. Python success is not kernel acceptance: `--emit-lean` deliberately emits data without an acceptance lemma. The kernel must still verify the concrete packed certificate against the exact original formula.

No completed Petersen UNSAT certificate exists in this archive. All 2592 searches and the 2590 baseline ended UNKNOWN or were stopped. The 1,689,837,568-byte 2590 trace and the large older 2592 prefixes are unverified, incomplete, and excluded from the tracked small archive. Neither an unfinished LRAT trace, an abstract code model, nor a restricted SAT control proves or refutes either posted statement. These limits are explicit in `results/orch/validation.txt`, the encoding notes, and the final search manifest.
