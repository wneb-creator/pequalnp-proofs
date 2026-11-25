# Counterexample and finite-search snapshot

Snapshot UTC: 2026-11-25T01:36:03.652087+00:00

All files here are our mathematical search code or complete saved outputs. No solver binaries, third-party packages, credentials, or downloaded source are included. The Python SAT scripts need official Z3 5.3.3; the task used its Linux wheel from https://github.com/Z3Prover/z3/releases/tag/z3-5.3.3, unpacked outside the repository. Scripts currently use the task scratch path for outputs; run with `PYTHONPATH` including the script directory and an installed Z3 Python package.

Only the small-case BFS and successful Z3 verdicts are computational results. Timeouts mean unknown. None of the external UNSAT results is a Lean proof by itself. Explicit SAT witnesses are evaluated independently on full truth tables. The separate `lemmas/counterexample.lean` C5 circuit witness passed Lean and the standard-axiom audit.

The C5 compact `bv_decide` draft initially compiled, but its axiom audit found a generated native-verifier axiom outside the three allowed axioms. That Lean draft is deliberately excluded. Its failed audit survives only as plain text. No checked-certificate claim is made until kernel validation is repaired.

An initial automorphism/canonical-order query used inconsistent pair ordering and was interrupted before any verdict. `counterexample-canonical.stdout` is that abandoned run; corrected work is `counterexample-canonical-v2.stdout`. Larger canonical and local-cut portfolios were stopped on root request to keep SAT memory under 512 MB while Mathlib loads. Complete outputs retain their starting rows and any completed query verdicts.

Running processes at snapshot: [{'pid': 11559, 'log': 'counterexample-freeand.stdout'}]

Included file count: 63

Refresh UTC: 2026-11-25T01:39:07.338879+00:00
The freeAND/freeOR portfolios now have all recorded verdicts in their JSONL files. Every timedout query remains unknown.
