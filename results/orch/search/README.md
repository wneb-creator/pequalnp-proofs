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

Additional normal_form search snapshot UTC: 2026-11-25T01:42:38.071725+00:00

C6 with at most4OR, friendship graph of two triangles with at most4OR, and C7 with at most5OR were externally UNSAT in the unrestricted-AND compact model (0.22s,0.16s,4.75s respectively). No extra pruning constraints were used; all four complete process files below were saved after exit0. These are external SAT results, not Lean proofs. The friendship graph is C4-free but has triangles, so its result is only an auxiliary comparison. The one process was capped at256MB and each query at120s.

Additional file manifest (4 files; SHA256):

- normal-form-freeand.py 964f1556689a8c65d3d50302eb0afc063fd13c1c427e87fe9b4f18a1719db723
- normal-form-freeand-results.jsonl 8d794cad23f21ce2094e7e294e03dc04e1fb45a51c1223d11d473a7608fe8274
- normal-form-freeand.stdout 41417c5da98a0c7f67d662a92bea238353ccffe49873d5ec70c2b4a608190b18
- normal-form-freeand.stderr e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
