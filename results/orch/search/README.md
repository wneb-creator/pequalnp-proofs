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

Counterexample-agent status refresh UTC: 2026-11-25T02:01:46.857822+00:00

All counterexample-agent SAT processes have finished or were explicitly stopped; the earlier PID entry is historical. Separate agents may be running additional queries. Trusted C5 certificate work now uses `decide +kernel`, with per-case sources, complete logs, metrics and exact102-case coverage in `semantic-cases/`. This semantic method does not use the excluded native BV draft. The general L-meta-1031 graph statement remains unproved.

Prepared additional search source: `counterexample_freeand_private.py` (SHA256 9f571f48a5cfe831ad9a187007d04b29e665b46439d69f285c13d65147c60c7f). Python syntax was checked; no solver query from this script has run yet. It adds private negative witnesses for every selected conjunction atom to the disjoint-mask/positive-incomparability free-AND model. The mathematical argument minimizes total mask cardinality after OR count; removing a redundant selected atom leaves all negative signatures unchanged and increases positives. These normalization arguments are not yet formalized in Lean, so any future UNSAT verdict requires that caveat. The script has a portable CLI, supports two disjoint C5 components as a candidate, and independently evaluates any SAT witness on every Boolean input.

Normal-form private-conjunction search refresh UTC: 2026-11-25T02:20:37.130719+00:00

All queries in this batch have finished. C5 at most3OR returned external UNSAT (0.085s); C5 at most4OR returned SAT (0.018s), with all32 inputs independently replayed and zero errors. Petersen at most13OR returned UNKNOWN after600s (timeout); Fano at most19OR returned UNKNOWN after517.2s (256MB memory ceiling). The auxiliary theta233 all-OR-deletions-lose-two query returned UNKNOWN after90.1s. No lower bound or counterexample follows from the UNKNOWN results. The private-conjunction pruning and padding arguments are documented in `normal-form-private-justification.md`; their completeness is a mathematical argument, not a Lean theorem. The independent review by exchange found the script consistent with those arguments. No solver process from normal_form remains running.

Complete source and output manifest (SHA256):

- normal_form_private_sat.py e6999a640bcc9e1aa8a9791f5a26ed9aace3b3e95be1de1a8c907441a82c3d0a
- normal-form-private-justification.md 6b2e7432064a385eca4159667776f0e7caa29508c12e8eb2313239b3fe4a677f
- normal-form-private-results.jsonl fe02a318f98473a9c14e7d1be42dc1bc6222c3d0d7d8bbe904f63f8caa05a3fc
- normal-form-private.stdout ae48b1070a18d896960906c1987d91559c1801bd474d6243cf1dfcfcc3a27035
- normal-form-private.stderr e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
- normal-form-theta-elim.py c1ea43aad65603c78c7d718232f6366efdfde759956986db5e5cb98567f6bb74
- normal-form-theta-elim.json 7f61d06edde8ce30f13ac8ce78f4385b2dc9760c8145ede35c91a8de14bbbfea
- normal-form-theta-elim.stdout 82be1f7a9743b6a4a0af5fd39fdd586fd1f2e0058b5428ad4e25e8e60828a8be
- normal-form-theta-elim.stderr e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

Root follow-up searches (complete): free-AND two-C5 ≤8OR and C7 size10 with an unsound AND both timed out at180s. Strict signed-dominance two-C5 searches returned external UNSAT at exact4/5OR and UNKNOWN at6/7/8OR; no padding completeness or certified lower bound is claimed. C5 controls passed and the SAT witness was independently replayed over all32inputs. Independent normal_form source/result review PASS. Complete sources/stdout/stderr/JSONL are preserved under root-followup-search and root-signed-search names.

The optional counterexample_freeand_private.py CLI was syntax-checked but not executed; it supplies no additional result. All external SAT UNSAT results are distinct from the Lean kernel-certified semantic-cases directory.
