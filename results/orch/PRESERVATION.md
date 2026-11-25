# L-meta-2592 partial research archive

The full posted statement is not proved or refuted. No proof PR was opened.
The strongest checked result is lemmas/BinarySeventeen.lean: every computing fan-in-two circuit satisfies17+notCount<=size. This excludes three or more NOT gates at total size19, leaving one and two NOT gates.

validation.txt and status_review.md identify checked components and their limits. Test harnesses import BinarySeventeen from a separately emitted local olean; these imports are development scaffolding, not final PR imports. Files ending Suffix.lean are integration fragments, not independent modules. Semantic.lean is an earlier source-reviewed draft with no standalone successful build recorded. SignedRestriction.lean and FirstGate.lean are superseded structure-based development versions; use the plain versions for integration. NotBudget.lean duplicates the checked one-step development. Research scripts, conjectural notes, and interrupted searches are not Lean proofs.

combinatorial_edge_depth5.json.gz is a complete checkpoint of3202 edge-first-OR states through depth5. Depth6 was interrupted; its observed771 children are not a complete certificate and were not saved as a checkpoint. counterexample_checkpoint.txt preserves complete captured solver output. No valid full counterexample or full-target UNSAT certificate was obtained.

beat-014-diagnostic.txt contains the full desk HTTP410 response. desk-log.txt records all requests through the failed renewal. Proof work paused at that error. Recovery is attempted only after this archive is pushed.

Additional complete intermediate mixed depth4/depth5 search snapshots are preserved losslessly as combinatorial_mixed_depth4.json.gz and combinatorial_mixed_depth5.json.gz. Original SHA256 values: depth4 a861701b0c05cce5464beb0fe45206abcbf2e8addaacc5f0418a5219db1617e9; depth5 c48895ce7f8eb4c9e8383c5ab4caa6ce7ed33bdbcfa3a8d810724dac773ce138. They are research checkpoints, not formal certificates. Root verified decompression byte equality before removing the large scratch copies.
