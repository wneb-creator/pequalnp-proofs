# Direct SAT completeness for L-meta-2592

A new generic bridge is compiled in `/tmp/oec/pequalnp-pilot-99/sat_encoding/CompleteCNF.lean` (529 lines). It adapts the direct model/valuation proofs of upstream `L_meta_5050.lean`, extending operation codes from AND/OR/TRUE to AND/OR/TRUE/NOT.

`circuit_sat` proves that every FanInTwo circuit of size at most s containing at least one NOT and computing a row function on any listed rows produces a satisfying assignment of `encN`. It makes no connectivity, output-last, nonconstant, fanin-order, topological-order, or exact-NOT-count assumptions. The proof handles empty AND/OR/NOT gates, unary gates, ignored second NOT operands, invalid/future reads, arbitrary output, unused gates and padding. `ofCirc_has_not` preserves original NOT existence, including a dead NOT.

Encoding: existing LratEncoding width/index/literal/source/output definitions; a four-operation ALO per gate; nine gate clauses (seven existing AND/OR/TRUE clauses plus two conditional NOT clauses); one final ALO asserting a NOT exists. No AMO constraints are necessary for completeness. Canonical Python generator `counterexample/canonical.py` was independently read and matches clause order and literal IDs. `canonical19.cnf` has 117946 clauses on the 91 rows consisting of all 76 independent assignments and 15 edge masks. Counterexample agent independently sanity-checked a 21-gate witness with a dead NOT and earlier output.

Compile result: `lake env lean CompleteCNF.lean`, exit 0. Complete logs: complete-cnf-02.stdout (warnings only), complete-cnf-02.stderr (empty). Uses only Mathlib and Defs; no axioms, native_decide, bv_decide, strings, or top-level code.

An UNSAT certificate for the exact canonical19 CNF now suffices to close the whole posted statement. Remaining work is computational UNSAT (or SAT counterexample), LRAT replay using the generic checker from L_meta_5531, and fitting certificate/source within 512 KiB and resource limits. Full proof would not need the large >=16 binary certificate, freeing most of the file budget. A Petersen-specific wrapper is being compiled separately in PetersenCNF.lean.

Final extension: `PetersenCNF.lean` now compiles (exit0, complete logs petersen-cnf-02.stdout/.stderr). It includes the exact91 rows from canonical19 metadata, the exact Petersen row function, kernel-checked row bounds, and `petersen_from_unsat` proving the exact posted statement from unsatisfiability of this single concrete CNF. Source is frozen for independent review. Generic LRAT replay from L_meta_5531 is RUP-only; the solver agent saw no negative hints in a100000-line prefix, but only a complete finished proof can establish compatibility. Raw LRAT is already hundreds ofMB, so backward slicing and dense-ID packing will be necessary if UNSAT appears. `bv_decide` is explicitly guard-forbidden and cannot replace the certificate route.

## Count bound and replay preparation

`AtMostThree.lean` compiles (at-most-three-03.stdout/.stderr). `ofCirc_notCount` proves exact preservation of NotBracket.notCount through bounded model extraction and TRUE padding. `circuit_sat_atMost3` maps a circuit with at most three NOTs to `encN ++ fAtMost3`, where fAtMost3 lists descending quadruples a<s,b<a,c<b,d<c and forbids all four from being NOT. For s=19 these are3876 clauses, matching canonical19-le3.cnf. The existing compiled16-binary bound supplies the at-most-three hypothesis for the genuine full Petersen function;91-row satisfaction alone is not claimed to imply that bound.

`PetersenReplay.lean` compiles (petersen-replay.stdout/.stderr). It appends the generic L_meta_5531 LRAT checker, with its anonymous noncomputable section named Replay for the current guard, then proves `petersen_of_certificate` from the kernel-checkable checkW=true condition. No certificate or UNSAT claim is present.

`lrat_pack.py` parses text or binary positive-hint LRAT, requires an empty final clause, slices backwards, rejects needed RAT hints, independently validates RUP propagation, removes no-op and post-conflict hints, renumbers retained derived IDs and packs≤1024 tokens per sentinel Nat. Initial IDs remain unchanged; a bitmap skips unused initial clauses. --emit-lean writes only data definitions, never an acceptance lemma. Independent status_review audit passed; binary parser agrees with official CaDiCaL lrattracer.cpp (https://github.com/arminbiere/cadical/blob/master/src/lrattracer.cpp, reviewed2026-11-25).

Positive text/binary fixtures produce identical tokens. Corrupted-hint fixture rejects. ReplayKernelControls.lean compiles with three kernel controls: a positive proof, corrupted negative proof, and a two-step proof with unused initial/derived clauses sliced away and retained IDs remapped. Use `decide +kernel` for replay; plain decide on the extended control grew to~5.7GB and that optional run was terminated. The minimal +kernel control finished successfully. Full logs remain in sat_encoding scratch. First1000 records of the actual binary≤3 run parsed successfully (922 additions,78 deletions,0 negative-hint records); this is only a prefix compatibility check, not a proof verdict.

No sat_encoding-owned Lean runs remain active. Root requested no new optional Lean runs while structural assembly uses the16GiB memory budget. All completed artifacts are frozen and ready for preservation. If a solver reports UNSAT, conversion can run without Lean, followed by root-scheduled kernel replay.

## 2026-11-25T14:34:01.791371+00:00 Generic NOT cardinality extension

Frozen compiled `/tmp/oec/pequalnp-pilot-99/sat_encoding/AtMostK.lean`, SHA256 `b97119bb6816c209b20628abac16cb7e61c6719f82faec2d7386de4125b8dcf2` (735 lines, 34746 bytes). Lean exited 0; full logs `sat_encoding/at-most-k-03.stdout` and `.stderr`. Independent reviewer notified.

Adds `decreasingLists`, `fAtMostK`, tuple length/distinctness/range proofs, and `circuit_sat_atMostK` conditional on the original circuit's NOT count being at most k. Uses the already checked exact `ofCirc_notCount` preservation. Concrete k=1 and k=2 equalities prove ascending outer loop with descending nested pair/triple indices; k=3 equals the previous `fAtMost3` exactly. Thus clauses match canonical.py without introducing connectivity, ordering, output, or circuit normal form assumptions.

Exact-two extension with conditional lower count bound is under separate validation in `ExactTwo.lean`; no full Petersen lower bound is claimed by this component.

## 2026-11-25T14:34:40.384651+00:00 Exactly-two NOT case compiled

Frozen compiled `/tmp/oec/pequalnp-pilot-99/sat_encoding/ExactTwo.lean`, SHA256 `f89dccb5c3e3d006d7b2fb22d9f74df4be0409664579107bdba1f8c4a5f58747` (784 lines, 36803 bytes). Lean exited 0 on the first run; complete logs `sat_encoding/exact-two-01.stdout` and `.stderr`. Root, counterexample agent, and independent reviewer notified immediately.

This extends frozen AtMostK.lean with `fAtLeast2` in canonical.py's precise order: j from 0 through s-1, clause negative N_j followed by positive N_k for every k≠j in ascending order. The finite cardinality proof finds a different NOT index for every j when the model contains at least two NOTs. `circuit_sat_exact2` proves completeness of `encN ++ fAtMostK 2 ++ fAtLeast2` conditional on the original circuit having exactly two NOTs. Together with k=1, these support the intended exactly-one/exactly-two split after a separate ≤2 structural bound is supplied. No solver UNSAT certificate currently exists; no full statement proof is claimed.

## 2026-11-25T14:40:18.712529+00:00 RUP restart/checkpoint provenance utility

Frozen untrusted data utility `/tmp/oec/pequalnp-pilot-99/sat_encoding/lrat_restart.py`, SHA256 `f4df39cec5a75c5a0412a39009a832e9f3021274e9379c489d217564def9da51`. Frozen tests `restart_tests.py`, SHA256 `dc87f5c8a05039845b3329da1ce9fd60aff9acb6f28abf7e83e4acce4e11e1bf`. Both preserve the existing Lean checker and existing lrat_pack.py unchanged. Reviewer notified; no new Lean build performed.

`checkpoint ORIGINAL_CNF STOPPED_PREFIX CHECKPOINT_CNF MANIFEST` reads text/binary LRAT, optionally gzip-compressed. It validates every addition as positive-hint RUP, tracks derived deletions, retains active learned clauses, and writes a hash-linked manifest. `--max-length` and `--max-learned` can select a smaller subset of active learned clauses; omitted means retain all. All negative/RAT hints are rejected, even if later irrelevant. Sources must be stopped and immutable; existing output paths are refused.

`stitch ORIGINAL_CNF STOPPED_PREFIX CHECKPOINT_CNF MANIFEST RESUMED_PROOF OUTPUT_BINARY_LRAT` revalidates prefix and resumed proof, verifies every learned input's content against its prefix proof ID, remaps resumed inputs/derived IDs, and emits original-prefix additions plus mapped resumed additions. Deletions can be dropped because all additions have RUP proofs. The resulting proof is packed against ORIGINAL_CNF, never CHECKPOINT_CNF: learned clauses remain proved facts, not assumptions. Failed stitching leaves only a `.partial` file, never publishes the final output path.

Genuine solver test (counterexample agent's pigeonhole8/7 fixture): original204 clauses; stopped text prefix100 additions,28 deletion records; checkpoint retains27 active learned clauses; resumed binary proof has6823 additions and solver UNSAT exit20. Stitched6923-addition proof validated and original-CNF packer accepted it, backward-slicing to6472 additions/279684 tokens. Full logs: `restart-checkpoint.stdout/.stderr`, `restart-stitch.stdout/.stderr`, `restart-pack.stdout/.stderr`. Original traces untouched.

Tiny restart test exercised gzip text prefix, deleted derived clause, nontrivial learned input ID remap, and binary resume. Its packed output equals the previously kernel-checked chain fixture exactly: tokens `[4,4,0,1,3,0,5,0,4,4,2]`, width3, packed word11342721572, original4 clauses. Negative controls reject RAT, invalid RUP, deleted hint, truncated binary, source hash mismatch, forged learned-clause content even with updated checkpoint hash, and incomplete continuation. Full tests exit0 in `restart-tests.stdout/.stderr`.
