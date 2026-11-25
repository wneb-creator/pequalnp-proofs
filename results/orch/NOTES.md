# L-meta-2592 orchestration notes

Root holds the sole lease for this job. Agents must not call the desk.

Target: Petersen edge function requires more than 19 fan-in-two gates when the circuit contains a NOT. A known monotone construction uses 20 gates. Reductions open, but 3 reductions already live.

Strategies: status_and_review = existing lemmas and independent review; counterexample_search = circuit constructions and SAT; root = formal proof integration and lease control.

## status_and_review findings 2026-11-25T14:03:16.688569+00:00
- L-meta-1035 is public-map status j (conjecture), not refuted or checked, in head snapshot 2026-11-25T13:58:57Z; current lease occupancy unavailable. No matching PR/local-history result in initial checks.
- R_meta_2592_271 splits binary floor (15 + notCount ≤ size) and exclusion for 1–4 NOT gates. R_318 cuts at last NOT and needs lower bound on prefix plus monotone suffix. R_408 normalizes legal reads/output, then finite bound.
- Checked L_meta_4725.lean proves exactly binaryFloor for Petersen-10; 3224 lines / 146284 bytes, can copy and rename helpers into allowed single file. This reduces candidate circuits to 1–4 NOT.
- L_meta_8367.lean (524213 bytes) has stronger internal graphLower excluding all ≤15-gate FanInTwo circuits for Petersen-minus-vertex (9 vertices). Restricting a Petersen-10 input false yields this graph; deleting ≥4 gates would suffice.
- Source read 2026-11-25: https://pequalnp.com/papers/note-1 explains gate-elimination proofs for paths/forests/cycles; general triangle-/C4-free exact monotone lower bound is not established there. Avoid assuming it.

### BinaryFloor extraction 2026-11-25T14:05:32.543695+00:00
Created results/orch/lemmas/BinaryFloor.lean, copied from checked L_meta_4725 with namespace changed to PEqualNP.Outside.L_meta_2592_Binary and all helper theorem declarations changed to lemma. Imports narrowed from Mathlib.Tactic to Mathlib.Tactic.ByContra and Mathlib.Tactic.SimpRw, retaining SimpleGraph.Basic and Defs. Added atMostFourNot and notComputes_of_fiveNot. 3249 lines, 146939 bytes. Waiting for cache/Defs preparation before compilation; no completed build claimed.

## Counterexample search 2026-11-25T14:06:36.648116+00:00
System libz3.so.4 accessed through ctypes, no installation. Exact bitvector SMT circuit synthesis with CEGIS plus CGP stochastic search. Scripts saved results/orch/search/. Initial51-sample one-NOT19gate model had42 truth-table mismatches; refinement67samples timed out120s (UNKNOWN, not a lower bound). Stronger all76independent-set samples running. Separate exactly-one-input-NOT case fixes first gate NOT(input0) by vertex transitivity, with maximum-parent gate ordering. CGP starts from minimum-vertex-cover20gate circuits reduced to19slots; best so far9 mismatches, no exact circuit. Every purported witness is checked across all1024 assignments.

BinaryFloor helper namespace corrected to PEqualNP.Outside.L_meta_2592.Binary for the final checker naming rule.
