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

### BinaryFloor compilation passed 2026-11-25T14:11:37.423735+00:00
Command: lake env lean ../results/orch/lemmas/BinaryFloor.lean (cwd lean/), Lean 4.36.0, exit 0. Complete output saved to results/orch/BinaryFloor.stdout (linter warnings only) and BinaryFloor.stderr (empty). Source SHA256 c148b85b798f8154c163c8ab566bca5f51e7760089a0604b52c846f42bcfe3df. The proved corollaries bound candidate NOT count by 4 and exclude circuits with at least 5 NOT gates. Full target remains unproved.

### Search update 2026-11-25T14:13:14.728782+00:00
Exactly-one-NOT all-independent/minimal-edge110sample synthesis timed out300s UNKNOWN. Unweighted CGP improved to6false-negative assignments with zeroNOT, missing minimaledge{5,7}. Exact two-gate rewrite search of this seed exhausted45097first-mutation/last-gate pairs; no one-NOT repair. Stronger weighted annealing emphasizes15edge minterms and76independent sets64times, otherpositive assignments once. Running: inputNOT0canonical SAT, free-NOT18binary SAT4normalizedops, and3-gate localrepair SAT near6-error seed. No UNSATglobal claim or exact witness.

### Search update 2026-11-25T14:20:02.822195+00:00
UnweightedCGP600s:889847808iterations/11028restarts,best6false-negativeerrors,zeroNOT. Annealing600s:605159424iterations,best9errors. Z3exactly1inputNOT0case115samples:UNKNOWNafter603s. Localrepair exactly1NOTand≤3changedgate-records from6-error seed:UNSAT118samples88s; onlya bounded-neighborhood exclusion. ActiveCaDiCaL2.1.2directCNF inputNOT0case114samples6877vars186466clauses20minute budget. ActiveZ3≤4-gatelocalrepair20minute budget. ActiveCGPforcingexactly1NOT20min,seed21false-negativeerrors; weightedboundaryannealingalsoactive. No exact witness or globalUNSAT.

## Root strategy checkpoint 2026-11-25T14:20:12.355219+00:00

Priority1: extract checked9-vertex signed lower bound and prove binary-cost restriction. Expected first improvement is16+notCount≤size; a two-reader argument using four distinct cofactors may raise16 to17. Do not claim either until checked.
Priority2: continue exact one-NOT synthesis and targeted local resynthesis; no exact witness exists so far. The6-error approximation is not a refutation.
Priority3: read-once counting is now checked under explicit normalized/liveness assumptions. A read-once-to-four-gate-removal theorem remains missing; naive shared-fanout charging fails for OR entrances without semantic absorption.
Naive full signed enumeration has not closed an orbit; prioritize extraction and structural lemmas over further unstructured enumeration.20-gate upper-bound kernel/simp trials are paused to protect lower-bound buildmemory; the source remains unchecked.

### Generic binary restriction bridge checked 2026-11-25T14:22:47.547559+00:00
BinaryRestriction.lean, 534 lines, SHA256 08339a0b0f21e26c7065f47303e3b00d6bd58d8e630ff9c563b68a441273883d, compiles with exit 0. The generic restrict_last_binary theorem gives a cofactor circuit with at least one fewer non-NOT gate whenever the last input is essential and its false cofactor is nonconstant. Proof uses constant propagation and a semantic invariant: if no binary gate disappears, each surviving wire is independent of the fixed input. Full compiler logs copied to results/orch/BinaryRestriction.stdout and .stderr. Petersen specialization pending.

### Counterexample search checkpoint 2026-11-25T14:24:40.630029+00:00
No counterexample. The signed 18-binary-gate Z3 instance timed out after 600 seconds (UNKNOWN). A search with exactly two NOT gates and 19 total gates is running for 20 minutes. The forced-one-NOT CGP best has 15 errors, but its NOT was unused; another run now requires the NOT to lie on the output dependency cone. A new CaDiCaL instance fixes NOT(AND(input0,input1)) as its prefix. The direct CNF encoding was validated on a known 23-gate one-NOT circuit: all 1,024 truth assignments match, and all 37,408 clauses for eight test rows hold. Active runs are expected to finish between 14:29 and 14:45 UTC.
Mathematical clarification: L_meta_8367 signedRoot excludes at most 14 binary gates, so the nine-vertex graph needs at least 15 binary gates. A one-gate restriction bridge yields a full Petersen binary lower bound of 16. A proposed two-gate bridge uses pairwise distinguishability of every input pair: fixing an exclusive neighbor realizes either variable as a cofactor, so both variables cannot occur only at their first common binary gate. This might yield a binary lower bound of 17; it is not proved here.

### Petersen binary restriction bridge checked 2026-11-25T14:25:48.754556+00:00
BinaryRestrictionPetersen.lean compiles exit 0. It contains the generic bridge plus petersen_restrict_binary, proving every full Petersen-10 circuit has a Petersen-minus-9 cofactor circuit with at least one fewer non-NOT gate. Size 25005 bytes; 576 lines; SHA256 2a42f098676b1fcc7fb992e2d68bd942d5f7f88aafb7fdac537413d5b39c5dc4. Output complete in results/orch/BinaryRestrictionPetersen.stdout/.stderr. Combine with signed Petersen-9 floor 15 to get 16 binary gates; full L-meta-2592 still open.
