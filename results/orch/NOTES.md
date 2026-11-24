# L-meta-2870 orchestration notes

Lease acquired 2026-11-24T17:09:44Z. Only root controls the lease.

Statement: projective-plane monotone fan-in-two circuit lower bound, conditioned on a positive small number of mixed AND gates. Reductions open.

Read exact statement at /tmp/oec/pequalnp-pilot-34/statement.txt and desk metadata at /tmp/oec/pequalnp-pilot-34/desk-response.json. Agents: append findings under a unique heading; do not overwrite other notes. Own scratch files under results/orch/lemmas or /tmp/oec/pequalnp-pilot-34.

## Direct proof analysis (17:14 UTC)

- `L_meta_2868.lean` proves the zero-marked sibling with the stronger incidence bound `N*(q+1) ≤ C.size+1`. Its core is that every AND input is pure in one side and linear (has a singleton witness), yielding a star-cover count on a C4-free graph.
- For L-meta-2870, a positive set of mixed ANDs destroys that linear-input property. Padding an otherwise correct circuit with one unused mixed gate can satisfy positivity, so positivity cannot yield a useful output structural fact by itself.
- Existing checked cut `R_meta_2870_713.lean` already has four pieces: (1) classification of sparse covers of projective plane, (2) CNF compilation of AO2 circuits, (3) quadratic floor for small q, (4) large-q CNF circuit extremal lower bound. Avoid reproducing this reduction unchanged.
- Parent cuts `R_meta_2008_1` and `R_meta_2475_271` already split semantic compilation into Boolean-grid unions/rectangular intersections and lower bound for those semantic circuits. Merely replacing syntax by semantic sets would duplicate these.
- Candidate substantive new route: under sparse-line soundness, identify output minterms with ≤q line variables as containing an incident pair; use a truncated antichain/set-union program and prove a cost lower bound there. This retains the hard combinatorics but removes evaluations and nonminimal supports. No completed lower-bound proof yet.

## Library search (17:16 UTC)

- `PEqualNP.Defs` imports only definitions modules, no Outside or Helper theorems. Existing proofs must be transplanted, not imported.
- `R_meta_2870_713` is an existing checked reduction of our exact step: four hypotheses cover classification; monotone-circuit CNF compilation; quadratic floor `4*q^2+2+n ≤ 2*C.size`; and a q≥250 combinatorial CNF lower bound. Do not duplicate it.
- `L_meta_2862` (556 lines, Mathlib + Defs only) proves the target bound for `100 < q < 200`, with weaker circuit assumptions (no sorted wiring/output bound, no marked-gate premises). Its `lb` proves a lower bound on OR-gate count, and `has_and` makes it strict. This is a candidate substantive partial component.
- `L_meta_2672` (982 lines) gives `N*q ≤ 32*C.size + 3*N + doubleReread.length` for exact incidence circuits. `L_meta_1942` (2620 lines) proves `N*q ≤ 100*C.size` assuming exact incidence and read multiplicity at most 2.
- `L_meta_2868` (sibling) proves zero mixed gates via pure-side linear functions, C4-free edge count, and incidence counting. Its proofs are sizeable but self-contained.

## Counterexample audit (2026-11-24T17:11:51.610359+00:00)

- No defect found in the stated incidence axioms or wire semantics. Pair uniqueness plus uniform line size and N=q²+q+1 forces the usual regular projective-plane incidence; sorted strict backreferences eliminate default-wire tricks.
- Positive mixed-AND count is not a substantive standalone restriction: an unused AND of two point inputs can be appended without changing the output, so do not base a proof solely on positivity.
- The relaxed function may accept all assignments with more than q selected lines. Candidate exact extension is incidence OR threshold(q+1 lines), but no efficient monotone circuit or counterexample was found. It is not enough to check only singleton-line inputs in a new combinatorial bound: the original soundness controls every selected line set of size at most q.
- Finite geometry checks completed in results/orch/lemmas/counterexample_small_cases.py for prime orders 2,3,5,7: incidence degrees, unique line through pairs, dual pair intersections, and each unselected line having a point outside any selected <=q lines. Exhaustive selected subsets for q=2,3 (29 and 378 tests), subsets of size <=2 for q=5,7 (497 and 1654 tests). These test supporting geometry only, not the full q>100 circuit statement. Output saved to /tmp/oec/pequalnp-pilot-34/counterexample-small-cases.stdout.

## Reduction design: DNF supports

Proposed two-hypothesis cut at `results/orch/lemmas/reduction_dnf.lean`: generic circuit-to-support-family compiler, then a purely finite-family lower bound. Raw supports (not minimalized) use union at OR and pairwise union at AND. Output has a support contained in every accepted incidence pair; every output support using at most q line variables contains an incidence pair. This removes circuit semantics and mixed-gate definitions from the hard combinatorial step. Compiler independently assigned to direct_proof; counterexample agent tests small instances. The prototype reduction proof uses the exact original conclusion. Not yet compiled.

### Independent raw-DNF validation (2026-11-24T17:13:28.269887+00:00)

For reduction_design, independently tested raw supports F(input)={{i}}, OR=family union, AND=pairwise union of supports. Truth tables were propagated independently with bitwise AND/OR and compared to evaluation of the resulting support family. Pair acceptance and sparse-line rejection were compared against the proposed output-family conditions. All passed.

- Exhaustive strictly sorted, backward-read 4-input circuits through 3 gates: 7,452 gate prefixes and 7,452 truth-table comparisons. All 16 binary 2x2 incidence relations and q=0,1,2: 357,696 condition-equivalence checks, including 18,048 successful promise instances.
- Random 6-input circuits: seed 2870, 2,000 circuits of 12 gates; 24,000 truth-table comparisons and 96,000 condition-equivalence checks using random 3x3 relations and q=0,1,2,3.
- Script: results/orch/lemmas/counterexample_dnf_check.py; complete stdout/stderr: /tmp/oec/pequalnp-pilot-34/counterexample-dnf-check.stdout and .stderr. These checks validate the compilation and output characterization, not the large-order lower-bound hypothesis.
- Mathematical caution: a raw-family lower bound without the mixed-AND assumptions is stronger than this conditioned step and retains the substantive lower-bound difficulty. Describe it as a semantic-to-combinatorial reduction, with generic compilation as the separately tractable part.

## DNF and charging audit (library search)

- Truncate support families to sets containing at most q line variables, then discard nonminimal supports. Both operations preserve all sparse-line evaluations under union/product. Output antichain is exactly the family of incident pairs: soundness forces every survivor to contain an edge, completeness ensures that edge itself survives. This is a cleaner finite-family normal form than raw DNF.
- Naive first-AND charging cannot assume an internal generated rectangle is sound. Explicit exact C4-free matching circuit: `((p1∨p2)∧(l1∨l2)) ∧ (p1∨l2) ∧ (p2∨l1)` computes `(p1∧l1)∨(p2∧l2)`, but the first AND produces all four pairs, including both nonedges. Exhaustive 16-assignment check saved under /tmp/oec/pequalnp-pilot-34/library-masked-rectangle.stdout. Later AND masks remove unwanted pairs.
- A Schnorr-style separated edge subfamily avoiding a third edge inside the union of any two edges is a star forest (in bipartite graphs it excludes a 3-edge path). It has O(N) rather than Nq edges, so direct separated-family counting loses a factor q. A stronger potential must pay for shared OR construction and later masking, not merely count newly born edges.

## Direct DNF compiler draft (17:14:45 UTC)

Draft `results/orch/lemmas/direct_compiler.lean` constructs a list of support families in parallel with circuit wires. The proof separates: union/product truth semantics; prefix preservation; a per-gate recurrence; initial input semantics. The exported `dnf_compiler` lemma has exactly the signature requested by reduction_design. It awaits Lean checking after cache setup.

The DNF representation is raw (not minimal): inputs are singleton singleton families, OR forms family union, AND forms pairwise support union. Nonminimal supports are retained, so no minimization theorem is assumed. This removes a possible validity hazard in abstract support bounds.

## DNF compiler checked

2026-11-24T17:18:04.867515+00:00: `results/orch/lemmas/direct_compiler.lean` passes `lake env lean` with exit 0, empty stdout/stderr, no warnings. The 170-line file proves the exact first hypothesis of the proposed DNF reduction; no missing facts remain in compilation. Earlier finite checks covered 9,132 circuits and 905,786 wire/assignment instances. Final logs are `/tmp/oec/pequalnp-pilot-34/direct-compiler.stdout` and `.stderr`. Root notified to archive/push immediately after independent review.
