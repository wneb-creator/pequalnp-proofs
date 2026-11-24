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

## Sparse minimal-support normal form checked

2026-11-24T17:21:04.987782+00:00: `direct_minimal.lean` (91 lines) passes Lean with exit 0 and no output/warnings. From the exact two output conditions in the reduction (subset witness for each incident pair; soundness of each output support with at most q line variables), it proves that inclusion-minimal surviving supports are exactly incident pairs, for every q≥1. No projective-plane geometry is needed. In particular, every incident pair itself belongs to the raw output family, strengthening subset completeness. Root and independent reviewer notified for immediate archive/push.

## Formal masking obstruction (2026-11-24T17:21:14.522290+00:00)

Lean checked results/orch/lemmas/masking_obstruction.lean with exit 0 and empty stdout/stderr. Explicit 4-input, 7-gate circuit computes (p1 AND l1) OR (p2 AND l2) on every assignment, proved by all 16 Boolean cases. Its first AND, wire 6, is true on the nonedge {p1,l2}; later AND gates reject that input. Concrete witness checked by kernel decide. This refutes only naive soundness/charging of internal first-AND rectangles, NOT L-meta-2870. Complete diagnostics: /tmp/oec/pequalnp-pilot-34/masking.stdout and masking.stderr. Root notified immediately on successful compilation.

## Root — point derivatives as a possible lower-bound route

Fixing one point input to true and all other point inputs false leaves a line function agreeing with that point's neighborhood OR on assignments of at most q lines. Each raw output support is therefore either a neighbor singleton or requires more than q lines. A possible route is a simultaneous derivative-to-OR-circuit conversion, charging shared AND masks. No such conversion or quantitative bound has been proved. The masking example explains why naive gate-by-gate linearization is insufficient.

## Checked mixed-singleton context lemma

`results/orch/lemmas/library_context.lean` compiles with Lean 4.36.0 (exit 0, empty output). If q≥2, output supports are sound whenever they contain at most q lines, a family A contains both a point singleton and a line singleton, and every union of an A-term with a B-term lies in the output family, then every B-term contained in a point-line pair equals that whole pair. The pair need not be incident. Proof: if the context omits the point, multiply by A's line singleton to get a line-only output with at most two lines; if it omits the line, multiply by A's point singleton to get a point-only output. Both contradict soundness.

This is a precise re-read obstruction: an internally mixed singleton gate cannot supply a genuinely new endpoint to an output pair through such a context. The missing global step is to bound how often edge-carrying contexts can be shared. The q≥2 assumption is necessary: q=1 permits a two-line-only term outside the soundness promise.

## Point-derivative route: concrete obstruction

For each gate and selected line set Y, collect points p for which the gate accepts singleton point input {p}. This gives a set-valued union/intersection circuit; at the output, for |Y|≤q, the derivative set equals the union of selected lines. However, this abstraction loses the original soundness for arbitrary point sets X. It cannot by itself sustain the desired lower bound.

Checked Fano witness (`results/orch/lemmas/reduction_derivative_obstruction.py`): encode points as nonzero 3-bit vectors. The parity-zero line is {011,101,110}. Precompute coordinate masks for selected point bits, then test whether the masks admit an incident bit pattern. All seven singleton point tests are exact. Yet X={001,010} activates the masks of 011, causing acceptance with this one selected line despite neither actual point lying on it. Thus even a one-line restriction must retain arbitrary point subsets.

Conceptual generalization: dual-rail coordinate masks plus fixed-line field-arithmetic tests produce compact circuits agreeing on every singleton-point input and arbitrary line sets, while allowing synthetic points assembled from several selected points. Any point-derivative proof must explicitly charge or forbid this coordinate mixing; mere additivity in Y is insufficient.

### A local pruning lemma and the unresolved charging step

For a monotone AND/OR circuit computing the disjunction of a variable set S, evaluate at the assignment which is zero on S and one outside S. The output is false. Retain both children at every false OR, and choose a false child at every false AND. The resulting OR-only cone has leaves only in S. Replacing AND by a child only increases the function, so the cone still accepts every singleton in S; hence it computes precisely OR(S), with no additional gates.

Applied after fixing a line set Y with |Y|≤q, this gives a pruned OR computation of the points on the selected lines. For Y={l}, at least q merges are required to join the q+1 incident point leaves. Summing across all lines suggests Nq merge charges, but the same original gate can receive charges under different line-dependent pruning choices. The missing substantive lemma must control this reuse using soundness on multiple points and up to q lines. Counting only singleton point derivatives or only distinct input leaves does not establish that control.

## Quantitative re-read audit (library search)

- Checked geometric consequence `library_sharing.lean`: if A contains two distinct point singletons, sparse soundness q≥1 and product inclusion A×B⊆F permit at most one line singleton in B. This is pair uniqueness applied after establishing soundness of each pair.
- `L_meta_2672.coreL` bounds line-single accepted edges by `6*C.size`. Its sole soundness use is helper `start`, at the assignment consisting of one line l plus all points not on l (source lines573–593). This assignment fits our sparse promise, so that one-sided counting proof should transfer after weakening its soundness interface.
- The dual `core2` applies soundness at one point plus all nonincident lines, typically q² lines, outside our promise. Therefore the existing full doubleReread inequality cannot be imported or transplanted unchanged.
- A precise missing quantitative statement is that incident edges requiring a line re-read number at most `94*C.size` (with the 6*size single-read count, this would prove the requested constant). Counting marked gates does not give it: appending a redundant AND with OR(all line inputs) can make every accepted edge reread its line. Some normalization or amortized charge to prior computation is essential.
- Raw support families forget multiplicity of variable occurrences. A provenance-based argument would need to track parse multisets (OR=min/union; AND=sum/product) or the `linearParts` recursion, rather than infer single-read behavior from support sets alone.

### Final frozen counting diagnosis

The one-sided transfer is specific: in `L_meta_2672.start`, the test input turns on the selected line l and every point not incident to l. It has exactly one line and no incidence, so the original sparse rejection hypothesis proves it false for q≥1. The only occurrences of the global `hsound` parameter in the underlying `gen`/`img2` counting arguments are calls to `start`. The dual orientation turns on one point and every nonincident line, so its test has q² lines and is unavailable here. No claim is made that the full existing theorem applies without modifying its helper interfaces.

Why raw re-read counts cannot be charged a constant per mixed gate: append a binary OR Q of all N line inputs (N−1 gates), then the gate `C.output AND Q` (one gate). Sparse rejection at zero selected lines already implies C is false whenever all lines are false, for every point assignment; thus C implies Q, and the appended AND preserves the entire Boolean function. On every incident-pair input, C's proof trees must use the selected line at least once (otherwise the point-only input would be accepted), and Q's tree uses it once more. Therefore every incidence is now line-reread. The single new final AND is semantically mixed on the line side and accounts for all N(q+1) such edges. Any constant-per-gate charge must first remove this redundancy or charge previously constructed information; raw marked-cardinality alone cannot do it.

Research files frozen after this note. The verified context and unique-line-context lemmas are local structural progress, not a proof of the remaining extremal lower bound.

## Root — random line restrictions

Restricting to q selected lines makes the promise exact on that restricted incidence graph, which has q(q+1) edges. A generic per-restriction counting argument therefore yields only the quadratic scale. Recovering the missing q factor would require an average pruned-size bound on the order of original size/q. Pure-point subcircuits survive setting line inputs to zero, so that bound needs a new sharing or amortization argument; it does not follow from restriction alone. No quantitative lemma on this route was proved.
