# L-meta-1031 orchestrator notes

Own lease acquired 2026-11-25T01:04:49Z; initial expiry was 01:24:49Z. Root renews every ten minutes and before long runs; current expiries are in the scratch desk log.

Statement: triangle-free and square-free graphs admit a minimum binary monotone circuit in which every AND gate owns a nonempty star of edges. Exact statement lives in /tmp/oec/pequalnp-pilot-55/statement.txt.

Desk permits reductions but reports reductions_live=3. Do not assume another reduction can be submitted.

Strategies and findings will be appended by agents in distinct sections. Root alone holds lease, commits and pushes.

## Counterexample strategy: initial finite checks

Enumerated semantic AND/OR circuits with 1–4 inputs in increasing gate count, deduplicating available-wire truth-table sets. All 1, 2, 7, and 38 labelled triangle/C4-free graph functions, respectively, have minimum witnesses satisfying the exact nonempty-star ownership test. Max size at n=4 is 4 (the 12 labelled P4 graphs). Constants/unary/copy gates can be normalized away for nonconstant graph functions; empty graph uses size zero. These are computational checks, not Lean proofs. Script and full output: /tmp/oec/pequalnp-pilot-55/counterexample_search.py and counterexample-small-results.json.

One P4 optimum uses nested ANDs: g0=x0∧x1; g1=x0∨x2; g2=x3∨g0; g3=g1∧g2. The later gate owns only the star {03,23}, because the earlier active AND excludes edge 01. Thus ownership condition intentionally allows nested ANDs, and does not imply a flat DNF structure.

## checker_review: reduction and lemma integration

- R_meta_1031_1: useful minimum (all AND gates own edges) plus an exchange lowering the number of AND gates owning disjoint edges.
- R_meta_1031_2: semantically sound minimum (each AND implies the graph function), plus ownership cleanup. Its second child is already proved by L_meta_1906. L_meta_1600 proves sound AND implies star profile; L_meta_4846 proves disjoint owned edges imply a nonedge pair where the gate is true.
- R_meta_1031_3: minimum with weak/vacuous star profile, plus removing empty owners.
- L_meta_2666 proves minimum existence. L_meta_2668 proves each gate is pivotal on an edge under replacement by false, but not ownership. L_meta_5355 gives useful circuits of size at most edge count plus vertex-cover size minus one.
- Desk imports permit only Defs (+ Mathlib), so outside source proofs must be adapted into the target file, not imported.
- The real gap on route 2 is existence of a semantically sound size-minimal circuit.
- Compact obstruction to pivot alone: chain AND[0,1], AND[2], output 3 on two inputs. Both gates are pivotal under false replacement; the last owns no pair, because its earlier AND is true on every pair where it is true. This circuit is nonminimal, so not a counterexample to the posted statement. Draft formal file results/orch/lemmas/checker_review.lean awaits cache/bootstrap completion.

## normal_form strategy (2026-11-25T01:09:03.229945+00:00)

- Direct structural obstacle: the proof must allow the possibility of dirty AND gates, true on nonedges and later filtered. No such minimum-circuit counterexample for the posted graph class has been established here. Edge-pivotality alone does not imply semantic soundness. Existing top-form helpers isolate this obstacle but do not remove it.
- Prepared `results/orch/lemmas/normal_form.lean`, self-contained using Mathlib and Defs only. It adapts checked L_meta_1906 cleanup and R_meta_1031_2 to prove: existence of a semantically sound minimum for every graph in the class implies the exact posted statement. This is a CONDITIONAL PARTIAL, not a proof of L-meta-1031 and not an admissible one-hypothesis reduction. Awaiting compilation after toolchain/cache setup.
- Literature caution: repo note mentions the disproved single-level conjecture. No source read establishes a counterexample under no-C4. Existing selector-family definition visibly has C4s when underlying edges meet. No falsehood conclusion is justified.

## graph_ownership strategy

- Exact graph-combinatorial step is already solved: R_meta_1031_2 reduces to a minimum with sound AND gates plus useful-owner cleanup; L_meta_1600 is the standalone sound-AND-to-star result; L_meta_4846 proves two disjoint owned edges force some nonedge pair to make the gate true.
- L_meta_1906 supplies nonempty ownership for every AND in a sound minimum. L_meta_2668 only supplies a pivotal graph edge, not an owned one.
- Existing normalization: L_meta_4181 converts any Monotone2 circuit of a nonempty graph to <=size IsLeastAO + TopForm. TopForm forbids a sound AND inside another AND cone but permits dirty AND gates. L_meta_1501 preserves the dirty count while arranging TopForm.
- Existing counting: L_meta_1491 gives |E|+|tops\centreless|+2|centreless|+|junk|+|orN\lam| <= size+|Ustar|+1, plus a cover of the star edges by <=|tops\centreless| centers. Closing the residual Ustar cost is still substantial.
- A direct quadratic truncation proof is not established: AND of signals with both singleton and pair minterms must selectively filter inherited pair minterms, so cost-preserving truncation cannot simply replace the same gate. Sound-minimum normalization is stronger than the posted ownership-star theorem.
- notes/note-1-edge-function-exact-size.md documents checked m+tau-1 lower bounds only for forests, cycles, and long-thread graphs, and distinguishes the known single-level bound on C4-free graphs from the unrestricted circuit problem.
- Special-task lead: L_meta_1036.lean is an existing negated-twin-style result with n<=7 and one NOT beating every monotone multioutput circuit, apparently the requested L-meta-1035 counterexample. Root informed.

No new Lean lemma claimed. Unrestricted web search returned Jukna single-level-conjecture references, but no theorem usable for this target was verified on an allowed page; no numerical external claim used.

## Root: boundary certificate lemma

Drafted generic monotone-function certificate: checking true on every edge input and false on every maximal independent-set input implies exact graph function on every assignment. This formalizes the compressed SAT certificate route for Petersen/Fano searches; compilation pending targeted cache. File results/orch/lemmas/boundary_certificate.lean.

### normal_form: structural bottleneck (2026-11-25T01:10:58.772815+00:00)

For a first active AND that owns disjoint edges uv and st, its two inputs have OR witnesses u,s and v,t. It therefore accepts the cross pairs ut and sv. At least one cross pair is a nonedge (otherwise C4), and a downstream AND must filter it. A prospective exchange is to bypass the first AND at downstream gates whose other operand implies one of its inputs, using `(A AND B) AND H = B AND H` when `H <= A`. The unresolved global step is handling shared OR paths and different downstream filters without increasing gate count. Semantic soundness of every AND is stronger than the requested star ownership, so failure to normalize soundness would not by itself refute L1031.

### Counterexample strategy: stronger soundness checks

All first minimum witnesses on n≤4 also satisfy that every AND wire implies the graph edge predicate. Official Z3 5.3.3 was obtained from GitHub into task scratch (no tracked dependency changes). Full truth-table synthesis confirms P5 minimum 5, C5 minimum 7, fork5 minimum 5, P6 minimum 7, C6 minimum 8. A second lower-bound pass checked every possible size n−1 through optimum−1 without gate-order symmetry; smaller sizes cannot depend on all n inputs. SAT witnesses were evaluated by Python on all assignments. Queries requiring at least one unsound AND at the optimum returned UNSAT on these five examples, with canonical independent-gate ordering (C6 took45s). This is computational evidence, not Lean verification or a general theorem. Files: /tmp/oec/pequalnp-pilot-55/counterexample_sat.py, counterexample-sat-results.jsonl, counterexample-sat-validation.stdout.

Petersen/Fano search uses edge pairs and maximal independent sets, enough to determine a monotone output. Petersen has15 edge tests and15 maximal independent sets (30 tests). A 19-gate query began, capped120s and768MB. One must not infer lower bounds from timeouts.

## exchange strategy (2026-11-25T01:12:12.744889+00:00)

- Direct target is weaker than sound-minimum normalization. A bad owner (AND owning disjoint edges) forces some cross nonedge to be true there, hence downstream filtering.
- Local size-preserving rotations: `(A AND B) AND H = (A AND H) AND B`; through OR, `(A AND B) OR D = A AND (B OR D)` needs global implication `D -> A`. Fanout and OR joins prevent naive repeated rotation.
- When the downstream residual filters are linear, a rectangle `(OR A) AND (OR B)` can retain only a double-star under the no-C4 condition. The P4 factorization `(a OR c) AND (b OR d) AND (a OR d)` costs five gates, versus `a AND (b OR d) OR (c AND d)` at four. Thus nonlinear/shared residual contexts are the real unresolved exchange case.
- No full invariant or refutation yet. Do not infer the statement false from these obstacles.

### checker_review: expanded theorem census

Scanned 279 Outside proof files selected by ownership, minimum-circuit, vertex-cover/cardinality, TopForm, and read-once vocabulary. Parsed 247 relevant final statements; the one alternative namespace style missed by the standard parser is L615, a specialized theta-graph theorem. Complete scratch census: /tmp/oec/pequalnp-pilot-55/checker-review-statement-census.json.

No unrestricted girth-at-least-five circuit lower bound of edge count plus minimum cover minus one was found. Existing exact bounds need forests (L3525, L1737, L243), formulas (L531, L252), semantically sound ANDs (L1407), read-once circuits (L2237), or each AND sound or true on at most one graph edge (L4767).

Other normal forms: L4181 constructs a least TopForm; L4543 also minimizes Ustar among such minima. L1491 counts top gates, junk gates, and uncovered edges but retains a Ustar error term. L3760 excludes exactly one junk gate for bipartite square-free graphs; L3653 normalizes a single junk gate true on a singleton under bipartite/fixed-point assumptions. None removes arbitrarily many junk gates for the full triangle/square-free class.

Independent exchange review: original five helper statements and subsequent guarded double-star identity are valid by finite Boolean cases / direct application of no-four-cycle premises. Guarded identity file hash c6d1cb1f58122a69b35de11ae1d947f71ba14eb36f87b73703a1d3dab61045b7 passed static forbidden/credential-shaped scans; these remain partial helper results only.

- Exchange partial compiled: `results/orch/lemmas/exchange.lean` (Lean core only) has guarded `(A AND B) AND (a OR d) = (a AND B) OR (d AND A)` when a implies A and d implies B. `results/orch/lemmas/exchange_circuit.lean` now compiles against actual root `Circuit`: two explicit binary monotone three-gate fragments have size 3 and equal evaluation on guarded four-bit inputs. This is a conditional local rewrite, not unrestricted circuit equivalence or the posted theorem.

### graph_ownership stochastic Petersen search

Ran a 300-second independent stochastic search for a 19-gate AND/OR circuit, seeded by 190 deletions of canonical 20-gate minimum-vertex-cover constructions. Evaluated on all 15 edge inputs plus all 15 maximal independent-set inputs, which determine monotone correctness. NO_WITNESS score=1 iterations=1656000000. No exact circuit found. This is heuristic failure only, not a lower-bound certificate. Full stdout/stderr and source remain under /tmp/oec/pequalnp-pilot-55/stochastic-petersen.*; the best 1-error candidate is stochastic-petersen-best.json and was sent to counterexample agent for SAT repair.

### Counterexample strategy: kernel-checked C5 component

`results/orch/lemmas/counterexample.lean` now compiles successfully with the pinned Lean, using only CircuitLowerBounds. It proves an explicit seven-gate AND/OR circuit computes the 5-cycle edge function and every AND is semantically sound, using ordinary kernel `decide` over32 assignments. It does NOT establish minimum size or the general gap. Build invocation from lean/: `lake env lean ../results/orch/lemmas/counterexample.lean`; exit0, stdout/stderr empty, stored as /tmp/oec/pequalnp-pilot-55/counterexample-lean.stdout and .stderr. Root notified immediately for push-early, independent reviewer requested.

### normal_form compile (2026-11-25T01:17:16.088914+00:00)

`lake env lean ../results/orch/lemmas/normal_form.lean` passed with exit 0 using the pinned toolchain and Defs only. This is the conditional theorem; the sound-minimum existence hypothesis remains unproved.

### checker_review: compilation and independent checks

The finite pivotal obstruction compiled with exit 0 and empty output after spelling the binary monotone model predicate explicitly (the narrow imports do not export Monotone2). Final SHA256 a35d17f8743b866e7efd9645646ba25ae906f94a4a34df24d745a9a575ec2b7f, 33 lines. Root independently reviewed it.

Independent final review passed conditional normal_form (SHA256 2b53479031c968b45e1d0e0c48fd2ff1525641757538e6e8da994ef654bb6bbe); it compiled with only an unused implicit-variable warning. Exact conclusion remains the posted statement, but the extra sound-minimum premise remains unproved.

Independent review also passed the C5 seven-gate sound witness, the concrete guarded exchange circuits, and the circuit monotonicity proof. All are partial results with their actual premises; none is a proof of the full posted statement.

### normal_form owner-input constraint (2026-11-25T01:18:14.495562+00:00)

New self-contained partial `results/orch/lemmas/owner_inputs.lean` compiled with exit 0, no warnings. If AND gate j owns any pair u,v, it cannot read an earlier AND output directly. A true AND forces every operand true, whereas ownership requires every earlier AND in its cone false. No graph or monotonicity assumption is needed. This is a necessary syntactic restriction for the posted target.

- New compiled structural partial `exchange_residue.lean`: if a–d is an edge in a triangle-free graph, a monotone signal P has both `P AND x_a` and `P AND x_d` below the graph function, and P is true on a nonedge pair {u,v}, then `(a~u and d~v) or (a~v and d~u)`. Proof enlarges the nonedge pair by a and d and excludes a common chosen neighbor using the triangle. Thus nonlinear shared residue necessarily traces a P4 across the adjacent filter centers. This does not yet remove the residue or bound gate cost.

### Independent review by normal_form (2026-11-25T01:19:23.791545+00:00)

Reviewed exchange_residue.lean (267f2580), one_dirty_graph.lean (c6ed97f7), finite_certificate.lean (3c353cb0): PASS mathematical and static red-team review as partial research artifacts. No forbidden constructs found. Claims and hypotheses are explicit; finite certificate correctly handles arbitrary monotone fan-in and forward references. These helpers do not establish L1031.

### One-dirty graph bridge, Lean checked

`one_dirty_graph.lean` now compiles with only SimpleGraph.Basic. For adjacent filter centers a,d in a triangle-free graph, if H∧a and H∧d are sound then H has no literal forcing support; monotone H is false on every singleton; hence a shared OR branch g∨OR(P) must have P empty. Added a C4-free product consequence: if a∈A,d∈B and both filters on g=OR(A)∧OR(B) are sound, all graph edges firing g touch a or d. Proof uses pair tests {p,d},{a,q} to establish crossed adjacency, then no4; it does not incorrectly infer adjacency from triples that already contain an edge. Consequently replacing g by (a∧OR(B))∨(d∧OR(A)) shrinks pointwise and preserves all graph-edge values, but local cost grows by two unless downstream filters contract.

### checker_review: signed domination theorem (compiled)

New theorem PEqualNP.Outside.L_meta_1031.signed_domination_impossible proves the counterexample-search pruning rule for every graph, without girth assumptions. In a size-minimal binary monotone circuit computing the edge function, no gate can be replaced by an earlier wire that is at least its value on every positive edge-pair test and at most its value on every maximal-independent negative test.

Proof: bypass/delete the gate using L2668's relational simulation, forward on positive tests and backward on negative tests. The bypass circuit remains binary monotone. The boundary-certificate lemma upgrades test agreement to full functional agreement, contradicting minimum size because one gate was removed.

File results/orch/lemmas/signed_domination.lean, 499 lines, SHA256 df673d1e0762c47724fc4250fb905eb8c86ecbe95629f1b4accbcebd148d92b1. Compiled exit 0. Only inherited deprecated-name and unused-simp warnings. This is a new structural partial, not the complete L1031 statement.

### normal_form star-cover dichotomy (2026-11-25T01:22:22.363629+00:00)

New `star_cover_dichotomy.lean` compiled exit0. A star-shaped edge family covered by adjacent centers a,d in a triangle-free graph is wholly incident to a or wholly incident to d. Combined with the product-two-centers lemma, a pure OR-product with prior star ownership and adjacent sound-filter contexts can be replaced by one sound AND branch, with no new gate. This is conditional local soundification, not yet a global normal-form proof.

Signed-domination follow-up: added AND-operand negative witnesses and OR-operand positive witnesses. Every earlier input of an AND gate has a maximal independent input on which that operand is true but the gate is false; every earlier input of an OR gate has an edge-pair input on which the gate is true but the operand is false. Both follow from domination impossibility and local gate semantics. Final signed_domination file 537 lines, SHA256 8bf1a3b15910686f6a7717fcb0da0524e067fbfb95a8146141a0c8d577932c3f, compiled exit0 with empty stdout/stderr after removing inherited deprecated-name and unused-simp warnings.

### Counterexample strategy: larger search and pruning

Baseline Z3 queries Petersen19 general/Petersen20 sound/Petersen20 unsound and Fano26 general/Fano27 sound/Fano27 unsound each timed out after120s. No lower bound or counterexample follows. Explicit star constructions independently pass all1024/16384 assignments, at20/27 gates; they have sound ANDs and nonempty-star ownership. Canonicalized witnesses (120 Petersen automorphisms,336 Fano automorphisms) satisfy the strengthened encoding; fixed-witness SAT runs complete in0.64s/0.60s. Witnesses: counterexample-star-witnesses.json.

Theta(2,3,3) has7 vertices,8edges,τ=4, candidate11gates. Theta(2,3,4)/(3,3,3) candidates12gates. Baseline and onehot queries below these candidates and for unsound candidate circuits timed out at120s. A graph-ownership agent19-gate Petersen seed misses exactly edge{6,9}; directed SAT proves no single gate edit repairs it, but2–5 edits time out30s. These are finite computational investigations, not Lean lower bounds.

Added signed-domination pruning: every earlier wire fails to dominate a new gate on edge-positive/maximal-independent-negative tests. Reviewer formalized this separately in signed_domination.lean. Also testing cheaper local AND-negative and OR-positive incomparability, nonempty edge-positive support, canonical gate ordering by(maxinput,mininput,operation), and first-input-pair orbit representatives. First-pair representatives must use the SAME max/min order; one provisional mismatched-order run was interrupted before any verdict. Corrected run uses theta4automorphisms and Petersen120automorphisms. Stronger queries capped300s and256MB each.

C5 component axiom audit also passed: only propext/Classical.choice/Quot.sound, with raw output in counterexample-axioms.stdout. No claim of full L1031 proof.

### Explicit one-sided replacement

`one_dirty_graph.lean` additionally proves `starProjection_below_product`, `starProjection_sound`, and `starProjection_preserves_graph_pairs`. The generic `single_star_replacement` lemma gives a same-one-AND substitution: if literal a forces operand A, all graph-edge pairs accepted by A AND B touch a, and (A AND B) AND a is sound, then a AND B is below the old signal, agrees on every graph edge pair, and is sound. No extra graph hypotheses are needed once the accepted-edge star is established. This is ready to compose with the independently checked star/double-cover dichotomy and the circuit semantic shrink bridge.

### checker_review — sound-wire exclusion 2026-11-25T01:26:14+00:00

The 552-line signed_domination.lean compiles with empty diagnostics. Added sound_wire_not_and_input: no earlier semantically sound wire directly feeds an AND gate in any minimum graph circuit, because the operand-negative witness is an independent input on which that wire is true. This is independent of girth. Existing L4181 A1527.main_aux, lines267–318, already gives exact-binary ReadsBack normalization of any Monotone2 graph circuit at no size increase; hence normalized-minimum existence follows from existing code adaptation, while every-minimum normalization is stronger.

- `exchange_context.lean` compiled: actual arbitrary prefix/suffix Circuit rewrite `(A AND B) AND (a OR d)` to `(a AND B) OR (d AND A)`, with three gates before and after. Hypotheses: operand wires come from prefix, a implies A and d implies B at its wire state; suffix never reads the first two fragment output wires; final circuit output also avoids those private wires. Suffix may read the unchanged final fragment output. Generic `run_agree` handles any gate operations and out-of-range reads. `exchange_size` proves equal total gate counts. This makes the local rewrite valid inside a private circuit fragment; global normalization still must establish that fragmentation/fanout condition.

- Exchange strategy status: local and private-context transformations are now checked. The unresolved global step is extracting or contracting such fragments when dirty AND outputs and their OR descendants have shared nonlinear consumers. No argument currently justifies that a minimum circuit satisfies the private-wire side condition, and no counterexample to L-meta-1031 has been found by this strategy.

### checker_review — every minimum is normalized 2026-11-25T01:30:26+00:00

The signed-domination extension now proves, for every graph G (no girth assumptions), every gate of every IsMinimalMonoCircuit computing graphFun G empty has exactly TWO DISTINCT EARLIER inputs. Derivation: false-wire bypass makes every gate true on some positive edge; AND operands therefore earlier; separation witnesses force distinct companion operands; OR gates consequently are binary and backward-reading, while AND gates are initially nullary or binary. A constant-true wire cannot be an OR operand (positive separation witness), nor an AND operand (the other operand negative separation witness); it cannot be the output since graphFun at zero is false. Thus any constant-true gate is unread and can be deleted, contradicting minimum. Nullary AND gates are eliminated. Added minimum_isAO2, minimum_isLeastAO and gate_false_on_zero as direct adapters. Scratch signed-normalization.lean compiles with empty diagnostics, and parent has been notified to preserve the snapshot. This is a structural partial, not a proof of soundness or the posted star-normal-form theorem.

### Independent axiom audit

All 15 current helper sources (188 lemma/theorem declarations) and the pending stronger signed-normalization source (58 declarations, including 6 new names) compiled in isolated scratch copies with per-declaration axiom reports. All reported axioms are in {propext, Classical.choice, Quot.sound}; no others. Complete stdout/stderr, exact SHA256 hashes, commands and scope are in `results/orch/axiom-validation.txt`. This is a helper audit, not a verdict on the full posted theorem.

### normal_form OR-count route (2026-11-25T01:33:47.866541+00:00)

Investigated the possible unrestricted bound OR-count >= |E|-1 for triangle-free, C4-free graph functions. No proof was obtained. Pair-input/singleton-support invariants alone lose the negative independent-set constraints: a dirty AND may create a large cross-product of pairs which later ANDs filter. The checked L4767 argument instead assumes each AND is semantically sound or accepts at most one graph edge; it charges edges to ANDs and large-support ORs, and cover vertices to small-support ORs. That does not establish the unrestricted OR bound.

A census also found L950: compressed AND-count circuits on exactly six variables admit biclique covers with at most the AND count. Its long finite case proof does not establish the general statement. A general version on C4-free graphs would imply AND-count >= vertex-cover number, since all bicliques are stars. No general theorem was found.

The counterexample agent now tests OR-count using an exact unlimited-AND encoding: every OR input/output can be a conjunction of original variables and previous OR outputs. This avoids total-gate cutoffs. Its C5 bound <=3 OR was externally UNSAT; this is finite SAT evidence, not a Lean proof.

Reverse-route observation (not yet formalized here): signed domination rules out a minimum gate whose accepted graph pairs all meet c and whose singleton-c value is true; replacing it by input c preserves positive edge pairs and can only decrease independent-set negatives. For a pure OR-product with disjoint singleton supports and all accepted graph pairs centered at c, replacing the operand containing c by c is pointwise decreasing and agrees on graph pairs. This leaves a shared-OR pruning problem before obtaining globally sound ANDs.

### checker_review — compact OR translation 2026-11-25T01:37:08+00:00

compact_or.lean proves a full generic representation theorem: every binary AND/OR circuit with backward references and valid output has an equivalent compact program in which every step ORs two conjunctions of earlier atoms, initial atoms are input variables, and final output is a conjunction. Program length equals the original number of OR gates exactly; all conjunction atom indices are bounded. Proof maintains an exact list equality representing every old wire, concatenates representations for AND, and appends one atom for OR. No Boolean solver or certificate assumptions. This matches counterexample agent's 5-input/3-OR finite mask model exactly; padding, list-to-mask encoding and an axiom-free finite obstruction remain needed for the C5 lower-bound bridge. Full source compiled with empty diagnostics; parent notified for independent review/push.
