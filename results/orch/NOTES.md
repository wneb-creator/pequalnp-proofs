# L-meta-1770 orchestration notes

Only root holds the lease and submits. Append findings with strategy names and UTC timestamps. Scratch Lean attempts belong in results/orch/lemmas; root owns the final Outside file.

Lease acquired 2026-11-25T02:59:42.485Z; original expiry 03:19:42.485Z.

## Structural strategy 2026-11-25T03:02:53.695440+00:00

- Existing R_meta_1770_401 proves bottom-bottom double-junk case with constant 204; leaves bottom-deep/deep-deep. R_meta_1770_1 splits singleton/quadratic behavior. L_meta_3807 solves non-nested junk globally.
- Existing leastness infrastructure (1495 no duplicate gates; 1498 tree of below-F gates; 1499/1501 normalize below-F AND nesting) does not remove dirty AND nesting.
- New scratch Structural.lean proves semantic separation: junk gates OR-reaching opposite sides of a top have incomparable truth functions, witnessed on graph-negative assignments. It uses only IsAO2 and top/junk definitions. Initial Lean attempt awaits PEqualNP.Defs oleans.
- Remaining possible route: every nested opposite-junk pair must have mixed AND/OR paths, since pure OR reach would force comparable truth functions and violate semantic separation. Need an amortized charge to such mixed paths; no linear bound established yet.

## Reduction design 2026-11-25T03:04:00.195995+00:00

Existing cuts partition singleton-vs-quadratic witnesses, and bottom-vs-deep junk. New candidate reduces exact residual edge graph to its minimum-degree-three core. Premise 1 is already checked support bound (L_meta_2074). Premise 2 bounds arbitrary core subgraphs of the exact full target predicate, with original graph and circuit fixed. Degree-one/two peeling costs at most twice the original support, giving coefficient k+2. Full target restrictions retained; core source currently 1370 characters, under the 2000 printed-character screen pending checker. Candidate: results/orch/lemmas/Reduction.lean.

## lemma_search 2026-11-25T03:04:24.867905+00:00

- Repository search found no checked general bottom-deep or deep-deep bound. Existing `R_meta_1770_401` proves bottom-bottom with constant 204; `L_meta_3807` covers junk antichains. `L_meta_5242` covers only two nested junk plus a non-concentration assumption.
- `L_meta_2074` (222 lines) proves the useful support bound `IsLeastAO G C → G.support.ncard ≤ C.size+1`.
- Compiled `results/orch/lemmas/LemmaSearch.lean` with Mathlib only: general 3-core peeling plus `bound_of_core` for arbitrary edge subset T. Low-degree peeling removes at most 2*support(G) edges. Both compile with exit 0; complete build output is `/tmp/oec/pequalnp-pilot-63/lemma-search-build.log` (empty on success).
- `reduction_design` is integrating this into exact L-meta-1770 reduction. Its two independent children are the known support bound and the target restricted to subgraphs whose nonisolated vertices all have degree at least three.

- 2026-11-25T03:05:08.489399+00:00: Structural.lean compiled with exit 0 (271 lines). New opposite_junk_separated lemma gives two graph-negative separating witnesses and excludes OR-reach in either direction between opposite junk gates. Eval infrastructure is adapted from R_meta_1770_1. Log: /tmp/oec/pequalnp-pilot-63/structural-build-5.log.

Reduction candidate compiled 2026-11-25T03:05:18.976400+00:00: `results/orch/lemmas/Reduction.lean`, theorem `PEqualNP.Outside.R_meta_1770_63`, 112 lines / 8535 bytes. Two hypotheses: already-known support bound; exact residual minimum-degree-three core bound. Proof peels vertices of degree1/2, loses ≤2 per support vertex, then combines coefficient k+2. Full target predicate is preserved in core; no stronger conjecture because core bound follows from original target by subset cardinality. All Lean proof terms standard; exit0, only unused x4 warning inherited from exact statement. Root notified immediately for early push.

## Counterexample strategy 2026-11-25T03:05:27.873441+00:00

All nonempty girth-at-least-five graphs on 4 vertices are 37 forests. Exhaustive synthesis by functional gate sets gives minimum AO size at most 4. Enumerating every ordered distinct-function circuit through size 4 finds 180 minimum circuits, 108 satisfying TopForm, none with junk gates. On 5 vertices, all 290 nonempty forests have minimum size at most 5; topology enumeration finds 3790 minimum circuits, 2110 TopForm, none with junk.

The remaining 5-vertex graph type is C5. CNF circuit synthesis with bundled CaDiCaL finds size 6 UNSAT and size 7 SAT; independent full truth-table evaluation validates the SAT circuit. At size 7, TopForm plus any junk is UNSAT. Thus the proposed junk-antichain/no-junk simplification passes all girth-five graphs on at most five vertices computationally. These are not Lean-checked claims. Programs and complete logs are /tmp/oec/pequalnp-pilot-63/Counterexample_*. Current search extends to C6.

## Alternative route — 2026-11-25T03:05Z

- Primary literature read: Stasys Jukna, *Disproving the Single Level Conjecture*, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf (read 2026-11-25). General quadratic Boolean functions can require far fewer monotone circuit gates than one AND layer; the paper’s counterexamples are saturated extensions containing cliques, so do not settle girth-at-least-five. Its Problem 8.2 asks for explicit quadratic functions with superlinear monotone circuit size. This cautions against invoking a generic arithmetic separated-monomial bound for Boolean circuits.
- Core reduction mathematical audit passed: keep original graph G and circuit C fixed while peeling the target edge graph. The arbitrary H in the core child must range over edge-subgraphs of the exact residual, which the candidate does. Removed degree-one/two vertices contribute at most twice original support, so core bound plus support bound gives original bound with additive constant two. This is not an unproved assertion about recomputing least circuits on induced subgraphs.
- Full support-child proof copied from checked L_meta_2074 and renamed into PEqualNP.Outside.L_meta_1770_aux.Support: results/orch/lemmas/AlternativeSupport.lean, 222 lines. `lake env lean` passed exit 0 at ~03:05Z, only unused implicit-instance binder warning. Log: /tmp/oec/pequalnp-pilot-63/alternative-support-build.log.

### Structural literature check (read 2026-11-25)

Primary source: Stasys Jukna, Disproving the Single Level Conjecture, ECCC TR05-021 (2005), https://eccc.weizmann.ac.il/report/2005/021/download/ . Theorem 5 gives an edge-linear bound for formulas on triangle- and C4-free graphs. Pages 15–16 distinguish arbitrary-fanout circuits: dense C4-free graphs yield superlinear formula bounds, while circuit bounds require additional arguments; Problem 24 asks for a superlinear monotone circuit bound for an explicit graph function. This warns against transferring formula bounds directly to the present circuit model. Current open/closed status since 2005: UNVERIFIED (not established by this paper).

Counterexample update 2026-11-25T03:07:19.408404+00:00: C6 size7 synthesis UNSAT and size8 TopForm+anyjunk UNSAT. Explicit8gate standard star circuit validated on all64 inputs, soC6 minimum8 (computational claim). Full logs Counterexample_sat_6_7_base.solver and Counterexample_sat_6_8_junk.solver. Testing theta graph with path lengths2,3,3 at11gates next.

- Structural clarification 2026-11-25T03:08:08.881451+00:00: OrReaches starts at a junk AND gate and stops there, so no OR-reach between distinct junk gates is already syntactically expected; do not interpret that conclusion as a new nesting bound. The substantive partial is semantic incomparability on graph-negative assignments. No multiplicity bound for nested junk follows from incomparability alone.

Counterexample core check 2026-11-25T03:08:55.131324+00:00: exhaustively generated every labelled girth-at-least-five graph through nine vertices. Counts: n5=303, n6=3424, n7=53365, n8=1121412, n9=31197241. Every computed 3-core is empty, directly validating the proposed core-child finite cases through nine vertices. Source, full count logs, and scope report copied to results/orch/lemmas/Counterexample_*.

Cleanup 2026-11-25T03:10:14.203931+00:00: `ReductionClean.lean` compiles exit0, 80 lines / 7213 bytes (baseline112 lines/8535 bytes). Both hypotheses and exact conclusion byte-identical. Removed generic local wrappers and replaced long support/set proofs by currentMathlib lemmas. Only x4 linter warning remains. Root will re-run namedbuild and checker beforekeeping cleanup.

- 2026-11-25T03:10:17.312681+00:00: strengthened structural partial compiled. StructuralDirect.lean (309 lines) excludes direct AND input dependencies between opposite junk gates. StructuralChain.lean (338 lines) excludes arbitrary nonempty all-AND dependency chains in either direction using Relation.TransGen. Hence a nested opposite-junk pair needs an OR somewhere along every dependency path. The original semantic-separation witness proves this, with no girth/leastness assumptions. No bound on how many edge witnesses reuse such OR gates has been established.

### Structural charging barrier 2026-11-25T03:10:59.070779+00:00

Informal construction (not Lean checked): for an edge uv of G, set g=F OR x_u and h=F OR x_v. Realize each by a monotone CNF with its distinguished variable in every clause. All internal ANDs are dirty because they are true on that distinguished singleton; add an identity AND if necessary. Final g AND h equals F since uv is an edge. Thus TopForm holds, the only top has empty syntactic sides, every graph edge is residual double-junk, and the same g,h pair witnesses all of them. Works for arbitrary high-girth graphs, including minimum-degree-three graphs. The circuit is generally nonleast and expensive. Therefore no constant bound per top or opposite-junk pair follows from girth, TopForm, and semantic separation alone; any successful charge must use leastness or amortized cost of the junk subcircuits.
