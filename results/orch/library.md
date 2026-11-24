# Library review for L-meta-2028

2026-11-24, status_review agent. Read-only investigation apart from this notes file.

## Assigned statement

L-meta-2028 is the literal negation of L-meta-612: every nonempty C4-free simple graph has monotone binary edge-function circuit size at least |E| + tau - 1. The desk permits Mathlib and PEqualNP.Defs only. PEqualNP.Defs gathers definitions modules; it does not import any Outside theorem. Thus existing Outside results are proof templates, not permitted theorem dependencies. No direct imported result settling either sign was found.

## Exact definitions

- `PEqualNP.MetaComplexity.Monotone2` in `Defs/MetaComplexityLgpMono.lean`: all gates are AND or OR, inputs length at most two. Zero-input AND is true; zero-input OR and absent-wire reads are false. One-input gates copy.
- `Circuit.size` in `Defs/CircuitLowerBounds.lean` is gates.length. Evaluation is a forward fold appending each new gate value. Future wire references read false, so malformed references do not provide hidden backward computation.
- `CoverPromise.IsVertexCover` in `Defs/CoverPromise.lean`: every edge has an endpoint in the finite set.

## Existing reductions of the positive statement

1. `R_meta_612_1`: splits graphs into acyclic and cyclic. This is a classical case split and does not remove the cyclic bottleneck.
2. `R_meta_612_2`: extract a biclique cover of familyCost at most circuit size, then count stars. C4-freeness implies every biclique has a side of size at most one.
3. `R_meta_612_7`: prove at least |E|-1 OR gates and at least tau AND gates separately. Disjointness of gate types yields the total bound.

`L_meta_1902` already proves the second hypothesis of reduction 2: a star-block cover yields a vertex cover S with |E| + |S| <= familyCost + 1. The extraction hypothesis `HasBlockCost G C.size` is the unresolved substantive part; no other Outside theorem uses HasBlockCost/familyCost. The definitions file explicitly warns that block cost need not equal least circuit size for graphs with 4-cycles.

## Partial positive results and limitations

- `L_meta_287` (8237 lines) gives exact AND/OR counts for arbitrary minimal circuits of forest edge functions (also isolated singleton outputs). It should rule out forests by minimizing first, but cannot be imported for this gap.
- `L_meta_599` (1267 lines) proves the OR-gate bound for C4-free pseudoforests, assuming every induced subgraph has at most as many edges as vertices.
- `L_meta_613` (665 lines) proves a total-count bound when every AND output already implies an edge and a designated center bit, and no AND gate depends transitively on another AND. The missing general normal form is substantive.
- `L_meta_614` (801 lines) proves a different n+tau-1 bound for graphs satisfying neighbor-separation assumptions; its t covers only edges between vertices of degree >=2. This is insufficient for dense C4-free graphs.
- `L_meta_2050` constructs projective-plane incidence circuits with size (q+2)N-1, matching |E|+tau-1 rather than refuting it.

## Relevant failed stronger count

`L_meta_1044` is a checked counterexample to a stronger gate accounting claim on 18 vertices, three disjoint copies of a triangle with one leaf at each vertex. The graph has 18 edges, minimum cover 9, and its exhibited circuit has 31 gates, so it does not refute the desired 26-gate lower bound. It shows that naive classifications of wide/thin gates can fail even on C4-free graphs.

## Assessment

No obvious definition loophole or already-checked refutation was found. A useful counterexample search should focus on cyclic C4-free graphs beyond pseudoforests, and circuits with nested AND gates/absorption; plain ORs of star blocks necessarily satisfy the conjectured lower bound. These are search guidance, not a proof that the assigned negation is false.

## Independent partial review

Reviewed `results/orch/lemmas/NonemptyCircuit.lean` and its identical named-file copy. The empty circuit computes an input projection or false, both incompatible with a nonempty simple graph edge function. Mathematical and plain-file review passes; compilation is handled by parent. This proves only positive size, not the posted theorem, and must be labeled partial. Reviewed named-file SHA256: `e45deaa7684f69bc3146f9b0cfe8bdde06fc710c07025fae3d7076b2e628cadc` (37 lines, 1498 bytes).

Compiled `results/orch/lemmas/HasAnd.lean`: every monotone circuit for a nonempty graph edge function contains an AND gate. An OR-only circuit preserves pointwise joins. Each singleton input is rejected but the join of an edge's two singleton inputs is accepted, contradiction. This is a structural invariant beyond positive circuit size. It is still partial progress and not a refutation. Independent definition_audit review passes.

Compiled `results/orch/lemmas/HasOr.lean`: AND-only circuits preserve pointwise meets, including nullary gates and absent-wire reads. Two distinct unordered edges give two accepted pair inputs whose intersection has at most one vertex, so their meet is rejected. Thus a circuit for a graph with two distinct edges contains an OR gate. Independent definition_audit review passes; Lean emitted no diagnostics.

Compiled `results/orch/lemmas/TwoEdges.lean`: combines both helpers and derives circuit size at least two for a graph with two distinct unordered edges. The generic cardinality argument observes that a list of at most one gate cannot contain both an AND and an OR. Independent definition_audit review passes. Logs are `hasand-build-001.log`, `hasor-build-001.log`, and `twoedges-build-001.log` in job scratch. These remain helper-only results; the posted negation is still unproved.

## Independent computational review

Reviewed `search/synth.py`, `search/and-synth.py`, fixed-graph and quotient drivers, random `search.cpp`, `multi.cpp`, `subbounds.cpp`, and the Petersen, truncated-tetrahedron, random-graph and line-Petersen evolutionary sources in job scratch. Reviewed `results/orch/rectangle_search.py` too. No total-bound witness exists at this review point.

Main SAT encoding:

- Conditional AND/OR truth clauses and one-hot distinct earlier sources are correct.
- Three possible four-cycles on each four-vertex set are excluded. Requiring every subset of size n-t+1 to contain an edge means independence number <= n-t, hence minimum cover >= t.
- Fixed graph edge-pair positives and maximal-independent-set negatives suffice for monotone circuits. `BoundaryComplete.lean` and `CircuitMonotone.lean` independently formalize this reason.
- Sorting gates by maximum source index, with minimum source index breaking ties, appears sound: choose the least available pair in a topological ordering. Newly unlocked gates have a source at the newest gate index, larger than all previously available source indices; tied maximum-source gates cannot depend on each other.
- Constants, unary gates and repeated inputs can be removed for a minimum nonconstant edge circuit. An exact-size query can pad a smaller nonempty circuit by repeating its last gate with its previous output and one previous operand. These normalizations are mathematical review, not a Lean certification of the SAT encoder.
- Decoder independently evaluates every Boolean input and enumerates minimum covers. After audit feedback, author added explicit C4 and strict-size checks. Solver UNSAT outputs remain computational evidence only; no Lean-checkable UNSAT certificate was produced.

Important restricted-scope caveat: `and-synth.py --size` charges the expanded cost `sum(selected operands and outputs) - AND count - 1` without sharing OR subexpressions between operands. Its bounded-cost UNSAT result excludes only that represented cost model, not every circuit with the same gate bound. The author added a separate query without an OR budget for the unrestricted AND-count question. Near-template queries exclude only their stated edit neighborhood.

Random searches:

- At current n=6/n=8 dimensions, full signatures, quadratic-function equality, common-neighbor C4 test, exact subset cover enumeration, and ancestor-mask gate counting are sound on inspection.
- Graph six lookup is exhaustive over graphs; circuit generation is stochastic and cannot support a universal circuit lower bound.
- `multi.cpp` and `subbounds.cpp` use a 64-bit graph edge mask, so their generic N setting must remain <=11. Author confirmed only N=8 runs.
- `subbounds.cpp` emits the word COUNTEREXAMPLE for a violation of either component gate-count conjecture too; that does not necessarily violate the assigned total bound.
- Evolution mutations keep each source earlier than its gate, including the conditional gate swap. Star-cover seeds have the expected gate count; any minimum vertex cover is inclusion-minimal, so every selected center has an edge to a vertex outside the cover.

Independent target recomputation from the displayed constructions:

| Graph | Vertices | Edges | Minimum cover | Proposed lower bound | Boundary inputs | C4-free |
|---|---:|---:|---:|---:|---:|---|
| Petersen | 10 | 15 | 6 | 20 | 30 | yes |
| Truncated tetrahedron | 12 | 18 | 8 | 25 | 52 | yes |
| Line graph of Petersen | 15 | 30 | 10 | 39 | 101 | yes |

These figures were independently recomputed by subset enumeration, not taken from a webpage.

Other searches:

- Independently checked the original 11-input quotient seed's hardcoded pairs/triples expansion against its circuit on all 2048 inputs: zero mismatches. Substitution therefore preserves the reviewed expansion.
- Near-circuit quotient search re-evaluates the complete collapsed truth table before accepting a candidate.
- Rectangle search originally recorded the number of live gates while saving the full list, including dead gates. Its negative-margin stopping condition originally did not require `verified`. Reported both to parent; definition_audit implemented pruning/reindexing before every record and requires verified complete truth-table equality, with a failure raising an error. No candidate was claimed as a witness under the earlier behavior.

Independently decoded both SAT positive controls with a separate small verifier: triangle has 3 edges, cover 2, 4 gates, all 8 truth-table rows correct; six-vertex control has 7 edges, cover 3, 9 gates, all 64 rows correct. Both are C4-free and exactly meet their respective 4/9-gate bounds; neither is a counterexample. Verified each decoded source index is earlier than its gate and each selector is uniquely assigned. These controls exercise satisfiable encoding paths but do not constitute a proof of encoder completeness.

## Pair-input diagnostic counterexample

Independently reviewed compiled `PairOnlyCounterexample.lean` (79 lines, SHA256 `fc1fc5f890c0dd28a3a3508e271f69026d943e2e75facfc62c33027cc67ca744`). It describes the six-vertex net graph: triangle 0,1,2 with pendant edges 0-3, 1-4, 2-5. The graph is C4-free, has six edges and minimum cover three. Its seven-gate monotone circuit agrees on all 36 ordered pair inputs but accepts the independent pendant triple {3,4,5}. Independent evaluation on all 64 inputs found exactly that one mismatch (mask 56). Thus it defeats a pair-only weakening of the bound but explicitly does not refute the assigned full-function statement. Kernel `decide` proofs, counts, format, and exact library semantics pass review.

Integrated named-file review also passes: appended namespace body byte-identical to the standalone source; named file 537 lines, SHA256 `59c400a52170bd0dd402bd28db841a7fe820252d71586689d482074d3c015cbf`.

## Later search and preservation review

ER3 shared-A encoder/decoder independently reviewed. The 31-gate control's model satisfies all 24,085 CNF clauses; each local piece has seven positive edge pairs and three maximal independent sets. The three local pieces plus the B triangle cover exactly all 24 target edges. Separate evaluation of all 8192 inputs gives zero errors, minimum cover eight, C4-free, and bound 31. The 30-gate search tests only this shared-A/local-six-gate decomposition; its UNSAT outcome does not exclude unrestricted 30-gate circuits.

C5 fixed-prefix multioutput encoding independently reviewed. The nine-gate control has the exact prefix OR(0,1), OR(2,3), valid source indices, and correct final C5 function on all 32 inputs. The eight-gate solver run reports UNSAT. The scope is computing the graph output together with those two auxiliary signals, which may be unused by the final output. The graph is fixed, so unknown-graph first-pair normalization is not involved. This is a solver result, not a Lean certificate or an unrestricted C5 bound.

Pendant-star gadget objective independently reviewed. For each safe OR(S), a new center adjacent to S and a private leaf adds |S|+1 edges, exactly one to minimum cover, and three gates using the precomputed signal. Old cover plus all centers gives the upper bound; each private leaf edge forces one additional cover vertex for the lower bound. No pair in S may have a common old neighbor, and different selected supports must intersect in at most one vertex. These exclude four-cycles with one or two new centers. The correct gain is `|E|+tau-1 + sum(|S|-1) - live union-ancestor cost`. A positive hit still needs full DAG pruning, input/gate index shifts, construction of the enlarged graph and independent truth-table validation.

All thirteen saved edited graph targets independently pass: eleven vertices, fourteen edges, cover number six, C4-free, bound nineteen and target eighteen gates. Their maximal-independent-set lists are complete. A separate exhaustive permutation check using vertex invariants confirms every one of the 78 pairwise isomorphism decisions and exactly eight classes. The eight leaf-stripped target files also pass independent C4, cover and maximal-independent-set checks. These artifacts are graph targets only.

The graph census source and provenance were reviewed. Independent graph6 decoding checks all 117 seven-vertex, 351 eight-vertex and 1230 nine-vertex rows for C4-freeness; connected minimum-degree-two counts are respectively 10, 28 and 112. For the preserved 140 eight/nine-vertex core records, edges, minimum-cover values, maximal-independent-set lists and proposed bounds independently agree. Runtime help confirms geng's flags. Census completeness depends on the pinned nauty generator, as its README states; core filtering is a heuristic, not a theorem about counterexamples.

Preservation safety review found no credentials, authenticated URLs, private keys or lease UUIDs in the reviewed archive. Search snapshots and graph-edit programs only perform local computation, explicit file writes, and local solver subprocesses. Both stored SHA manifests match their files (114 main archive records, 22 supplied inputs). The incomplete archived `seed11-and6-sorted.log` is deferred along with its main inventory manifest until the run's complete diagnostic is copied; running scratch logs, caches and the duplicate NonemptyCircuit scratch file are excluded from the preservation manifest.
