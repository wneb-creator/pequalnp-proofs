# L-meta-2028 definition audit

2026-11-24 UTC. Exact desk statement read from desk-answer-001.json.

- `Circuit.size` is precisely gates.length. All gates count, including constants and copies.
- `Monotone2` checks every gate's operation is AND or OR and its input list has length at most two.
- No well-formedness predicate is assumed, but this is harmless for cheap nonlinear witnesses: gates fold left, forward/missing references evaluate false. There is no cyclic or free gate semantics.
- Circuit output may name an input or a missing wire; neither computes a nonempty simple graph edge function without actual gates.
- `Fin n` makes the graph finite; `SimpleGraph` enforces symmetry and looplessness; edgeSet counts unordered edges.
- `IsVertexCover` is the conventional edge-covering vertex set predicate. Existence at size t plus universal minimality correctly fixes t to the cover number.
- The six pairwise-distinctness hypotheses and four adjacency hypotheses exclude all simple four-cycles, not just induced four-cycles.

No definitional loophole found.

## Related refutations examined

`Outside/L_meta_1006.lean` gives an 11-vertex C4-free graph (16 edges, cover number >=7) and a 6-AND circuit with free ORs. Translating its formulas appears to cost 20 total gates, apparently below 22, but its specification only requires values at maximal independent sets and their immediate supersets. Exact evaluation on all 2048 assignments finds 39 mismatches with the edge function, all false negatives. For instance {6,7} is an edge but the circuit returns false. This candidate does NOT prove our target.

`Outside/L_meta_1044.lean` refutes a stronger weighted accounting invariant using three disjoint triangles with pendant leaves; its circuit has 31 gates against E18+tau9-1=26, so not a counterexample to our target either.

## Existing positive reductions

`R_meta_612_2` reduces the positive bound to extracting a block-cost certificate and counting stars; C4-freeness forces each complete bipartite block to be a star.

`R_meta_612_7` separates OR >= E-1 from AND >= tau. A counterexample to the target must break at least one of these bounds, though breaking either alone does not suffice.

## Independent partial-proof review

Reviewed `results/orch/lemmas/HasAnd.lean` after its author compiled it. PASS: all-OR circuits preserve pointwise Boolean joins, including default-false invalid references, while a nonempty simple graph edge function is false on singleton inputs and true on an adjacent pair. The helper therefore correctly proves an AND gate exists. Namespace, allowed imports, no forbidden words/quotes/attributes/options, regular file, and scope checked. Full compiler log contains only an unused simp argument warning. This proves a helper, not the posted negation.

## Structured rectangle search

`rectangle_search.py` sampled 100,000 circuits with 8–14 inputs, one shared rectangle R=(OR A) AND (OR B), and 2–5 mixed filters (R OR local-star-side) AND other-star-side. It computed all degree-2/3 monomials exactly, rejected quadratic graphs containing a 4-cycle, and greedily added C4-safe graph edges to absorb remaining higher-degree terms. The added edges were implemented by a minimum-cover star circuit. It counted the actual commutatively hash-consed circuit DAG and computed the final graph's minimum cover exactly.

Counts: 16,062 initial C4-free quadratic graphs; 6,877 successfully repaired graph functions. No bound violation. Best size was 10 versus bound 9 on ten inputs; all 1,024 assignments were verified for that best candidate. Full log is `/tmp/oec/pequalnp-pilot-31/audit/rectangle-100k.log`; best data is `rectangle-best.json` beside it. This randomized family search is not an exhaustive nonexistence result.

Structural obstacle: quadratic rectangle edges surviving through these filters are exactly those incident to selected rectangle vertices. C4-freeness permits at most one selected vertex from each rectangle side, so the surviving part is a double star with at most |A|+|B|-1 edges and cover at most two. Without extra sharing, k filters cost at least k-2 gates more than the crude E+tau-1 upper bound can require. Shared neighbor ORs across distinct star centers themselves create a C4; repeated filters at one center can be combined. A two-rectangle extension is prepared to test whether nonlinear intersections escape this obstacle.

The two-rectangle extension sampled another 100,000 families and found 13,750 valid repaired graph functions, none violating the bound. Its best tie used only one rectangle. A focused run then forced both rectangles to be active: 300,000 families, 24,485 initially C4-free quadratic graphs, 9,698 valid repaired graph functions, best margin +2 (14 inputs, 14 gates, bound 12), verified on all 16,384 inputs. This is evidence against these restricted families, not a proof of the target bound.

Search records now always prune and reindex dead gates, so `size` equals the stored gate list length. Any failed independent full truth-table check raises an error rather than reporting a witness. All three complete logs and compact verified best examples are archived under `results/orch/rectangle-results/` for preservation.

A tight one-rectangle motif is (R OR l) AND (a OR b), where R=(OR A) AND (OR B), a∈A, b∈B, and l lies outside A∪B. It realizes a double star plus the triangle a-l-b at exactly E+tau-1 gates. Reusing R for a second such tight motif in a C4-free union forces the same a,b: selecting a second vertex from either side exposes a K2,2. A second distinct l then creates the C4 a-l-b-l′. Thus this direct sharing of tight motifs cannot yield the desired gain.

## Dynamic near-witness repairs

The 18-gate dynamic snapshot has a 15-edge, cover-number-5 quadratic graph and four unwanted minimal triples {0,5,8}, {1,5,8}, {3,5,8}, {5,6,8}. Its exact first component is a 7-gate, 6-edge, cover-number-2 triangle-with-leaves function. The second component is

(x2 OR (x5 OR x7) AND (x9 OR x8)) AND (x0 OR x1 OR x3 OR x6 OR x7 OR x9).

Its unwanted triples arise from the unselected rectangle edge5–8. Removing the four external leaves from the second component leaves an exact 6-gate, 5-edge, cover-number-2 graph function. Reattaching independent optimal star gadgets cannot undercut E+tau-1 without sharing: vertex-cover number is subadditive under graph union, while OR joining adds the matching gate cost.

`near_repair.py` checked all256 ways to split the second occurrence of each of the8 twice-used inputs; none yielded a pure quadratic function. It also checked all70,490 choices of up to4 individual input occurrences set independently to Boolean constants. Semantic simplification and dead-gate removal gave3,756 pure graph functions, of which1,732 were C4-free; none beat the bound (best margin0). This is occurrence-local cofactoring, not merely global input substitution.

With `--expose`, each edited circuit was also tried after OR-ing into the output one or two hidden AND intermediates not already implied by the output. Total110,253 output variants from70,746 edit patterns:14,412 pure graph functions,3,182 C4-free, no violation, best margin0. Every best record was independently verified across all Boolean inputs. Full logs and compact examples are under `near-repair-results/`.

`gadget_graphs.py` enumerated the17 inclusion-minimal edge-addition sets that cover all four unwanted triples, and all existing-edge deletions up to the first feasible cardinality. Adding5–8 needs at least2 deletions; all9 minimal repairs have target bound at most18. Without5–8, one chooses z–5 or z–8 for each z∈{0,1,3,6}; all16 such choices need at least5 deletions. Thirteen choices admit a repaired C4-free graph with14edges and cover number6, hence target18gates against bound19. One maximum-bound repair per such choice was saved, not every possible repaired graph.

`near_graph_targets.py` independently checked these13 saved graphs by explicit four-vertex cycles and exhaustive2^11 independent-set enumeration, then deduplicated them into8 isomorphism classes by exact adjacency-preserving backtracking. `near-edited-graphs.json` holds all13, the8 representatives, and their complete lists of maximal independent sets. The representatives have18–22 maximal independent sets. They are new graph targets, not counterexamples; no18-gate circuit has been found.
