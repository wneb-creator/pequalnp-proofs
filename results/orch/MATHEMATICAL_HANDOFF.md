# L-meta-4675 mathematical handoff

Status: **partial work, not a proof or refutation of the posted gap**.
The 3,547-line `lean/PEqualNP/Outside/L_meta_4675.lean` consolidates helper results.
It does not declare the required theorem `PEqualNP.Outside.L_meta_4675`.
No checker acceptance of the posted statement is claimed. Build and checker status belong in `validation.txt`.

## Goal and terminology

For a C4-free bipartite edge set E, an exact fan-in-two backward AND/OR circuit C computing its edge function,
and `TwoColour.tCount = 0`, find a vertex cover S with `E.card + S.card ≤ C.size + 1`.
Inputs are free; every gate counts. The two vertex classes supply the input colours.

A wire's `singletonSupport` consists of inputs whose one-hot assignments make that wire true.
An AND is **clean** when its truth implies the target edge function on every input; otherwise it is **dirty**.
A **birth** is a reachable AND with nonempty singleton support at both operand wires.
The condition `tCount = 0` concerns syntactic OR-only reach, which stops at AND gates.
It does not, by itself, make semantic singleton support monochromatic or make ANDs false on one-hot inputs.

## Strongest checked results

1. **Clean circuits satisfy the requested bound.**
   `Reuse.clean_bound` proves the exact bipartite conclusion under the additional hypothesis that every AND is clean.
   It needs C4-freeness, `IsAO2`, and exact computation; it does not need `tCount = 0`.

2. **Dirty ANDs accepting at most one target edge can be repaired simultaneously.**
   `Normalize.erase_unique_edge_dirty` assumes `IsAO2`, exact computation of a nonempty graph edge function,
   and that every dirty AND accepts at most one distinct undirected target edge on pair inputs.
   Replacing each such gate by an endpoint conjunction preserves size, the full function, and `tCount`, and makes all ANDs clean.
   `Normalize.unique_dirty_graph_bound` adds C4-freeness and obtains the vertex-cover lower bound.
   Consequently a counterexample must contain a dirty AND accepting at least two distinct target edges.
   The hypothesis is not derived from `tCount = 0`.

3. **Every edge has a projected certificate at an actual reachable AND input.**
   `Reuse.graph_projected_actual_slot` assumes a monotone fan-in-at-most-two backward circuit,
   a bipartite colouring, and exact computation of the graph edge function.
   For an edge (a,b), it finds a reachable AND operand w whose singleton support contains a,
   and whose support elements of a's colour all lie in N(b).
   It needs neither C4-freeness, `tCount = 0`, nor one-hot-false ANDs.
   The proof tests the independent input consisting of b and all same-colour non-neighbours of b.
   This is a certificate about a projection of an existing support, not a construction of a wire computing that projection.

4. **Semantic colour and useful gate budgets hold under an explicit one-hot restriction.**
   `Reuse.unitfalse_semantic_monochrome` derives monochromatic singleton support from `IsAO2`, `tCount = 0`,
   and the extra hypothesis that every AND output has empty singleton support.
   `Reuse.positive_gate_budget` requires that hypothesis only for reachable ANDs, plus monotonicity and backward reads.
   It bounds the number of distinct positive operand slots at AND gates, plus the designated OR merges, by `C.size + 1`.
   `Reuse.certificate_budget` additionally requires a selected subset of births, an actual operand and adjacent centre at each,
   and coverage of all graph edges by those whole-support stars. It then supplies the cover and the desired budget.
   The star selection is an assumption, not a consequence of the slot certificates.

5. **Pure rectangle flags admit a clean semantic cover.**
   `FlagCover.clean_rectangle_cover` considers generators `hit A_i AND hit B_i` and an arbitrary monotone upper Boolean function F.
   Assuming soundness on all inputs and acceptance of every target edge pair, E is covered by
   `A_i × {b in B_i | every a in A_i is adjacent to b}`.
   If every A_i has at least two elements, C4-freeness makes each cleaned line side a singleton or empty;
   `clean_star_cover` gives globally consistent stars, and `finite_centres` extracts finite centre choices.
   `active_certificate_cases` isolates the remaining possibility: active generators with singleton point and line sides.
   These are semantic results for pure generators. They do not establish an equal-cost transformation of an arbitrary circuit.

6. **Linear families with small pairwise intersections require disjoint OR resources.**
   `Reuse.linear_family_budget` assumes selected wires in one monotone backward circuit compute the linear OR functions on sets S_i,
   with `|(S_i ∩ S_j)| ≤ 1` for distinct indices. It proves `sum_i (|S_i| - 1) ≤ C.size`.
   It needs no `tCount` or one-hot-false-AND assumption, and allows AND gates.
   The proof expands gates false on the input setting everything outside S_i true, then counts disjoint pools of large-support OR gates.
   `seven_triple_linear_outputs_need_fourteen` gives 14 gates for seven such triples.
   Thus a 13-gate precomputation of all seven Fano neighbourhood ORs is impossible; this does not exclude every 26-gate Fano circuit.

The rectangle-family cover lemmas give the final combinatorial step once an appropriately priced family of clean stars is available.
Further checked local reader-pricing lemmas constrain nonstar readers of one pure dirty rectangle; their assumptions must be retained.

## Strategies refuted or restricted

- **One safe whole-input star per unchanged birth is false.**
  The checked masked-theta construction has 8 inputs, 9 edges, 26 gates, `tCount = 0`, and every AND false on one-hot inputs.
  Only eight safe singleton input slots are available, so one whole-support star per birth cannot cover all nine edges.
  This refutes that allocation strategy, not the posted gap. Its `|E| + tau = 13` is below its positive-slot/merge count of 22.
- A larger projective-plane construction has a boundary-only count below `|E| + tau`.
  That evidence is exact Python arithmetic and finite checking, **not Lean-checked**, and still does not refute the full circuit-size bound.
- Removing one identity AND can expose a point to an arbitrarily long OR chain and increase raw `tCount` by many gates.
  Therefore one credit per removed mask does not generally pay for the increase. Minimality would require a separate argument.
- `tCount = 0` does not imply READ-1, an OR output, or that every dirty AND accepts at most one edge.
  Checked small examples disprove proposed intermediate implications; none is a counterexample to L-meta-4675.
- Counterexample searches produced no checked refutation. Heuristic failures and solver timeouts are not lower bounds.

## Remaining mathematical gap

The missing step is a global budget for shared gates that turns the semantic certificates into a cover at total cost at most `C.size + 1`.
Projection may discard part of a wire's support, but a wire computing the projected OR is not supplied for free.
A support can be reused by several readers; singleton masks and upper ANDs with no positive operands can require further filtering.
C4-freeness makes the centre unique for a large safe support, but does not price every residual singleton certificate or reconvergent region.
The unrestricted singleton-mask model can contain an arbitrary monotone edge-function computation above its generators.

A successful continuation must either prove a size-nonincreasing normalization to a class already covered by the checked budgets,
or charge multi-edge dirty regions, projections, and repeated use directly without counting the same gate twice.
The full independent-input correctness condition matters: pair-input truth alone does not rule out false positives on larger independent sets.
The current results do not justify adding cleanliness, one-hot falsity, unique dirty-edge acceptance, or a global star assignment to the posted hypotheses.
