# Circuit geometry strategy

## 2026-11-24 23:15 UTC findings

- A witness center `u` is in `wmax G C g`. This uses only AO validity, top membership, raw reach of `u` on one side, and OR reach of `g` on the other; leastness and top form are not needed. Checked helper `L_meta_3805.top_wmax` proves the semantic statement.
- `L_meta_3805.main_bound` gives coefficient 54 for the entire one-sided Ustar set under junk-cone incomparability, with no assumption on the junk count. Its published theorem unnecessarily includes at least three junk gates. The proof works because no junk gate then has AND ancestors, so each junk gate is AND of two raw OR supports.
- `L_meta_4322` removes junk incomparability and gives coefficient 27 for witnesses whose selected junk gate has both raw sides intersecting the edge pair. Root already identified this.
- `L_meta_4005` proves every input accepted by any junk gate is accepted by some junk whose two raw sides each hit the input. This does not preserve the original top OR-context, so it cannot directly combine with L_meta_4322.

## Remaining obstruction

A nested junk gate may have a dirty minterm of size at least three. Its selected edge still has a bottommost raw-exposed junk ancestor, but the context `x_u AND gate <= f_G` need not propagate through AND masks on the path to that ancestor. If each mask is true on singleton `u`, context does propagate. A mask requiring `v` makes `u AND v` already imply the graph function and requires a different charge or circuit shortening argument.

## Potential useful refinement

For fixed `v`, the final disjointness assumption says selected opposite raw-side sets are pairwise disjoint. If all are nonempty, choose one `w_e` in each. Girth five implies the selected `u_e` have pairwise private neighbors `w_e`: another `u_d` adjacent to `w_e` would form the 4-cycle `v-u_e-w_e-u_d-v`. The raw-empty opposite sides are not controlled by this observation.

## Explicit masked-frontier reduction proposal

Use the existing raw-exposed edge bound L_meta_4322 as one child. The other child bounds the following finite subset of Ustar: edges `e=s(u,v)` with top `a`, side `b`, junk `g`, `u in side a b`, `g` OR-reached from the opposite top operand, and a side `c` of `g` such that neither endpoint lies in `side g c`, but `g` fires on `pairInput u v`. This is the genuine remaining masked-input case, stronger than merely asserting that some junk gates are nested. A refined formulation also names a junk `h` OR-reached from operand `c` of `g`, true on the same pair; this h is necessarily strictly below g. No transfer of the top context to h is asserted.

Raw and masked subsets cover every witness. The raw child is already checked. The masked child is a narrower circuit configuration than the original witness set, and is distinct from R_meta_1770_1.oneSing, which assumes the selected junk is false on both endpoint singletons. This masked case includes singleton-v junk and quadratic junk but forces actual hidden computation below an AND operand. A local OR-trace lemma plus top form extracts h when desired.

## Finite context-transfer sanity check

Checked all 32 inputs: 8-gate AO circuit computes star edges (0,1),(0,4).
Selected junk g=gate4 has center 0 cleaning context. Its raw-exposed junk ancestor h=gate2 does not.
Counterexample to context transfer: input (True, False, True, True, False).
This circuit is not least (same graph has 2-gate AO circuit). It only refutes context-transfer claims omitting leastness.

Circuit gates, inputs 0=u,1=v,2=x,3=y,4=z: [('or', 1, 2), ('or', 1, 3), ('and', 5, 6), ('or', 1, 4), ('and', 7, 8), ('and', 0, 9), ('and', 0, 4), ('or', 10, 11)].

## Correction: avoid duplicate raw split

R_meta_1768_1 already splits L4322 raw exposure from the globally non-raw witness set. The simple raw/masked split above is not a useful new reduction on its own. A new cut should preserve the rich/disjoint core or expose a strictly more local nested-mask frontier.

## Exhaustive small circuit checks

The scratch script circuit-small.py enumerated every nonduplicate AO gate sequence through depth4 on four inputs (81,985 circuits), and depth5 on five inputs (27,160,961 circuits). Every nonempty forest target was reached at optimum: 37 girth-five graphs on four vertices; 290 forests on five vertices. No least circuit enumerated had a dirty AND. The 12 labeled C5 functions were not reached through depth5. These are computational checks, not Lean proofs.

The original rich core itself is vacuous on at most13 original vertices: the directed incidence graph of its u/v labels is bipartite, C4-free, and minimum degree at least3, so each shore has at least7 vertices. If the shores overlap, that original vertex has at least6 neighbors; their other neighbors are distinct by girth5 and each neighbor has degree at least3, forcing at least19 original vertices. Thus a smallest core uses at least14 vertices and at least21 edges. This is a paper argument, not yet formalized.

## Review of bounded-degeneracy reduction

The existential bounded-degeneracy premise in V3 omits V2's minimum-three-fiber assumption. This is equivalent after increasing its unknown constant: V2 implies V3 with `max d 2`, since a subset failing richness already has a fiber of size at most2. Conversely V3 directly implies V2. Thus V3 is a cleaner, shorter formulation, without materially strengthening V2. The premise is still unproved and must retain leastness. It cannot be inferred from a global bound in terms of the full circuit size alone, because a subset may use only a few of the circuit labels.

## Continued direct attempt, 23:22–23:28 UTC

A sound local surgery principle: if a dirty AND gate has exactly one direct reader, which is a top AND, and replacing that gate by one of its operands keeps the new top below the graph function, then deleting the dirty gate produces a smaller valid circuit. The reader can be modified at its original position, so its other operand need not precede the deleted gate. Leastness therefore forces an independent-set counterexample to each such replacement. This principle alone does not bound role fibers: the reader contexts may differ, and a gate can have multiple readers. No uniform d was obtained.

A checked intermediate is now in DirtyWitnessPartial.lean (68 lines; lake env lean exit0, no warnings). It proves:

1. In a C4-free graph, if every u in A is adjacent to v and to some member of S, with v outside S, then |A| <= |S|. Choosing the second neighbor gives an injection into S.
2. For a monotone gate g accepting an independent support S, every center in wmax(g) has a neighbor in S.
3. Therefore a fixed-(g,v) family of selected centers has cardinality at most |S| whenever g has an independent dirty witness S omitting v.

The remaining barriers are concrete: independent dirty witnesses can be large (nested ANDs), they may necessarily contain v, and bounds on joint (g,v) fibers do not bound one of the four individual role fibers. A uniform d requires a further amortization or circuit-surgery argument.

Checked L_meta_563 gives a possible normalization direction in the AndCountCircuit model: singleton-true ANDs can be stripped while preserving the function and AND count. OR supports are free in that model. Translating it back to root AO circuits can add many OR gates, so it does not yet bound the total size needed here.
