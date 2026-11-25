# Reusable wrapper lemma map

These are checked components toward a possible counterexample, not a proof or refutation of L-meta-2962. All listed Lean artifacts use only `Mathlib` and `PEqualNP.Defs`. They are standalone snapshots sharing copied infrastructure; combine their new namespace tails, rather than importing several snapshots and duplicating declarations.

Let `m = C.gates.length`. The wrapper appends `q = C.output OR z` and `r = q AND C.output`, at gate indices `m` and `m+1`. Its output is initially the wire of `r`.

| Artifact / namespace | Reusable conclusion | Main assumptions |
| --- | --- | --- |
| `ReadVectorSupport.lean` / `L_meta_2962_aux.ReadVectorSupport` | `pair_vec_shape`: pair vectors have two coordinates. `below_pair_vec_pos`: both coordinates of every vector are positive. | AO2, valid old wire; positivity additionally requires that wire's function be below the graph edge function. |
| `WrapperVectorsSnoc.lean` / `L_meta_2962_aux.WrapperVectors` | `AV_append` preserves old read vectors; `AV_snoc` gives exact vectors of an appended gate. `or_and_vector_repeats` supplies the pure capped-count obstruction. | Prefix invariance requires a valid old wire. The appended-gate equation has no wellformedness assumption. The pure obstruction assumes the old vectors have pair shape and positive coordinates. |
| `WrapperReadTwice.lean` / `L_meta_2962_aux.WrapperReadTwice` | `wrapper_AV` computes the two-gate wrapper's vectors. `wrapper_readTwice` proves `ReadTwiceAt` for the new AND gate, for every vertex pair. | AO2, valid old wire, old wire below the graph function, and a valid raw input `z`. Acceptance of the pair is not needed for this lemma. |
| `AbsorbWrapper.lean` / `L_meta_2962.AbsorbWrapper` | `correct` preserves output semantics, `ao2` preserves AO2, `r_below`, `q_not_below`, and `gamma_all` identify the new gates. | Valid old output; semantic graph statements additionally assume the old circuit computes the graph function exactly. |
| `AbsorbWrapperCore.lean` / `L_meta_2962.AbsorbWrapper` | `isCore` proves the new AND is a core. | AO2, valid output, exact graph function, and at least one graph edge. |
| `WrapperCone.lean` / `L_meta_2962_aux.WrapperCone` | Append preserves `Step`/`Reach`; `inCone_append_reader` propagates old output reachability. `maximalCores_eq_singleton_final` and `coneSet_eq_range_final` handle a final core containing every prior gate. | ReadsBack for the extended circuit, plus the explicitly stated cone/core premises. |

`WrapperMaximal.lean` is the compiled compact final composition. It adds `wrap_all_previous`, `wrapped_maximalCores`, and `wrapped_coneSet`: if every old gate is reachable from the old output, the wrapper's only maximal core is `m+1` and its cone contains all `m+2` gates. Its semantic assumptions are those of `AbsorbWrapper.isCore`; the cone identity alone needs only AO2, a valid old output, and old-gate reachability.

`WrapperDominance.lean` adds the compiled `WrapperCone.maximalCores_eq_singleton_of_core_dominance`: under ReadsBack, a core containing every other core strictly in its cone is the unique maximal core. The designated core need not be the final gate. This is the appropriate bookkeeping lemma after appending output circuitry, once that circuitry has been proved core-free and prefix core properties have been transferred.

## Conditional amplification accounting

A 26-gate exact circuit for one Fano incidence graph would not directly defeat the target using the two-gate wrapper. Three disjoint copies, joined by two OR gates, would have 80 gates. Wrapping gives 82 cone gates and one maximal core. The disjoint graph has 63 edges and vertex-cover number 21, so the target would require `84 <= 83` when the deleted-edge residual is empty. This is conditional arithmetic; no such 26-gate witness has been obtained or Lean-checked.

## Remaining obligations for a full refutation

1. Obtain and Lean-check an actual small exact circuit. An interrupted or timed-out SAT run supplies no witness and no lower bound.
2. Construct the disjoint copies and verify exact semantics, gate indices, and reachability of all gates used by the wrapper.
3. Meet `IsLiftFixedPoint`. The wrapper with output `r` does not solve this: its live OR `q` is not below the graph function but has an implicant operand. Keep the wrapper outside the final output cone, using an independently justified fixed-point output circuit, and show the added output circuitry creates no additional cores that alter the accounting.
4. Prove graph bipartiteness, the absence of four-cycles, and the precise cover/cardinality facts. For the 42-vertex amplified graph, avoid enumerating all vertex covers; a disjoint matching of size 21 proves the lower bound, while the 21-vertex bipartition gives the upper bound.
5. Transfer old-gate semantics, read vectors, and maximal-core accounting through any final appended output circuitry. The current final-root singleton theorem applies before that extra circuitry; preservation must be proved explicitly afterward.

The general core-cover inequality is still unresolved. These components establish the wrapper's local behavior and the principal cone bookkeeping, not the global claim.
