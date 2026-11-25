# L-meta-2583 independent strategy and submission review

Reviewed 2026-11-25 by the setup/review agent. This records partial progress and remaining obligations; it is not a completed proof or checker verdict.

## What the earlier source establishes

The source retrieved from PR 13723 is preserved at `/tmp/oec/pequalnp-pilot-103/2583-pr13723.lean` during this run. It has 7090 lines. The useful theorem locations in that source are:

- `plane_read_one_upper`, line 1216: a circuit of size at most `N * (q + 2) - 1` with the required semantic read-one property exists.
- `read_one_cover`, line 3162: a read-one circuit for a graph with no four-cycle yields a vertex cover and the size accounting needed for an exact read-one lower bound.
- `read_one_plane_lower`, line 3395: every read-one circuit for the plane incidence function has size at least `N * (q + 2) - 1`.
- `read_one_replacement_iff_size`, line 3416: the posted replacement conclusion for a given arbitrary circuit C is equivalent to `N * (q + 2) - 1 ≤ C.size`.
- `exists_least_graph_top_fixed`, line 4817: one may pass to a least circuit with the stated normalized top form. This does not prove that every remaining AND block is a star.
- `surplus_identity`, line 5746, and `elig_le_Bplus`, line 6047: current fanout accounting charges one unit per eligible variable.
- `graph_size_ge_inputs_add_cover`, line 6631: the current unrestricted generic lower bound combines the number of essential inputs with a minimum cover bound.
- `point_degree`, line 6716: the missing-looking dual regularity assumption is derived from the posted point-join and line-degree axioms. There is no identified hypothesis flaw here.
- `unrestricted_plane_size_lower`, line 7075: the current unrestricted lower bound is only `3 * N - 1`. The source does not finish the posted target theorem.

The essential unproved strengthening is from `3N - 1` to `N(q + 2) - 1`. In the normalized live-DAG identity, the total fanout surplus must increase from the presently established lower bound N to the needed Nq. Multiplying the existing eligible-label count by q is not justified: gates with multiple labels can share the surplus charges.

`ReadK.IsReadK` is a semantic proof-tree condition per prime implicant. Treating it as a global fanout-one or syntactic read-once condition would change the problem. Arithmetic multilinear lower bounds therefore cannot simply be applied to the unrestricted Boolean circuit.

## Quantitative edge-deletion bridge

The independently developed file `lemmas/Deletion.lean` proves the following for any balanced d-regular bipartite incidence relation, with d positive. If P and L cover all edges outside a deleted set U, then

```
N * d ≤ (|P| + |L|) * d + |U|
N ≤ |P| + |L| + |U| / d
```

Here division is natural-number floor division. This is equivalent to the proposed lower bound `N - floor(|U|/d)` for a vertex cover after deletion. The proof counts edges incident to P or L and charges every remaining edge to U. The estimate is sharp for deleting all incident edges at several vertices on one side. No projective-plane axiom beyond equal degrees is needed. The finite fiber-count helper proofs are adapted from the earlier PR's `restricted_incidence_card_left/right`; the deletion and floor bounds are added here.

Validation: `lake env lean ../results/orch2583/lemmas/Deletion.lean` completed with exit code 0. Complete stdout and stderr are in `/tmp/oec/pequalnp-pilot-103/2583-deletion-second.stdout` and `.stderr`, both empty. The source is 104 lines, 4757 bytes, SHA256 `9aac0235e290a080ad046fd0bef8644ebb01987d3962099e1836adb3481f39be`. This is standalone Lean elaboration, not the posted-target checker.

Let m be the full edge count, t the number of non-centreless tops, u the number of Ustar edges, and B the sum `2 * centreless + junk + otherOR`. L_meta_4183 gives `m + t + B ≤ size + u + 1`. The deletion-cover bound gives `N ≤ t + floor(u/d)`. Combining them proves the desired `m + N - 1 ≤ size` provided the additional circuit charge

```
u + floor(u/d) ≤ B
```

is established. Geometry alone does not establish that charge. For `u < d`, the condition reduces to `u ≤ B`.

## Existing partial charge results

A bounded census found 143 Outside files mentioning Ustar, including 51 L-file final theorem statements. No direct refutation of the proposed charge was found in that census; this is not a proof that no counterexample exists.

- L_meta_6240 proves `2 * u ≤ B` under the extra hypothesis that each gate in centreless, junk, or mixing owns at most one Ustar edge. This would imply the proposed charge when `d ≥ 1`. The ownership restriction remains unproved for arbitrary plane circuits.
- L_meta_8103 proves a stronger full-cover accounting result when `junk.card = 1` and Ustar is nonempty: there exists a vertex cover K of the full graph with `|K| + u ≤ t + B`. Combining this directly with the regular full-cover lower bound and L_meta_4183 settles that restricted case.
- L_meta_7077 includes the fact that no junk implies empty Ustar, so the zero-junk case is also compatible with the straightforward accounting route.
- R_meta_5066_2 packages a related full-cover charge as a hypothesis for balanced bipartite graphs with a perfect matching and minimum degree two. Its presence as a reduction does not establish that hypothesis.

The unresolved cases are arbitrary multiple junk gates and ownership of multiple omitted edges. Replacing these by an unproved per-gate bound would merely restate the hard part.

## Submission boundaries

The current desk record allows `PEqualNP.Defs` and does not mark this step as a refutation or open it to reductions. The local checker version 4 supports `check`, `refute`, and `reduce`, but the authoritative workflow and `.github/scripts/outside-guard.mjs` additionally enforce the desk kind. A local refutation check is not evidence that an ordinary proof-step PR will be accepted in refutation mode. Likewise a conditional reduction cannot be submitted for this row without the desk opening reductions.

An accepted proof submission must have exactly the posted theorem, with its expected full name, and the final PR net diff must contain only the named Lean file. Preservation-branch results and partial lemmas are useful durable checkpoints but do not themselves meet that condition. No checker acceptance has been claimed for these partials.

## Literature scope

On 2026-11-25 I read Jukna, *Notes on Boolean Read-k and Multilinear Circuits*, https://arxiv.org/abs/2207.08701 and https://web.vu.lt/mif/s.jukna/ftp/readk-submit.pdf. It confirms the semantic read-k distinction and the connection of read-one circuits with homogeneous multilinear arithmetic. I found no projective-plane-specific theorem there that settles the unrestricted Boolean lower bound. General separation results and linear design-matrix circuit bounds do not close this gap.
