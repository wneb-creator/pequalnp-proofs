# L-meta-2448: graph geometry route

The graph-combinatorial part needs only triangle-freeness: any nonempty family of graph edges whose pairs intersect has a common endpoint. The standalone proof compiled successfully after cache restoration.

For an arbitrary computing circuit, star ownership is false. On the two-edge matching with vertices a,b,c,d, the circuit

`((a OR c) AND (b OR d)) AND ((a OR d) AND (b OR c))`

computes `(a AND b) OR (c AND d)`. Its first AND owns the disjoint edges ab and cd. It has seven gates, whereas the canonical circuit has three. Therefore least-size selection or an exchange argument is essential.

Accepted reduction `lean/PEqualNP/Outside/R_meta_2448_263.lean` has the stronger local fact needed for normalization: if one monotone two-input AND gate owns two disjoint pairs, in a C4-free graph it fires on some nonedge pair (possibly a singleton) among their four endpoints. The proof is its local `pairDirt` fact. It proceeds by extracting OR-only reachability from each endpoint to the gate's two inputs; a clean four-endpoint truth table would otherwise create a C4. The reduction assumes separate size-preserving repairs for singleton and distinct-nonedge false positives and minimizes the number of gates owning disjoint edges.

The root assigned formalizing the common-center lemma and a clean-gate-to-star wrapper to this agent. The global size-preserving repair remains with the normalization strategy.

## Checked components

`lemmas/StarGeometry.lean` now has 453 lines and uses only `import PEqualNP.Defs`. It compiled with pinned Lean 4.36.0, exit code 0, via direct `lake env lean`. Logs: `/tmp/oec/pequalnp-pilot-74/star-geometry-combined-002.stdout` and `.stderr`. One unused-simp warning remains; there are no errors.

Declarations under `PEqualNP.Outside.L_meta_2448`:

- `common_center_of_pairwise_meeting`: the graph-only common-center lemma, independently written here.
- `owned_disjoint_edges_have_false_positive`: the 340-line local `pairDirt` fact adapted from accepted `R_meta_2448_263.lean`, with no outside-file dependency.
- `hasStarProfile_of_pairwise_meeting`: packages common centers for the circuit profile definition.
- `hasStarProfile_of_pair_sound`: a monotone circuit has star profile if every AND gate is true only on adjacent pairs, assuming the graph has no triangle or C4.

This is a partial component, not a proof of L-meta-2448. The unproved step is finding an optimal circuit whose relevant gates satisfy such cleanliness, or another property ensuring pairwise-intersecting ownership.
