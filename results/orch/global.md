# Global normal-form strategy for L-meta-2448

## Checked partial

`owns_bipartite_of_singleton_silent` proves the following, for any monotone fan-in-two circuit and any gate `j`:

If gate `j` is false on every singleton input, then there exists a Boolean coloring of the input vertices such that the endpoints of every pair owned by gate `j` have different colors.

This needs no graph or girth hypotheses. It generalizes the five-cycle-specific singleton obstruction used in `R_meta_2448_17`: any odd cycle in an ownership graph forces the gate to be true on some singleton.

The first standalone file, `/tmp/oec/pequalnp-pilot-75/global/OwnershipBipartite.lean`, compiled successfully with the pinned Lean version. Its first 317 lines adapt checked wire/cone/OR-reach foundations from `L_meta_1762`; the final lemma is new. The 64-line fragment `BipartiteShort.lean` also compiled successfully against the structural strategy's shared foundations, with no warnings.

`BipartiteLocal.lean` further localizes silence to an arbitrary vertex set and derives `odd_owned_closed_walk_has_singleton`: a closed owned walk of length `2*k+1` has a singleton-firing vertex among the walk's vertices. The first build passed; redundant cleanup tactics were then removed, and the final build also passed with no warnings. Root was advised to prioritize the main exchange problem over this optional strengthening.

## Proof idea

For each input of an owning AND gate, the no-earlier-AND condition in `Owns` forces its truth on an owned pair to arise from an OR-only path from one endpoint. A gate that is silent on every singleton must have two inputs. Color a vertex by whether it makes the first input true. No vertex can make both inputs true. Each owned pair must make both inputs true, so its two vertices have opposite colors.

## Global argument status

The difficult step remains replacing gates that are true on nonedges or singletons without increasing circuit size. Local distributivity can extract a singleton from `(u OR A) AND (u OR B)`, but shared input subcircuits can make this increase size elsewhere. Nothing here proves that a minimum circuit is singleton-silent, pair-sound, or has a star profile.

The repository's note on exact edge-function size only supports general lower bounds for forests, cycles, and long-thread classes. Its cited single-level conjecture counterexamples are saturated graph extensions with cliques within both bipartition sides, so those constructions do not satisfy this task's triangle/C4 exclusions.

## Sharing/charging observations (not yet formalized)

For a dirty singleton diamond `g=(u OR a) AND (u OR b)` owning edge `ab`, a direct clean user `h=a AND (u OR b)` already accepts every input lost by replacing `g` with `u`. If `h` is exposed to the output through OR gates, this replacement preserves the function and removes `g`. Thus clean direct sharing is potentially dispensable, while useful external users may remain dirty.

Diamonds sharing factors `u OR a_i` form a graph on the `a_i`. Its owned edges may form long cycles even when triangles/four-cycles are forbidden, so earliest-gate arguments do not ensure an unshared factor. Whole components satisfy the common-input identity `C(u OR a_i)=u OR C(a_i)`, but outside masks must be charged together.

A single-mask special case is tractable: suppose a component output `u OR f_H` is cleaned by `OR(S)` and all `H` edges are preserved. Then `S` covers `H`, and correctness adds edges from `u` to every vertex of `S`. Triangle freedom makes `S` independent; four-cycle freedom forces every outside vertex to have at most one neighbor in `S`. Consequently `H` is a star forest. This does not handle multiple nonlinear masks.

## Checked common-input component extraction

Frozen fragments in the scratch `global/` directory, to be appended in order inside the existing `cross` namespace:

1. `Component.lean` (175 lines): a closed AND/OR core commutes with joining every input with a common Boolean value. It constructs the old block with `p` initial OR gates and the new block with `t` boundary OR gates, proves the boundary values equal, and proves exact size difference `p-t`.
2. `ComponentExtras.lean` (55 lines): fan-in-two monotonicity preservation, indexed output equality, and single-output circuit evaluation equality.
3. `Continuation.lean` (76 lines): generic suffix rewiring. Every old-prefix wire read by a suffix gate must map to an existing new-prefix wire with the same value; later suffix wires are shifted automatically. The suffix retains its gate count and gate operations.
4. `ComponentContext.lean` (122 lines): explicit `InterfaceRead` conditions allow consumers to read original base inputs or listed boundary outputs, but not unlisted internal block wires. Under these conditions, the complete old and rewritten circuit functions agree, fan-in two is preserved, and the size difference remains exactly `p-t`.
5. `MinimalBoundary.lean` (51 lines): a minimum circuit containing such a component must have `p <= t`; if additionally `t <= p`, extraction preserves minimality and exact size.

All five fragments compiled together in `MinimalBoundaryIntegrated.lean`; the final build log is empty. The only dependencies outside these fragments are the shared `cross.wf`, `wf_len`, and `wf_keep` foundations.

Scope is explicit: the base input list is `[u] ++ a`, where `a` contains the `p` factor inputs. This is not yet an embedding into arbitrary additional ambient input wires. An ambient extension would retain an arbitrary prefix containing `u` and change offsets from `1` to the prefix length, or instantiate the general prefix-renaming lemma.

## Remaining boundary-count issue

Triangle/four-cycle freedom plus correct output alone cannot imply `t <= p`. For example, the ten common-u factors corresponding to Petersen vertices can feed fifteen boundary ANDs corresponding to Petersen edges; filtering each boundary with its direct edge term and OR-ing gives the Petersen edge function with `u` isolated. All fifteen boundaries are used, but the circuit is redundant. Minimum/irredundancy must therefore be essential in any boundary-count theorem.

Potential measure for a successful equal-size extraction: each core signal changes from `u OR v` to `v`, so core AND functions decrease pointwise. Added and removed boundary gates are ORs, and all suffix gate values remain unchanged. Hence AND gates cannot acquire new false-positive inputs. Every core AND loses the singleton-u input. This suggests minimizing circuit size and then total AND truth on nonedge/singleton pairs. The existence of an extractable region with `t <= p` is still unproved.

## Independent star-cover review and conditional target result

Reviewed `StarCoverPrototype.lean` independently: its constructor assigns each graph edge to one covering endpoint, builds each resulting star, and ORs the stars. Every AND directly reads its center input, giving `HasStarProfile`. Its exact size is `|E| + |M| - 1` for the active centers `M`, so it is bounded by `|E| + |K| - 1` for the given cover. It makes no minimum claim. Frozen hash: `315c489b288898f1e918c65bed308905afa43225f729724df1fb45162c7d4c56`.

`OneJunkStar.lean` (38 lines) combines that witness with `OneJunkAll.lean`: a least AO circuit in top form with one dirty AND can be replaced by a no-larger star-profile circuit. An additional public minimum premise gives the posted existential conclusion conditionally.

`AtMostOneJunkStar.lean` removes the top-form and nonempty-graph premises using `OneJunkTopFree.lean`, and handles zero dirty ANDs directly. Its final theorem proves the posted existential conclusion provided there is a public minimum circuit `C` that is `IsAO2` and satisfies `(junk G C).card <= 1`. The case of two or more dirty AND gates remains unsolved, so this is not a proof of L-meta-2448.

The combined file `AtMostOneJunkStarIntegrated2.lean` compiled successfully. Its only warnings are the two inherited unused variables in `OneJunkTopFree`. These prototypes use outside imports and are checked scratch results, not submission-format files.
