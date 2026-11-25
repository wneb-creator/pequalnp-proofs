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
