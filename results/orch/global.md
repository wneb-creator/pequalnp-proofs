# Global normal-form strategy for L-meta-2448

## Checked partial

`owns_bipartite_of_singleton_silent` proves the following, for any monotone fan-in-two circuit and any gate `j`:

If gate `j` is false on every singleton input, then there exists a Boolean coloring of the input vertices such that the endpoints of every pair owned by gate `j` have different colors.

This needs no graph or girth hypotheses. It generalizes the five-cycle-specific singleton obstruction used in `R_meta_2448_17`: any odd cycle in an ownership graph forces the gate to be true on some singleton.

The first standalone file, `/tmp/oec/pequalnp-pilot-75/global/OwnershipBipartite.lean`, compiled successfully with the pinned Lean version. Its first 317 lines adapt checked wire/cone/OR-reach foundations from `L_meta_1762`; the final lemma is new. A shorter variant is being checked against the structural strategy's shared foundations.

## Proof idea

For each input of an owning AND gate, the no-earlier-AND condition in `Owns` forces its truth on an owned pair to arise from an OR-only path from one endpoint. A gate that is silent on every singleton must have two inputs. Color a vertex by whether it makes the first input true. No vertex can make both inputs true. Each owned pair must make both inputs true, so its two vertices have opposite colors.

## Global argument status

The difficult step remains replacing gates that are true on nonedges or singletons without increasing circuit size. Local distributivity can extract a singleton from `(u OR A) AND (u OR B)`, but shared input subcircuits can make this increase size elsewhere. Nothing here proves that a minimum circuit is singleton-silent, pair-sound, or has a star profile.

The repository's note on exact edge-function size only supports general lower bounds for forests, cycles, and long-thread classes. Its cited single-level conjecture counterexamples are saturated graph extensions with cliques within both bipartition sides, so those constructions do not satisfy this task's triangle/C4 exclusions.
