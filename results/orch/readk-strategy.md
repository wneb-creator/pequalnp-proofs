# ReadK strategy for L-meta-2583

## Semantics and route

`IsReadK n C 1` is not global read-once. It asks, separately for every prime implicant, for one proof tree in which each variable is read at most once. For incidence functions the prime implicants are incident point-line pairs. The scalar `eachReadsAtMost` recursion is weaker and cannot be substituted.

`IsAO2` requires every gate to be AND or OR, have exactly two inputs, and read backward wires. There are no free constant gates.

A circuit for a pair can fail read-1 due to redundant filtering: `(x AND y) AND (x OR y)`. Thus taking D = C is invalid without further reasoning.

The accepted construction in `L_meta_7684` yields a read-1 AO2 circuit from any bipartite vertex cover with at most |E| + |A| + |B| - 1 gates. `L_meta_4897` and `L_meta_7639` give matching lower bounds only when the original circuit is already read-1. The target is therefore a genuine normalization/lower-bound assertion.

## Prepared artifact

`results/orch/lemmas/readk_star.lean` contains the inlined L_meta_7684 construction renamed to the target namespace, then helpers:

- `incidence_readOne_upper`: size at most |E| + N - 1 by covering with every point;
- `incidence_edge_card`: uniform line cardinality implies |E| = N*(q+1);
- `plane_readOne_upper`: size at most N*(q+2)-1.

The file imports only Mathlib and PEqualNP.Defs. All declarations sit within PEqualNP.Outside.L_meta_2583 and no final named target theorem is claimed. Awaiting initial Mathlib cache completion before first compile.

## Other relevant library results

- L_meta_8933 proves exact cover charging if no dirty AND accepts two distinct nonread1 edges.
- L_meta_7241 proves exact cover charging if every AND rejects every nonedge pair.
- L_meta_3706 proves a relaxed bound with a read-twice-edge error term.
- The repository note `notes/note-1-edge-function-exact-size.md` only claims exact size on long-thread/forest/cycle graphs, and separates monotone formulas and single-level circuits from unrestricted circuits. No easy normalization theorem emerged.

Full discovered ReadK file inventory and extracted theorem statements are in `/tmp/oec/pequalnp-pilot-143/readk-files.txt` and `readk-theorems.txt`.

## Validation

2026-11-25T14:59:21.440755+00:00: `readk_card.lean` compiled cleanly via `lake env lean`; exit 0, stdout and stderr empty. Full star construction still waits for project dependency build.

2026-11-25T15:01:48.889029+00:00: `readk_semantics.lean` compiled cleanly, proving exact characterization of prime implicants as incident point-line pairs. No plane axioms or circuit structure needed, only exact function correctness.

2026-11-25T15:02:02.350511+00:00: `readk_criterion.lean` compiled cleanly, exit 0 and empty outputs. It subsumes semantics and proves IsReadK equivalence to per-incident-pair readsAtMost checks, for every k.

## Local elimination follow-up

Explored15:04UTC until root STOP15:07UTC. No new full proof.

The L_meta_4849 counterexample graph contains an odd5-cycle, so it does not refute bipartite normalization. Its supplied minimum11-gate circuit has a dirty AND but can be manually rewritten to a same-size star circuit; therefore it refutes universal structural cleanliness rather than existence of a clean optimum.

Exploratory SAT in `readk_cycle_cnf.py` checks C6 on all64assignments, with read1 vector tracking for a distinguished edge. At8gates, forcing that edge notread1 returned UNSAT (51.46s,830106conflicts). At9gates, SAT returned a circuit; a separate direct Python evaluation verified all64function values and its capped readvectors. This is computational evidence only, not a Lean certificate. All solver outputs preserved in scratch; no solver remains running after root STOP.

The9-gate witness: AND(0,4), OR(5,6), OR(0,1), AND(1,3), OR(3,4), AND(2,10), OR(9,11), AND(7,8), OR(12,13), output14. Pair(0,4) has only countvector(2,1); the other5edges have(1,1). Thus one extra gate suffices for a redundant reread.
