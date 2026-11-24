# L-meta-2584 orchestration notes

Held by pilot-39. Root alone manages the lease and submissions.

## Assignment

Four-cycle-free incidence: replace any AO2 circuit by a no-larger read-2 circuit. Exact statement is stored in scratch statement.txt.

## Strategies

- combinatorial_route: graph/star-cover lower bound and existing lemmas.
- circuit_route: size-preserving normalization and explicit construction.
- counterexample_search: edge cases and finite experiments.
- status_review: prior L-meta-1035 and reductions eligibility.
- toolchain_setup: recover absent pinned toolchain and Mathlib cache.


## Counterexample and finite-case route

ReadK uses one jointly bounded proof tree for each prime implicant. It does not mean bounded fanout. IsAO2 requires exactly two earlier wires but permits a missing output. Empty incidence graphs have no prime implicants, so the read-2 condition is vacuous and cause no edge-case obstruction.

A stronger statement saying the original circuit itself must be read-2 is false: compute xy, then AND with x twice; the only tree uses x three times. Replacing by the original one-gate xy circuit resolves this.

Finite experiment (not Lean checked): Exhaustively generated all fan-in-two AND/OR circuits through four gates on 5 inputs, and through five gates on 6 inputs, omitting semantically duplicate wires (eliminable in a minimum circuit). No four-cycle-free bipartite incidence function beats the candidate star-cover cost |E| + tau(G) - 1. This checks all 54 four-cycle-free labeled 2-by-3 graphs and all 189 four-cycle-free labeled 2-by-4 graphs, including empty graphs with cost zero. The six-input run enumerated 174,325,200 final-depth gate sequences.

Source: /tmp/oec/pequalnp-pilot-39/counterexample/exhaust_small.cpp. Complete logs result-2x3.txt and result-2x4.txt in that directory. The bound has not been proved in Lean. A minimum vertex cover supplies a partition into nonempty stars, giving a natural read-1 (hence read-2) circuit with |E| + tau(G) - 1 gates. This suggests separating a circuit lower bound from an elementary star construction, though the lower bound remains the genuine hard part.

## combinatorial_route 2026-11-24T18:01:18.935289+00:00

- ReadK uses joint count vectors, not separate scalar minima. IsAO2 has exactly two backward operands, but permits an absent output (constant false).
- Candidate in scratch combinatorial/Prime.lean: incident pairs are exactly prime implicants; ReadK equivalently checks each incidence pair; C4-free complete bipartite subgraphs have a singleton side. 107 lines, waiting for toolchain.
- Canonical star cover is MetaComplexity.coverCircuitB; size/function proof available for copying from Outside/L_meta_3243.lean, model/structural proof Outside/L_meta_3245.lean. Root and circuit_route notified.
- Full conjecture is stronger than known read2 lower bounds; no existing normalization result found among the ReadK-related files. The lower-bound route would require circuit cost at least star-cover cost; not established.

### circuit_route — 2026-11-24T18:03:38.450119+00:00
Constructed uncompiled FlatRead.lean in /tmp/oec/pequalnp-pilot-39/circuit-route. Generic result: AO2 circuits whose AND operands lie in OR-only wire regions are read-2. Uses checked word semantics from L_meta_2466 plus reverse capped-vector encoding and proof-word length ≤2. Added separated_isReadTwo matching the structural conclusion of L_meta_3245 for coverCircuitB. This can finish read-2 of any canonical star-cover construction. Missing full-gap step remains size-preserving flattening of arbitrary C4-free incidence circuits. No reductions:true flag for current gap; root has sole lease.

### combinatorial_route literature check 2026-11-24T18:04:34.560536+00:00

Read 2026-11-24 via built-in web only: Stasys Jukna, Notes on Boolean Read-k and Multilinear Circuits, https://web.vu.lt/mif/s.jukna/ftp/readk-rev.pdf. Abstract states: “read-2 (∨, ∧) circuits can be exponentially smaller than read-1 (∨, ∧) circuits.” Definition is the same joint monomial degree notion as ReadK. Section 9 treats higher read hierarchy as open. No quadratic or C4-free normalization result found in this text.
Local notes/note-1-edge-function-exact-size.md limits the checked exact |E|+tau−1 theorem to long-thread graphs/forests/cycles; it does not claim all C4-free graphs. Thus generic star-cover-cost lower bound remains a genuine missing argument.
Existing same-size top-form normalization is checked Outside/L_meta_1501.lean (about 1120 lines); communicated to circuit_route. Known normalization stops before resolving junk blocks.

### Extended finite evidence

Exhaustive 2-by-3 search now reached five gates (26,560,320 final-depth sequences), checking all 471 syntactically distinct irredundant circuits at the star-cover optimum across the 54 four-cycle-free graphs. Every such optimal circuit is read-2. This is evidence for the stronger all-minima-read-2 conjecture, not a proof beyond these finite graphs.

Installed a scratch-only standalone Z3 5.3.3 release obtained from GitHub. Exact circuit synthesis for C6 has returned UNSAT at six gates (7.64 seconds) and seven gates (52.93 seconds), and SAT at eight gates (4.25 seconds), with an independently checked truth table/read-1 witness. The search assumes no semantically duplicate wires and all gates live, valid for minimum circuits; it orders adjacent independent gates by truth table to reduce isomorphic orderings. A separate eight-gate search forbidding read-2 on one edge is still running. Source synth_cycle.py and full SMT2/logs under scratch counterexample directory. None of these solver results is Lean checked.
