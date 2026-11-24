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

### C6 all-optima test

Z3 returned UNSAT at C6 size5 (0.99s), size6 (7.64s), size7 (52.93s), SAT at size8 (4.25s), and UNSAT at size8 under the requirement that the distinguished edge has no joint read-2 tree (111.85s). C6 is edge-transitive, so the tested stronger property holds throughout its minimum circuits under this encoding. Fewer than five gates cannot depend on all six input variables. The evidence is computational and not Lean checked.

For larger cycles, synthesis is compressed to minimal-positive inputs (edges) and maximal-negative inputs (maximal independent sets). Those inputs characterize a monotone target: any true input contains an edge, any false input lies inside a maximal independent set. Semantically distinct intermediate wires on the compressed inputs can be required for a minimum circuit, because replacing a duplicate by its earlier representative preserves the compressed output tests and hence, by monotonicity, the entire final function. The circuit itself is evaluated on all assignments to independently verify any SAT model. C8 uses 18 such assignments rather than256.

### circuit_route checked component — 2026-11-24T18:07:13.993006+00:00
CoverRead.lean compiles exit0 with no diagnostics; full logs scratch circuit-route/build-003.stdout and .stderr. 688-line component includes generic flat_isReadTwo, separated_isReadTwo, and canonical_cover_isReadTwo. All statements use only Defs/Mathlib; structural helpers adapted from L_meta_3245 and word semantics from L_meta_2466, under own L_meta_2584 namespace. Root notified immediately for merge/push.

### Lean-checked C6 witness

The explicit eight-gate C6 circuit found by SMT has now compiled in pinned Lean with kernel decide only. Scratch CycleSix.lean defines the cycle incidence relation and circuit, then checks size8, AO2, no4cycle, the exact incidence function on all64 assignments, and the full IsReadK6 circuit2 property. It imports only Mathlib and PEqualNP.Defs and uses namespace PEqualNP.Outside.L_meta_2584.CycleSix. No native evaluation or new axioms. Complete build stdout/stderr are empty and process exit0. This is an existence witness, not the general L-meta-2584 theorem or a Lean lower bound. Root notified for immediate integration/push.

## structural_route 2026-11-24T18:10:14.746961+00:00

- Lean checked `one_junk_isReadTwo`: any TopForm AO2 circuit computing a simple graph edge function and having exactly one dirty AND gate is read-2. No leastness or C4 hypothesis needed.
- Key induction: a wire whose only possible AND ancestor is g has proof words of length one, or length two plus implication g => wire. If both operands of a below-function AND have length-two words, g implies the function, contradicting dirtiness. Thus all output words have at most three leaves. Singleton rejection bounds each variable multiplicity by two.
- Standalone candidate scratch structural/OneJunk.lean (compilation build-005, exit 0; no output). Integration fragment structural/one-junk-fragment.txt uses stable circuit_route FlatRead word machinery and its short_isReadTwo lemma.
- This does not prove general normalization: circuits with two or more dirty AND gates remain open.
