# L-meta-4675 exploratory search report

These computations are evidence only. They are not Lean proofs, and no solver result is used as an axiom or substituted for the posted statement.

## Exhaustive fixed-gate search

`counterexample-search.cpp` represents each wire by its full Boolean truth table and a two-bit OR-reach colour set. AND gates reset the colour set to empty; OR gates union their operands' colours and are forbidden when both colours occur. Thus the search retains idempotent AND input buffers, which change OR reach without changing the function.

The search deletes duplicate `(truth table, colour)` signals and orders adjacent independent gates by that signal pair. These pruning rules are intended to preserve at least one representation of every minimal circuit: duplicate signals can be replaced by the earlier signal, and a lexicographically least topological ordering has no adjacent independent inversion. Operand order is canonical because AND and OR commute.

Every nonempty C4-free edge set for the dimensions below is tested against every generated signal. Vertex-cover size is computed by enumerating all subsets of the input vertices. The bound is `edges + tau - 1`.

| Dimensions | Nonempty C4-free edge sets | Gates searched | Result |
| --- | ---: | ---: | --- |
| 2 x 2 | 14 | through 3 | no violation |
| 2 x 3 | 53 | through 4 | no violation |
| 2 x 4 | 188 | through 5 | no violation |
| 3 x 3 | 333 | through 7 | no violation |

Each range covers all gate counts below the claimed bound for those dimensions. The final 3x3 run enumerated 9,281,809,818 canonical depth-seven extensions and took 299 seconds. The counts are generated extensions, not distinct circuit equivalence classes. Degenerate dimensions/empty graphs are trivial, and one-side-size-one graphs have the usual disjunction support lower bound. Together these checks cover all bipartite graphs on at most six input variables.

`split-search.cpp` separately tests AND count < tau or OR count < edges-1. `dirty-search.cpp` looks for an optimal-size circuit containing an AND gate whose function does not imply the output. Both tested all 2x3 targets through five gates; neither found a witness.

## Free-gate SMT encodings

`freegate-synth.py` calls the already-installed native `libz3.so.4` through ctypes. No SAT package was installed or downloaded.

The input assignments retained are every positive edge pair and every maximal independent set as a negative assignment. This is exact for a monotone output: positive edge tests imply all true assignments are accepted, and maximal-independent negatives imply all false assignments are rejected. In particular, the encoding does not merely test two-hot assignments; it excludes false positives involving four or more active inputs.

* Counting AND gates with arbitrary OR gates: each AND operand is the OR of a nonempty subset of raw inputs and earlier AND outputs. This flattens the entire OR cone. Without `--mixed`, the raw inputs selected by each operand have at most one colour, exactly the tCount=0 requirement. Every prior AND output has empty OR reach. Final output is the OR of a nonempty subset of AND outputs; a raw input at final OR reach would violate the required rejection of singleton assignments. Repeated functions are allowed, including AND input buffers and padding gates.
* Counting OR gates with arbitrary AND gates: use the dual flattening, so each OR operand is the AND of a nonempty subset of inputs and prior OR outputs, and the final output is a nonempty AND. This model imposes no colour restriction. Any witness can be converted to tCount=0 by inserting an idempotent AND buffer for every raw input; this changes the AND count but preserves the OR count.
* With `--mixed`, AND-count searches drop the colour constraint and therefore test a stronger unrestricted-OR lower bound.

All free-gate searches permit repeated signals, so a circuit with fewer counted gates can be padded and is included in a query with more counted gates.

`batch-split.py` performed 85 isomorphism-reduced tests covering all C4-free graphs of dimensions 2x3, 2x4, and 3x3, querying AND < tau and OR < edges-1. Every query returned UNSAT. Isomorphism representatives and exact edge sets/gate limits are in `batch-split-results.json`.

Additional completed results (see individual complete logs):

* C6, <=2 ANDs with arbitrary mixed-colour ORs: UNSAT.
* C6, <=4 ORs with arbitrary ANDs: UNSAT.
* Theta graph with three internally disjoint paths of length three (4x4, nine edges, tau four), <=3 ANDs with arbitrary ORs: UNSAT, both pure-colour and mixed-colour variants.
* Incidence subdivision of K4 (4x6, twelve edges, tau four), <=3 ANDs with pure-colour ORs: UNSAT.
* Theta graph <=7 ORs: UNKNOWN at both 120 and 600 seconds.
* Fano incidence (7x7, twenty-one edges, tau seven), <=6 ANDs with pure-colour ORs: UNSAT in the longer run, after 329.6 seconds. An existing Lean theorem in L_meta_634.lean already proves the stronger unrestricted-OR bound.

UNKNOWN is a timeout, not an UNSAT result. All finite solver results remain exploratory evidence. Independent encoding reviews are archived alongside this report.

## Fixed-size SMT caveat and exact archive

`synth.py` uses duplicate-signal and liveness pruning. Its UNSAT results therefore concern irredundant circuits of the queried exact size; they rule out smaller circuits only when a separate optimum/lower-bound argument is already available. The C6 eight-gate dirty/AND/OR queries are supplementary to the complete bounded C++ run and the free-gate split queries, not general stand-alone lower bounds. The theta eleven-gate query timed out.

The archive includes the exact generated SMT-LIB query and complete stdout for each SMT run, as well as source and summary logs. This preserves the actual query even when the generator evolves. Each file has a SHA256 in `search-archive-manifest.json`.

## Later results and refinements (17:41 UTC)

The independent review is in SEARCH_REVIEW.md; the OR-footprint refinement is reviewed in OR_PRUNING_REVIEW.md. No flaw was found in the primary exhaustive/free-gate scopes. The single-edge scope guard requested by the reviewer is implemented and tested.

The longer Fano AND<=6 query returned UNSAT after329.6 seconds; another agent identified the corresponding checked bound in existing L_meta_634.lean, so this search was not repeated. Fano OR<=19 and theta OR<=7 both returned UNKNOWN at600 seconds. K4-incidence OR<=10 returned UNKNOWN at120 seconds.

For OR-minimal exact graph circuits, the positive-edge footprints of the operands of each OR are incomparable. Replacing a comparable OR by its dominating child preserves every minimal positive and decreases the full circuit pointwise, hence preserves the graph function while saving an OR. With at least two edges, unused ORs of two edge conjunctions can pad a smaller normalized circuit to the query size. The --prune-or option enforces this independently reviewed invariant. It rejects fewer than two distinct edges. Additional redundant clauses forbid an AND operand from selecting a nonedge pair of raw inputs, because then it would accept no positive edge. An optional canonical-order condition sorts adjacent independent OR nodes by boundary truth vector; equality is allowed. The same topological-order argument as the C++ search applies and was independently reviewed. Refined theta/Fano OR searches remain in progress.

New cleanliness tests with unlimited pure ORs: C6 at its minimum 3 AND gates cannot contain a dirty AND (UNSAT0.11 seconds); theta at its minimum 4 AND gates cannot contain a dirty AND (UNSAT1.04 seconds). Here dirty means true on some maximal-independent negative assignment. The Fano7-AND dirty query ended UNKNOWN at120 seconds.

Direct Fano work uses a validated27-gate canonical star cover (all16,384 assignments tested) and one removable bypass to represent26 counted gates. The radius-three SMT query returned UNKNOWN at60 seconds. Exhaustive radius-two rewriting tested15,389,010 candidates, of which11,902,093 obey tCount=0; no exact26-gate circuit was found. The minimum observed boundary-error count was1. The120 second direct annealer tested1,320,560,000 mutations over 33,014 restarts; no witness. A separate free-AND19-OR annealer tested1,017,360,000 mutations over 25,434 restarts in180 seconds; no witness. A27-gate/tCount0 search for an OR-count split violation (<=19 ORs) also remains available in its separate log. These stochastic searches do not establish lower bounds.

## Independent SAT engine and graph symmetries

Lean's installed toolchain contains CaDiCaL. The conversion script `smt-to-cnf.py` applies Z3 simplify, bit-blast and Tseitin-CNF tactics, asserts that there is exactly one resulting goal, and saves DIMACS with original Boolean selector names and input/output hashes. No solve-eqs tactic is used, to retain selector-model decoding. A CaDiCaL SAT control for C6 was reconstructed and independently checked on all64 Boolean assignments.

The ordered theta query has2214 variables and8369 clauses; ordered Fano has38997 variables and146336 clauses. Both ended UNKNOWN at their explicit600-second wall-clock limits. CaDiCaL writes c UNKNOWN and exits0 on these timeouts; neither is an UNSAT result.

`first-or-orbits.py` adds verified graph automorphisms. It decodes and checks the exact boundary rows from the original SMT constants, verifies every emitted permutation on the full edge set, and enumerates all feasible raw conjunctions for the first OR: a vertex or an edge pair. For theta,12 verified automorphisms reduce118 candidate operand pairs to18 canonical pairs. For Fano,336 verified automorphisms reduce553 pairs to8. The mathematical completeness argument chooses a lexicographically least wire-value sequence over both graph automorphisms and topological orders. Its first OR is orbit-minimal and has no adjacent independent inversion. Two independent agents inspected the argument and current implementation; the complete pipeline review is SAT_PIPELINE_REVIEW.md. The symmetric C6 positive control returned SAT under CaDiCaL; its decoded circuit passed all64 assignments, and a reviewer independently checked all2963 CNF clauses with no failures or unassigned variables. Both symmetric theta/Fano searches ended UNKNOWN at600 seconds. No further lower-bound variants are running.

All finished Z3 Fano/theta OR queries, including the ordered variants, ended UNKNOWN at their limits. A direct theta11-gate annealer tested2,345,080,000 mutations over58,627 restarts in180 seconds with no witness; best boundary error1. A Fano27-gate search for<=19 ORs tested1,148,520,000 mutations over28,713 restarts in180 seconds with no witness. These are bounded heuristic failures, not proofs.

The path a-b-c-d illustrates why cleanliness needs the colour condition: ab OR bc OR cd equals (a OR c) AND (b OR c) AND (b OR d). It uses the minimum2 AND gates but its first AND is dirty and the middle OR mixes colours. The model returns SAT for a minimum2-AND dirty circuit with mixed ORs and UNSAT with tCount=0.

The final K4-incidence14-gate annealer tested2,227,040,000 mutations over55,676 restarts in180 seconds; no witness, best boundary error1. Its canonical15-gate seed was independently evaluated on all1024 assignments. The exhaustive/local/stochastic/SAT work has produced no counterexample to the posted statement and no proof of the general statement.
