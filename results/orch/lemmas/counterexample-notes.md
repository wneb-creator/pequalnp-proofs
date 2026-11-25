# Counterexample search for L-meta-4675

The actual model is consistent with the intended bound: `IsAO2` imposes binary AND/OR and earlier-wire reads. Missing output wires yield false, which only computes the empty graph and satisfies the conclusion with an empty cover.

`tCount=0` is purely syntactic. AND gates reset OR reach. Thus a circuit can compute copies `a AND a` and `b AND b`, then OR these copies, and have zero two-colour OR gates despite its output having singleton support in both colours. Any proof treating T=0 as a semantic singleton-support restriction is invalid. The two copy gates are charged in the size, so this alone does not refute the claimed bound.

## Exhaustive finite computation (not Lean verification)

The C++ program `counterexample-small.cpp` enumerates binary AO circuits as truth-table functions paired with their OR-reach colour (0, point, or line); OR of opposite nonzero colours is forbidden. AND resets colour to zero. Repetitions are permitted. A new signal is pruned if an already available signal has exactly the same truth table and a subset of its OR-reach colours: replacing the new signal by the existing one preserves functionality and cannot create mixed OR reach, while decreasing size. This includes colour-erasing idempotent AND gates when their input colour is nonzero.

All nonempty C4-free bipartite edge functions for each input split are generated independently, and their exact minimum vertex-cover size is found by exhaustive vertex-subset enumeration. Every generated gate output is compared to these targets and the asserted lower bound. The empty graph always satisfies the theorem with the empty cover. Input-wire outputs cannot compute a nonempty graph edge function.

- p=2, l=3, through 4 gates: 53 targets; depth counts 1, 19, 469, 14551, 554957. No counterexample. Every target bound is at most 5, so all possible violating sizes are covered for this split.
- p=3, l=3, through 5 gates: 333 targets; depth counts 1, 27, 930, 39714, 2060178, 127767588. No counterexample.
- p=3, l=3, through 7 gates, using symmetry/state memoization: 333 targets; depth counts 1, 27, 138, 1452, 17714, 1091872, 79477938, 6754248074. No counterexample. This covers all potentially violating circuit sizes for the split.
- p=2, l=4, through 5 gates: 188 targets; no counterexample. Maximum asserted lower bound is six, so all potentially violating sizes are covered.
- p=1, l=5, through 4 gates: 31 targets; no counterexample. Maximum asserted lower bound is five, so all potentially violating sizes are covered.

Together, these tests exclude counterexamples with at most six inputs computationally. Exchanging the bipartition covers the reversed splits; adding unused inputs embeds smaller cases. This is evidence only, not a Lean proof.

An additional instrumented search through six gates for p=3,l=3 found no violation of either proposed separate inequality `OR_count >= |E|-1` or `AND_count >= tau`. The memoization key includes OR count so that the separate-count check preserves both counts. These separate inequalities remain unproved in general.

The extended version canonicalizes the unordered available non-input signal set under all permutations within each bipartition and, when the two parts have equal size, exchange of the two parts. It memoizes these canonical states through depth 3. This is sound because the target set contains every graph on the chosen labelled split and is invariant under all these permutations. All continued searches retain the raw actual gate sequence for producing a witness.

The first nonforest obstruction on a 3+3 split is C6, with six edges, cover number three and asserted gate lower bound eight. A search through seven gates covers every potential counterexample on that split.

## Fano incidence heuristic search

`counterexample-fano.cpp` tests 26-gate circuits against the Heawood/Fano incidence graph (21 edges, vertex cover number seven, asserted lower bound 27). Because every candidate is monotone, exact semantic equality is determined by the 21 positive edge-pair assignments and the 37 maximal-independent-set negative assignments. These 58 cases fit in one 64-bit word. Every OR gate is also checked for mixed OR reach.

The search begins with 27-gate star-cover circuits and removes one gate, then uses neutral-drift local mutations. A zero-score witness would prove the equality on all assignments, but absence of a zero-score witness has no exhaustive significance.

The initial five-minute run completed 3,017,100,000 mutations across 30,171 restarts without a witness; the best candidate missed one required edge.

The improved `counterexample-fano-diverse.cpp` explores two settings: 26 total gates, and 40 total gates with at most 19 active OR gates (testing the proposed separate OR lower bound). It varies positive/negative mismatch weights, permits rare uphill moves, optionally rewards fewer active gates, and checks OR reach only on the output cone. Removing inactive gates preserves semantics and the OR-reach condition on the cone, so a witness would be pruned before Lean certification.

Both ten-minute runs finished without witnesses: 2,790,600,000 mutations / 27,906 restarts for 26 total gates, and 1,949,000,000 mutations / 19,490 restarts for the 19-active-OR/40-total-gate setting. Best mismatch count remained one. These failed heuristic searches establish no lower bound.

`counterexample-graphs.cpp` extends the same exact-signature heuristic to 55 C4-free bipartite graphs: even cycles on 6 through 12 vertices, the three-length-three-path theta graph, the subdivision of K4 and of K4 minus one edge, and 48 random maximal C4-free graphs on 5+5, 5+6, and 6+6 inputs. Each graph's exact vertex-cover number and maximal independent sets are computed by exhaustive subset enumeration before synthesis. The circuit budget is one below |E|+tau-1. Initial circuits are built from minimum vertex covers and lose one leaf OR gate. A failed heuristic search again establishes no theorem.

The ten-minute 55-graph run completed 3,550,000,000 mutations across 35,500 restarts without a witness.

The algebraic agent located an accepted Fano bound of at least seven AND gates (`L_meta_634`), so any 26-gate Fano counterexample must use at most 19 OR gates. The general analogous AND lower bound was only located for vertex-cover number at most five (`L_meta_2399`). This is evidence that deriving separate gate-count bounds is substantive.

## Independent validation and SMT

`counterexample-crosscheck.py` independently uses sets of assignments, explicit OR-reach input sets, and no semantic or state pruning. For p=2,l=2 through four gates it visits 747,439 raw states and recovers the exact asserted minimum for all 14 nonempty C4-free graphs.

`counterexample-certificate.py` independently derives the Fano graph's 37 maximal independent sets by closure on the point side. It checks, over all 16,384 assignments, that an assignment is independent exactly when it is contained in one of these sets. It also verifies the C4-free property, exact minimum cover size seven, and the known 27-gate star circuit's full truth table and OR reach. It can check any generated candidate and prunes unused gates for size and colour checks.

The installed system library `/usr/lib/x86_64-linux-gnu/libz3.so.4` provides Z3 4.13.3 through ctypes, without installing packages. `counterexample-fano-smt.py` encodes 26 binary AO gates, earlier-wire selectors, exact 58-case semantics, T=0, and at most 19 OR gates. The known 27-gate star circuit validates as SAT when pinned into the same encoding. A preliminary version had forward-declaration errors in a gate-use symmetry constraint and its solver result was discarded. The corrected version declares every selector before use. Solver conclusions are not Lean proofs; only an independently checked witness could advance the refutation.

The corrected bit-vector-selector encoding returned UNKNOWN after its 300-second timeout. No model or lower bound resulted.

`counterexample-fano-onehot.py` uses a different encoding: one-hot wire selectors, native cardinality constraints, and a requirement that at least one AND gate is true on a maximal independent set. The latter focuses on dirty-AND circuits, because the known pair-clean theorem excludes a counterexample with all AND gates pair-clean. Its known 27-gate validation also returns SAT without errors. The search timeout is 600 seconds.

The one-hot Fano search returned UNKNOWN after 600.13 seconds. No witness or lower bound resulted. All counterexample-agent long-running jobs had completed by 2026-11-25 17:43 UTC.

Independent review of the structural agent's `structural-cycle-smt.py` found its C6 target, full 64-assignment truth table, pair-dirty mask, read-back conditions, and colour recursion consistent. Excluding unused gates and idempotent OR gates is sound for minimum eight-gate circuits because either would permit a smaller circuit, which the separate exhaustive enumeration excluded. Its reported UNSAT result remains computational evidence only.

Independent review of `semantic-orfree.py` also found the flattening sound: arbitrary AND regions become nonempty conjunctions of inputs and earlier OR outputs; the output is another such conjunction. Exact k OR nodes represent circuits with at most k ORs by unused or idempotent OR padding. Thus its C6 k=4 UNSAT tests unbounded-AND OR complexity, not merely total circuit size. Its known k=5 witness replays on all 64 assignments.

## Residual inequalities

The algebraic agent proposed `|U| + tau(U) <= 2*c + j + o`, with stronger pieces `|U| <= c+o` and `tau(U) <= c+j`. Here U is the target edge set not represented by cross-pairs of raw OR-reach sides of clean ANDs, c counts clean ANDs with an empty side, j counts dirty ANDs, and o counts ALL dirty ORs outside lambda. OR gates hidden behind a dirty AND still count in o if absent from lambda. An initially reported counterexample from another agent was corrected after this last distinction; it satisfied equality.

`counterexample-residual.py` checked all circuits of size |E|+tau(E)-1 on the 2+2 split: 60 bound-sized histories, 36 TopForm, all with U=c=j=o=0. `counterexample-residual.cpp` then checked raw histories through five gates, without state memoization or semantic pruning, including nonminimum circuits. Across 48,250,603 histories it found 6,857,860 TopForm graph outputs, of which 67,652 have every gate active; all three residual inequalities held. Truth tables determine clean/dirty gates exactly, while OR reach, OR closure, and full ancestry are tracked from the actual wiring.

The raw residual check on 2+3 inputs through five gates also passed all three inequalities: 209,272,048 histories, 30,435,054 TopForm graph outputs, and 167,730 all-active TopForm outputs. Maximum |U| was three, including in all-active cases; these checks are not vacuous. No leastness assumption was imposed for this test.

## Large-lambda follow-up (2026-11-25)

`largeLam` is `lam` filtered to gates whose raw OR-reach contains at least two inputs. Its residual budget is at least the original lambda budget. The earlier successful original-lambda checks therefore imply the large-lambda inequality on those same circuits.

The independently evaluated eight-gate double-star circuit has |U|=3, tau(U)=2, c=0, j=1, o=4. It DOES refute the separate proposed bound tau(U)<=c+j outside a minimum-circuit hypothesis. It does NOT refute the sum bound: both sides are five. This corrects any inference from the earlier small successful separate-bound tests to unrestricted nonminimum circuits.

`counterexample-large-lam.cpp` retains the complete raw wiring history and does not memoize or prune semantic duplicates. On the 3+3 split through five gates it completed 696,220,624 raw histories in 24.0049 seconds. There were 113,455,197 TopForm graph-output hits, including 379,755 with every gate in the output cone. All three large-lambda residual inequalities passed. Among the all-active hits, 49,707 were within two gates of |E|+tau(E)-1, and the smallest residual-sum slack was zero. This is an exhaustive finite computational check only, not a Lean proof.

`counterexample-large-lam-smt.py` encodes an unknown nonempty C4-free graph on 3+3 vertices, all 64 input assignments, T=0, TopForm, all gates in the output cone, and a circuit size at most two above |E|+tau(E)-1. It computes raw OR reach and lambda from actual wires, and computes tau by testing every vertex subset of size zero, one, and two (the point side always gives a cover of size three). A pinned eight-gate double-star validates SAT for the separate-AND-bound violation, recovering the exact counts above. Pinned SUM violation returned UNSAT because the same counts give equality. The unpinned eight-gate SUM search is bounded by a 300-second solver timeout; its eventual status is recorded in the manifest, never inferred from elapsed time.

The independent reviewer approved `counterexample-large-lam-dag.cpp` for exact prefix-DAG symmetry: each key stores every gate operation and operand, retains duplicate gate instances, renumbers topological layers, and minimizes over the 72 valid input permutations. It does not merge equal truth functions. The 3+3 through-six-gate run completed in 44.1316 seconds. Its visited-state counts were 1, 33, 229, 4662, 121215, 11662683, 1364456661 (total 1376245484). These are representative-prefix visits, not raw histories. There were 203323318 TopForm graph hits, 458592 structural output-cone-active hits, and 11279 such active hits within two gates of the cover reference bound. All three largeLam residual inequalities passed; maximum |U| was three and minimum sum slack zero.

The unpinned eight-gate direct SUM residual SMT search returned UNKNOWN after its 300-second limit (elapsed 300.230553444 seconds). This is inconclusive: no witness, no UNSAT result, and no general residual bound. All counterexample-agent computational runs in the manifest had terminated by 2026-11-25 18:08:28 UTC.
