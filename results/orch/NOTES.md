# L-meta-5282 orchestration notes

Root holds the only lease. Assigned 2026-11-24T21:49:44.996127+00:00

Exact statement and desk response are in /tmp/oec/pequalnp-pilot-43/.

Goal: minimum-size monotone fan-in-two circuit computing a triangle-free, square-free graph edge function, with each AND gate false on empty/singleton inputs. Reductions permitted after at least 20 minutes real work.

Agents append discoveries under own headings. Never call desk, commit or push; root handles these. Scratch Lean files belong in results/orch/lemmas; final proof uses only the assigned file.

## Counterexample agent — finite checks

Exact exhaustive breadth-first search over available truth-table sets found equal unrestricted and singleton-safe monotone circuit minima for every triangle-free, square-free labelled graph on 0 through 4 vertices. Each minimal circuit may be assumed not to recompute an already available function, and unary/copy gates removed; false is available for free by out-of-range wire and true costs one empty AND gate. Safe mode disallows every AND output true on empty or singleton inputs. Full script/log/data: `/tmp/oec/pequalnp-pilot-43/small_circuit_search.py`, `.log`, `.json`. This is a computational check, not Lean evidence.

Read parent reductions `R_meta_1904_493.lean` (source of this exact step) and `R_meta_1904_137.lean` (prior normalization/budget/builder split). No immediate definitional counterexample: actual input length determines gate outputs consistently. Constants and unary gates are permitted but removable in a minimum nonconstant circuit.

### Counterexample agent — five-vertex forests

All 291 labelled forests on 5 vertices also have equal unrestricted and singleton-safe minima, by full exact circuit-state BFS through 5 gates. Unrestricted depth-5 state count 958,669; safe 864,994. Script and full output are `forest5_search.py`, `.log`, `.json` in scratch. C5 is the only remaining triangle-/square-free graph type on 5 vertices, up to relabelling. A 7-gate safe C5 realization: OR(1,4), AND(0,5), OR(1,3), AND(2,7), AND(3,4), OR(6,8), OR(10,9), output wire 11. All three AND gates reject every singleton and empty input.

### Counterexample agent — all five-vertex graphs verified

C5 exact unrestricted BFS, quotienting states by its 10 dihedral automorphisms, found no circuit through 6 gates (depth-6 states: 1,423,242; truth-table functions encountered: 2,189). The 7-gate safe witness above was verified independently on all 32 assignments. Thus every triangle-free, square-free labelled graph on 0 through 5 vertices satisfies the target normalization numerically: 352 graph instances total (49 for n≤4, 291 five-vertex forests, 12 labelled five-cycles). This is strong finite-case evidence, not a Lean proof or a result for n≥6. C++ search: `cycle5_search.cpp`; full output `cycle5_search.log` under scratch.

## lean_setup

The warm Lean environment was absent. Installed official Lean v4.36.0 binary release under `/tmp/oec/pequalnp-pilot-43/lean-4.36.0-linux`. Use its `bin` directory first in PATH. Fetched pinned packages via Lake (no update) and downloaded all 2480 cached Mathlib dependencies of `PEqualNP.Defs`. Full cache output is `/tmp/oec/pequalnp-pilot-43/cache-get.log`; cache command succeeded. Avoid broad `import Mathlib`: only about 1.4 GB disk remains. PEqualNP.Defs build is in progress, logging to `/tmp/oec/pequalnp-pilot-43/defs-build.log`.

## Reduction design agent

Candidate cuts considered: (a) global vertex-cover lower bound plus clean star construction, but lower-bound child may be stronger than assigned normal form; (b) top-form purification then graph-specific singleton redundancy, needing general Monotone2-to-AO2 bridge; (c) semantic erasure certificate plus generic gate-erasure algebra, stronger all-minima-clean claim undergoing finite tests. Naive bypass of a singleton-visible AND to either operand is false even for a singly read gate; matching example supplied by counterexample agent. Generic `erase_mono` and `erase_size` proofs are drafted in `results/orch/lemmas/ReductionDesign.lean`, pending cache.

Lean setup complete: `lake build PEqualNP.Defs` exited 0. All agents may now check scratch proofs. No tracked build config changes.

## Existence strategy

- `results/orch/lemmas/Existence.lean` compiles with only `import PEqualNP.Defs`.
- `edge_circuit_exists`: every finite graph edge function has a monotone fan-in-two circuit, built from finite OR of its edge ANDs.
- `edge_minimum_exists`: Nat.find chooses a globally minimum-size such circuit.
- `safe_edge_circuit_exists`: explicit edge-DNF circuit has every AND reading an actual graph edge, hence no AND true on an input with at most one true variable. No triangle/square-free assumptions needed.
- `minimum_good_of_descent`: a local repair preserving function, never increasing size, and strictly decreasing any natural measure when Good fails yields a globally minimum Good circuit, by lexicographically minimizing size and measure.
- Full proof of global safe minimality still requires a genuine nonincreasing-size repair, or matching lower/upper bounds. Safe DNF construction alone does not prove optimality.
- Validation: `PATH="/tmp/oec/pequalnp-pilot-43/lean-4.36.0-linux/bin:$PATH" lake env lean ../results/orch/lemmas/Existence.lean` exited 0; full stdout/stderr saved at `/tmp/oec/pequalnp-pilot-43/existence-check.log` (empty).

### Counterexample agent — stronger claim and surgery limitations

Exact path-sensitive enumeration also found no bad AND in **any** minimum circuit for every eligible graph with n≤4 or every five-vertex forest (not merely existence of a good optimum). State search tracks whether any realization includes a visible AND; complete output `optimal_bad_search.log`.

Naive local bypass is false outside minimum circuits, even with one reader and a forest target. Example: `d ∧ ((a∨b)∧(a∨c)) ∨ bc = ad∨bc`; replacing the middle AND by either operand introduces bd or cd, while replacing it by a works. Stronger example: let A=(a∨c)∨b, B=(b∨d)∨a with no earlier a∨b wire, h=A∧B, and output e∧h∨cd = ae∨be∨cd. No earlier wire may replace h correctly; a new OR(a,b) gate can. Any bypass-only hypothesis needs minimum/stronger structural assumptions.

C5 path-sensitive search is now complete: no optimum seven-gate circuit has a visible AND. Depth-6 frontier has 1,423,242 symmetry classes, 172,305 admitting a bad realization; no seven-gate extension computes C5 while retaining badness. Therefore the stronger EVERY-minimum-circuit claim survives all 352 labelled graphs on 0–5 vertices. Full source/log: `cycle5_bad_search.cpp`, `cycle5_bad_search.log`.

### Checked generic erasure components

`ReductionDesign.lean` compiles: deleting an existing gate lowers size by exactly one and preserves Monotone2. `CopyErasure.lean` compiles without diagnostics: if gate k computes exactly an earlier wire p<n+k on all n-inputs, CircuitMoves.eraseGate n C k p preserves output. No ReadsBack premise is needed because this definition leaves the prefix untouched. Generic redundant/comparable-operand erasure can therefore be supplied as an actual proof in a reduction, not left conjectural. Files import only PEqualNP.Defs.

Finite agent reports every minimum circuit is clean on all 352 labelled eligible graphs through five vertices. Stronger all-minima-clean conjecture remains unrefuted there. Still avoid arbitrary-circuit deletion hypotheses: forest example e*[(a∨b∨c)∧(a∨b∨d)]∨cd = ae∨be∨cd can need a new OR(a,b) wire; neither operand nor any existing earlier wire is a valid replacement when a∨b was never built.

## Normalization strategy

- 2026-11-24T21:57:27.656649+00:00: `Normalization.lean` checked: light-set/invisibility equivalence, graph false on light inputs, full assigned conclusion for edgeless graphs.
- `StarUpper.lean` checked: every nonempty simple graph G with vertex cover T has an AND/OR fan-in-two circuit with size + 1 ≤ |E(G)| + |T|, all AND gates invisible on light inputs. Proof adapts in-repo EdgeUpperMono with strengthened Bld invariant. No triangle/C4 assumption. Convenience clean_cover lemma converts to posted Monotone2 and set-input form.
- Full singleton normalization remains open. A local visible AND such as (x OR a) AND (x OR b) cannot simply be replaced by one child; shared children require global absorption.
- Existing R_meta_1904_137 reduction assumes essentially our normalization plus a clean-circuit budget plus star construction, so replacing our step with entire total lower bound risks circular decomposition. Better proposed split: AND count bounds vertex cover; OR count + 1 bounds edge count; use proved construction. Finite checks pending counterexample agent.

## Counterexample agent — quantitative reduction checks

Proposed split: (A) every fan-in-two monotone circuit for a triangle-/square-free graph has at least the minimum vertex-cover number of AND gates; (B) it has at least |E|−1 OR gates. Both survive exact searches permitting **arbitrarily many gates of the other operation**.

- A verified for all 3,423 nonempty eligible labelled graphs on six vertices; maximum minimum-cover size is 3. Exact free-OR closure enumeration through two AND gates checked 8,937,420 output candidates from 1,416 possible first-AND functions. Smaller vertex counts embed by isolated vertices, so this covers n≤6.
- B verified for all 280 eligible five-vertex forests with at least two edges. Under duality this is free-OR enumeration through two AND gates against the dual edge functions. 503,084 candidates; 318 first functions. Cases with zero or one edge are immediate.
- B verified also for C5: no circuit with at most three OR gates can compute its edge function, even permitting arbitrary AND gates. Exact dual free-OR closure search used 285 nontrivial first AND functions, 6,619 two-stage states modulo D5, and 4,674,402 final operand-pair tests. Thus B is verified for all eligible n≤5.

Programs and complete outputs in scratch: `make_count_targets.py`, `make_count_targets.log`, `free_or_count_search.cpp`, `count_A_6.log`, `count_B_5.log`, `cycle5_or_bound.cpp`, `cycle5_or_bound.log`. These are computational checks, not Lean proofs.

Method: between charged AND gates, any number of free OR gates yields exactly OR-closures of inputs and earlier AND outputs. An output for an edge graph cannot include input clauses because it rejects all singleton inputs. For general dual targets, all allowable singleton clauses are combined as the target's linear part. Constant gates can be simplified away without increasing either operation count; the general two-AND enumeration nevertheless includes the empty-AND true constant. D5 canonicalization preserves the C5 target. At the last AND, earlier outputs lying below the target can all be ORed in, reducing verification to whether two available operands intersect to cover the remaining required rows without adding forbidden rows.

Both inequalities are substantive structural claims. B correctly fails on excluded C4: (a∨b)∧(c∨d) has 4 edges and only 2 OR gates. No counterexample found within the stated graph class.

## Count reduction assembly

- `results/orch/lemmas/CountReduction.lean` compiles with exactly one theorem and only `PEqualNP.Defs` imported, 487 lines.
- Frozen SHA-256: `da223f80fc1593b271736b95d5b604987437aa99907931aee9f3133ffeeabd66`.
- Child A: every circuit for a triangle-free/C4-free graph edge function has at least the minimum vertex-cover number of AND gates (stated as existence of a cover within AND count).
- Child B: every such circuit has at least |E|-1 OR gates.
- Proof fully inlines StarUpper builder, minimizes cover cardinality with Nat.find, proves the AND/OR count partition from Monotone2, then uses a safe star-cover circuit of size ≤ |E|+|T|-1. Edgeless case uses a zero-gate circuit.
- Exact posted statement retained unchanged. Two lint warnings only: posted implicit x3 binder and redundant List.countP_cons simp argument. Full stdout/stderr at `/tmp/oec/pequalnp-pilot-43/count-reduction-check.log`.
- Root now owns official file, checker, review, cleanup and push. Do not edit frozen scratch candidate without coordination.

Checker cache prerequisite repaired without altering the checker: `lake exe cache lookup Mathlib` computed pinned root artifact `79da901f0eeeaa4a.ltar`. Downloaded that single official cache artifact from `https://cache.mathlib.org/mathlib4-master/f/79da901f0eeeaa4a.ltar`, extracted with bundled `leantar` at the Mathlib package root, and verified via cache lookup: `git=mathlib4@fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The resulting authentic `Mathlib.olean` is 803632 bytes. Full root Mathlib dependency closure is still intentionally not downloaded (disk constraint).

### Independent adversarial validation of numerical cut

Proposed children: vertex-cover size ≤ number of AND gates, and edge count ≤ number of OR gates + 1, for triangle-/square-free edge functions.

- Independent exhaustive free-OR normal-form enumeration on six inputs found no violating 2-AND circuit or (dually) 2-OR circuit: 3,424 eligible labelled graphs, 1,415 first-AND functions, 4,465,825 second-AND operand pairs, 8,931,650 tested outputs. Source/log: `countbound_exhaust6.cpp`, `.log` in scratch.
- Exact dual synthesis for all six nonisomorphic six-vertex trees excluded circuits with ≤3 OR gates and arbitrarily many ANDs. Each tree has five edges, so this verifies its required OR≥4 lower bound. Each run enumerated 2,959,204 first-two-AND states, then 590–751 million possible final factors. Sources/logs: `or3_target6.cpp`, `or3_path6.log`, `or3_star.log`, `or3_broom42.log`, `or3_double33.log`, `or3_arms311.log`, `or3_arms221.log`.
- Random normalized circuits on 6–9 inputs, 2–9 counted AND gates, arbitrary free ORs (and dual circuits for OR bound): 40,000,000 circuits / 923,981,711 output candidates, with maximal free output completion; no counterexample. Only 32 candidates survived the low-cost and pair-edge girth filters, and none equalled its graph function even after completion. Source/log: `countbound_repair.cpp`, `.log` in scratch.
- These are ordinary exact/random computations, not Lean proofs. The six-vertex cyclic OR≥5 cases (C6 and C5 with a leaf) were not exhaustively resolved by this agent. No theoretical counterexample found; graph-specific singleton/minterm constraints appear consistent with both bounds.

### Weaker minimal-circuit variant

`results/orch/lemmas/CountReductionMinimal.lean` compiles, 508 lines, SHA-256 `700bf91868a30f60c06c0edd0bfa179a60995c3a4818bf15d65670f9b3b203f2`. Both count children now assume `IsMinimalMonoCircuit n C`, weakening the universal all-Monotone2 children. The constructed clean circuit seeds a Nat.find minimum circuit K; apply both count bounds to K, and compare clean C ≤ K ≤ any competitor. This adds 21 lines and is recommended over the first candidate. Original CountReduction remains frozen. Complete log: `/tmp/oec/pequalnp-pilot-43/count-reduction-minimal-check.log`.

### OR-count follow-up

- 2026-11-24T22:04:08.601663+00:00: proved in Lean that AND-only circuits preserve pointwise Boolean meet. Consequently an AND-only graph edge-function circuit can have at most one edge. Core compiled; short corollary that any graph with ≥2 edges needs an OR was appended, pending cache restoration (Mathlib DirectoryDependency.olean temporarily absent). File: results/orch/lemmas/OrBoundBase.lean.
- A simple per-gate separated-minterm measure fails on P4: product of edge monomials ab and cd contains a third edge bc. Circuit `(a OR c) AND (b OR d) AND (b OR c)` computes P4 and illustrates later AND filtering of intermediate nonedges, while respecting OR bound.
- Existing L_meta_1491 charging theorem allows Ustar residual edges to be paid from several gate classes; separate OR lower bound is genuinely stronger than directly available inequality. Weighted finite checks by counterexample agent support it through n=5.
