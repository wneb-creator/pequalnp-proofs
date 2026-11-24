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
