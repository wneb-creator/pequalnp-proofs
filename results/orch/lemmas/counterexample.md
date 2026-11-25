# Counterexample search for L-meta-2592

Started 2026-11-25 13:48 UTC. Only root holds and renews the lease.

## Semantics checked

`Circuit` is a straight-line list of gates. Out-of-range and forward wire reads yield false. An empty AND yields true and an empty OR yields false; all gates still count. `FanInTwo` allows only AND, OR and NOT and at most two inputs. NOT reads only its first input. No apparent semantic shortcut was found.

## Known 20-gate circuit checked computationally

A minimum vertex cover of size six gives 20 gates: 15 gates total inside six stars, then five OR gates. The particular cover is `{1,3,4,5,6,7}`. A concrete circuit was evaluated on all 1024 assignments using an independent Python evaluator. Its gate list is saved in `/tmp/oec/pequalnp-pilot-99/counterexample/upper20.txt`. This is computational evidence, not a Lean theorem.

## Stochastic search

`counterexample/search.cpp` (under the same scratch root) evaluates all 1024 truth-table rows with 16 machine words. It uses 19 gates and penalizes circuits containing no NOT. Starts are obtained from all five minimum vertex covers, randomized star order/orientation, deleting one gate and changing one operation to NOT. Hill climbing, neutral mutations, annealing, and random restarts run for ten minutes.

The best initial result has ten wrong truth-table rows; no counterexample has been found. The complete log is `counterexample/search.log`.

## SAT synthesis

The Lean toolchain's Cadical executable is available at `/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical`. The script `counterexample/synth.py` builds exact Boolean gate-selection constraints, starts with all 76 false rows and the 15 two-input edge witnesses, and independently checks any model on all 1024 rows. Any newly discovered mismatches are added in another round.

The encoding searches connected, constant-free circuits with distinct binary inputs. This is a restricted counterexample search, not a complete lower-bound certificate. Initial runs: arbitrary placement of exactly one NOT (`sat-not1`), and exactly one NOT fixed to the first gate on input zero (`sat-inputnot`). Each solver run is capped at 300 seconds. CNF files, selector/row metadata, full stdout, and full stderr are retained under the scratch `counterexample` directory.

Positive sanity check: fixing the independently verified 20-gate circuit gives SAT, and its decoded model agrees on all 1024 rows (`sanity20b.log`). The earlier `sanity20.log` used an over-broad terminal label `COUNTEREXAMPLE`; it is only the 20-gate sanity witness and does not refute the target. The script now prints the actual gate and NOT counts.

Additional structured search `sat-parity`: choose independent set `{0,2,8,9}`. Its complement has three internal matching edges `{1,6}`, `{3,4}`, `{5,7}`. Fix a five-gate circuit H computing the OR of these three products and fix the final gate to OR with H. The remaining thirteen gates, including one NOT, must handle the four star terms. The star neighborhoods pick one endpoint from each matching pair in four parity patterns. This exposes possible simplifications on the inputs where H is false; on H-true rows the other branch is unrestricted.

Both initial unrestricted-placement one-NOT search and first-input-NOT search hit their 300-second wall limits without SAT or UNSAT. These timeouts do not support a lower bound.

Added optional symmetry breaking: maximum fanin indices are nondecreasing across gates. Informal justification is greedy topological ordering by least maximum fanin among ready gates; any newly ready gate has maximum fanin equal to the just-created wire, so this quantity never decreases. Reordering the known 20-gate witness this way passed the same positive SAT and full-table sanity check (`sanity20-colex.log`). `sat-colex` searches with this constraint.

`repair.py` probes local SAT neighborhoods of the best approximate circuit, releasing roughly 8–10 gates while fixing the others. Its per-neighborhood cap is ten seconds. These are explicitly partial searches, and any local UNSAT is not a global circuit lower bound.

## Existing reductions

All three reductions are already in the repository: `R_meta_2592_408` normalizes wires and output; `R_meta_2592_271` separates the 15-binary-gate floor from the one-to-four-NOT case; `R_meta_2592_318` cuts at the last NOT. A fourth reduction should not be assumed available.
