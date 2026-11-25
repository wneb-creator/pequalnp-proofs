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

The first stochastic run completed 1,004,863,488 mutations in 600 seconds. Its best circuit computes the target plus the two nonedges `{0,2}` and `{4,7}`, differing on ten assignments. Its NOT is unused. A second run penalized absence of a syntactically live NOT; after 1,072,496,640 mutations in 600 seconds its best circuit has one live NOT and sixteen independently verified errors. Neither run found a witness.

All 24 local repair neighborhoods finished: five were UNSAT, nineteen timed out. Both five-minute colex searches also timed out without a verdict.

## Unrestricted canonical encoding

`canonical.py` now implements exactly the numeric scheme and clause order requested by the `sat_encoding` agent: AND0, OR1, TRUE2, NOT3; each gate source ranges through all earlier wires plus the explicit false source; output is arbitrary; unused and constant gates are permitted. There are no at-most-one, connectivity, ordering, or other normalization clauses. Only existence of at least one NOT is required. The agent independently reviewed the Python encoder against its Lean `encN` completeness theorem.

`canonical19.cnf` has 117,946 clauses and uses maximum DIMACS variable 126,510. It constrains the same 91 rows. An UNSAT certificate for this exact CNF would suffice for the full posted statement through the proved completeness bridge, without the restricted-search assumptions above.

Positive sanity check exercised a 21-gate circuit: the known 20-gate witness plus an unused NOT reading the explicit false source, with the output pointing to the previous gate. The canonical formula is SAT, and decoding agrees on all 1024 assignments.

At about 14:07 UTC, following root's fresh lease renewal, started a 1500-second Cadical run on the canonical CNF, retaining text LRAT and complete stdout/stderr as `long-canonical.*`. A separate 1500-second restricted colex run started about 14:02 UTC (`long-colex.*`). Neither has a verdict yet. The first 100,000 canonical LRAT lines contain 89,460 additions, 10,540 deletion records, and no negative hint records; this is only a prefix sample.

## Essential-NOT witness branches

The lower-bound agent supplied five simultaneous automorphism orbits with fixed true edge mask3 and independent blocker masks50,104,116,138,201. `witness_branches.py` adds exactly-one-NOT and the source/sign witness constraints, plus six counterfactual evaluations forcing the opened suffix to have the majority pattern on intersection, edge, blocker, and union. These are currently search constraints only; the full canonical CNF is kept unchanged. Each branch has an initial 60-second run, with all outputs retained.

All five witness branches timed out after 60 seconds; no model or contradiction was found.

## Count-restricted canonical search and storage

The `sat_encoding` agent compiled exact preservation of NOT count and completeness for the canonical formula with at most three NOTs. Together with the compiled sixteen-binary-gate floor, this remains complete for the full posted target. `canonical19-le3.cnf` appends 3,876 clauses, in descending quadruple order, to the unchanged baseline, for 121,822 total clauses.

Following root's renewals, the search portfolio now consists of the unrestricted canonical baseline started about 14:07 UTC and a canonical-at-most-three run started about 14:19 UTC. The latter writes binary LRAT to reduce disk use. A tiny UNSAT control confirmed the binary format. The earlier restricted colex run and the first text-LRAT at-most-three run were interrupted deliberately, with full outputs retained and their incomplete proof prefixes compressed. They did not produce a verdict and are not certificates. At least 5 GB of free disk is reserved for Lean artifacts.

A separate all-1024-row canonical probe, containing 1,328,735 clauses, timed out after 60 seconds.

## Free-complement sanity search

At the structural agents' request, `aig.py` searches seventeen binary gates with free wire and output complements. This is a different model from a nineteen-total-gate counterexample: a found witness would still need its NOT cost evaluated. A positive twenty-gate control passed SAT and all 1024 truth-table rows. The unrestricted seventeen-gate probe and two probes fixing the first signed gate to the edge/nonedge OR cases all timed out after 60 seconds. A ten-minute bit-parallel stochastic search in this model is running as `aig_search.cpp`; no exact witness has been found.

## Existing reductions

All three reductions are already in the repository: `R_meta_2592_408` normalizes wires and output; `R_meta_2592_271` separates the 15-binary-gate floor from the one-to-four-NOT case; `R_meta_2592_318` cuts at the last NOT. A fourth reduction should not be assumed available.
