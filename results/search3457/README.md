# L-meta-3457 exploratory searches

These are computational research artifacts, not Lean-checked proofs. No search found a counterexample to the posted statement, and no full proof or refutation is claimed. The SAT encoding and its normalization/symmetry arguments have not been certified in Lean. In particular, a solver UNSAT verdict below is a verdict about the generated CNF.

## Results

| Instance | Search | Result |
|---|---|---|
| All 15 C4-free 2-by-2 incidence matrices | Exhaustive normalized wire-function-set BFS through three gates | Dirty/clean minimum sizes agree; three-edge cases use an explicit four-gate clean upper bound |
| C6, 3-by-3 off-diagonal incidence, mask 238 | Seven gates, singleton-clean ANDs, full 64-row truth table | CaDiCaL UNSAT |
| Same C6 | Eight gates | SAT; saved witness independently evaluated on all 64 assignments |
| 4-by-4 C4-free graph, nine edges, mask 13726 | Eleven gates, full truth table | Interrupted in favor of the smaller critical-row encoding |
| Same graph | Eleven gates, critical rows | UNKNOWN after 120 seconds |
| Same graph | Eleven gates, exactly four ANDs, critical rows | UNKNOWN after 60 seconds |
| Same graph | Eleven gates, critical rows and colex gate ordering | UNKNOWN after 120 seconds |
| Same graph, additionally clean ANDs | Eleven gates, critical rows and colex ordering | Interrupted; no verdict |
| C8, 4-by-4 incidence, mask 13740 | Ten gates, critical rows and colex ordering | Interrupted; no verdict |
| Same C8 | Ten gates, critical rows, colex and edge-useful pruning | UNKNOWN after 120 seconds |
| Nine-edge 4-by-4 graph, mask 13726 | Eleven gates, critical rows, colex and edge-useful pruning | UNKNOWN after 120 seconds |

The natural star constructions use twelve gates for mask 13726 and eleven gates for mask 13740. These are upper bounds, not established lower bounds here. An N5 heuristic result is listed below; it is not a circuit lower bound.

## Encoding

An incidence matrix is encoded row-major: bit `p*N+l` states whether point `p` meets line `l`. Inputs are the N point variables followed by the N line variables. Each synthesized gate is binary AND or OR, reads two distinct earlier wires, and the final gate is the output. Every other gate must feed some later gate. All AND outputs are constrained false on every singleton input.

The normalization rationale is that constants, copies, repeated-input gates and dead gates can be simplified away for a nonempty edge function. This rationale is mathematical background for the search, not a formal normalization certificate. The search allows duplicate wire functions and does not assume syntactic multilinearity or single-level structure.

`--clean` additionally makes every AND false on each nonincident point-line pair. Same-part pairs and larger independent sets are not silently omitted from function correctness.

By default the encoder checks all assignments. `--critical` instead checks output true on every edge pair and false on every maximal independent vertex set. For monotone circuits these determine the full edge function: every positive set contains an edge, and every negative set extends to a maximal independent set. Singleton rows, and nonincident cross-pair rows when requested, are also included to constrain internal gates.

`--sym-c6` restricts the first unordered input pair to `(0,1)`, `(0,3)`, or `(0,4)`, representatives under C6 graph automorphisms. `--sym-auto` computes part-preserving and part-swapping graph automorphisms. `--colex` orders gate input pairs by larger then smaller wire index; a topological ordering that always selects the available gate with smallest such pair motivates this restriction. When combined with graph automorphisms, representatives use the same colex order. These symmetry/completeness claims are not Lean-checked.

The optional `--edge-useful` flag requires each AND to accept a real edge pair, motivated by the separately developed edge-useless-gate elimination lemma. Two later N4 runs used this pruning and both returned UNKNOWN. The earlier C6 verdicts do not depend on this extra constraint.

All SAT witnesses are independently recomputed over every assignment, even when critical rows generated the CNF. The C6 witness is in `n3-m238-k8-dirty.witness.json`, with wire numbering starting at six.

## Reproduction

Original working directory: `/workspace/pequalnp-proofs`. The scripts retain the original scratch path `/tmp/oec/pequalnp-pilot-53/search/` and pinned solver path `/tmp/oec/pequalnp-pilot-53/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical`; adjust those two paths when reproducing elsewhere. Create the scratch directory first. CaDiCaL was version 2.1.2, with default random seed 0. Each solver child has a 256 MiB address-space limit. All stdout and stderr were saved, including interrupted runs. The latest wrapper also imposes an external wall limit five seconds beyond the solver limit and deletes any stale solution file before starting.

```sh
python3 results/search3457/small3457.py
python3 results/search3457/synth3457.py --N 3 --gates 7 --mask 238 --seconds 90 --sym-c6
python3 results/search3457/synth3457.py --N 3 --gates 8 --mask 238 --seconds 90 --sym-c6
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 180 --sym-auto
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 120 --sym-auto --critical
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 60 --sym-auto --critical --and-count 4
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 120 --sym-auto --critical --colex
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 120 --sym-auto --critical --colex --clean
python3 results/search3457/synth3457.py --N 4 --gates 10 --mask 13740 --seconds 120 --sym-auto --critical --colex
```

Additional edge-useful runs:

```sh
python3 results/search3457/synth3457.py --N 4 --gates 10 --mask 13740 --seconds 120 --sym-auto --critical --colex --edge-useful
python3 results/search3457/synth3457.py --N 4 --gates 11 --mask 13726 --seconds 120 --sym-auto --critical --colex --edge-useful
```

The later `stochastic3457.py` is a heuristic search, with no completeness or UNSAT implication. It checks the C4-free graph condition, uses full truth tables, penalizes singleton-responsive ANDs, and starts from randomized minimum-cover star circuits with one gate removed. It randomizes minimum covers, edge ownership and binary OR trees, then mutates read-back gate operands/types under simulated annealing. Any zero-score witness is independently checked by scalar evaluation on every assignment. The score is truth-error count plus 16 times erroneous edge pairs, 32 times erroneous maximal-independent-set inputs, and 256 times AND/singleton violations. All random choices use the recorded seed; time-bounded runs can execute different iteration counts on other machines. The evaluator and deletion remap received an independent read-only review by the lower_bound agent; this does not constitute a formal certificate.

```sh
python3 results/search3457/stochastic3457.py --N 4 --mask 13740 --gates 10 --seconds 120 --seed 0 --out results/search3457/stoch-n4-m13740-k10-seed0.json
python3 results/search3457/stochastic3457.py --N 4 --mask 13726 --gates 11 --seconds 120 --seed 0 --out results/search3457/stoch-n4-m13726-k11-seed0.json
```

Completed stochastic results (all 120 seconds, all without a witness):

| Instance | Seed / schedule | Mutations | Best full-truth errors | AND singleton violations |
|---|---|---:|---:|---:|
| C8, mask13740, 10 gates | Seed0, temperature10, 10000-step restarts | 44646144 | 8 | 0 |
| Nine edges, mask13726, 11 gates | Seed0, temperature10, 10000-step restarts | 41291792 | 5 | 0 |
| Same nine-edge graph | Seed1, temperature60, 100000-step restarts | 36660416 | 5 | 0 |

The last command was:

```sh
python3 results/search3457/stochastic3457.py --N 4 --mask 13726 --gates 11 --seconds 120 --seed 1 --temperature 60 --restart-steps 100000 --out results/search3457/stoch-n4-m13726-k11-seed1-hot.json
```

Complete stdout, stderr and best-candidate JSON are saved for every stochastic run. The nine-edge graph consists of three paths `[0,5,3,4]`, `[0,6,2,4]`, `[0,7,1,4]` with common endpoints. Thus, after renaming inputs, its function is `x(a OR b OR c) OR y(p OR q OR r) OR ap OR bq OR cr`. This structural identification is an independently checked finite graph fact, not a circuit lower bound.

Generated CNF and large mapping files are omitted because the preserved script regenerates them. The complete captured solver output, solution-status files where available, wrapper output, and the verified C6 witness are included. Search work paused for cache repair after the interrupted runs, then resumed for the explicitly listed edge-useful and stochastic searches.

## N5 theta graph search

After a fresh lease renewal, the same stochastic search was run for120 seconds on mask18125950, the C4-free graph of four length-three paths sharing endpoints. Its canonical minimum-cover construction uses16 gates; the search attempted15. Seed0, temperature60 and100000-step restarts found no witness after 35274496 mutations and 353 restarts. The best candidate has 9 full-truth-table errors and 0 AND singleton violations, confirmed by independent scalar evaluation on all1024 assignments. Complete stdout, stderr and JSON are preserved.

```sh
python3 results/search3457/stochastic3457.py --N 5 --mask 18125950 --gates 15 --seconds 120 --seed 0 --temperature 60 --restart-steps 100000 --out results/search3457/stoch-n5-m18125950-k15-seed0-hot.json
```

## Auxiliary operator-count searches

The free-OR model in [free-or/README.md](free-or/README.md) found the N4 nine-edge graph impossible with at most three singleton-clean ANDs in its reviewed CNF (UNSAT,0.068s). Sanity cases C6 with two ANDs were UNSAT, C6 with three ANDs and the N4 graph with four ANDs were SAT; both witnesses passed full scalar checks twice. These are reviewed computational results, not Lean certificates.

The complementary free-AND model with at most seven ORs returned UNKNOWN after120 seconds, both unrestricted ([free-and/README.md](free-and/README.md)) and with the necessary singleton condition on multi-leaf AND regions ([free-and-root/REVIEW.md](free-and-root/REVIEW.md)). Thus no OR-count bound or total-size normalization is established. All source, full logs, small CNFs, mappings and result JSON are preserved. No search remains active.
