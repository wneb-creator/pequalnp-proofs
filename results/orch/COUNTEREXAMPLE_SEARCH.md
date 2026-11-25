# L-meta-2592 counterexample search

No counterexample was found. None of the computational exclusions below is a Lean-checked proof of the gap.

## Native truth-table optimization

The Petersen edge function is false on 76 of its 1,024 inputs. Exhaustive vertex-cover enumeration gives minimum cover size 6, with 5 covers. Orienting the edges within these covers gives the 40 valid 20-gate monotone circuits embedded in `lemmas/search_seeds.hpp`.

`lemmas/search_local.cpp` searches 19-gate AND/OR/NOT circuits initialized by deleting and rerouting one gate from those seeds. Every fitness evaluation uses all 1,024 input assignments. Gate-operation codes are 0 = AND, 1 = OR, 2 = NOT. The output is wire 28.

Compile from the repository root:

```sh
g++ -O3 -std=c++20 results/orch/lemmas/search_local.cpp -o /tmp/oec/pequalnp-pilot-101/counterexample/search_local
```

Runs, with arguments seed, time limit in seconds, penalty for having no NOT, and random-order flag:

```sh
/tmp/oec/pequalnp-pilot-101/counterexample/search_local 101 600 8 0
/tmp/oec/pequalnp-pilot-101/counterexample/search_local 102 600 100 1
```

The first run completed its 600-second limit. The second was stopped on the orchestrator's instruction after it stalled. The current source records extra intermediate candidates compared with the original first-run executable, while retaining its ordered-start search mode.

Independent validation with `lemmas/search_validate.py` re-evaluated all 43 logged candidates. The best candidate without NOT has 9 incorrect rows. The best candidate containing NOT has 10 incorrect rows, and its NOT gate is unused. Neither is a witness. Full logs and best-candidate JSON are in `/tmp/oec/pequalnp-pilot-101/counterexample/search-local-{101,102}*`.

## SAT experiments on the full Petersen function

The repository's `notes/data/lrat-link/gennot.py` generated the necessary constraints on 15 minimal true rows and 15 maximal independent rows. First-gate cases were fixed to NOT of input 0, AND of adjacent inputs 0 and 1, and OR of nonadjacent inputs 0 and 2. All three were SAT, but independent evaluation found respectively 682, 378, and 858 incorrect rows. These models are spurious partial-row solutions.

The strengthened CEGAR driver is `lemmas/sat_cegar.py`, maintained by the semantic-audit agent. It uses unique selectors and at least one, at most four NOT gates. The following runs returned UNKNOWN at their 300-second limits:

- AND of adjacent inputs first: 187 explicitly added rows, 401,886 clauses. Original complete logs are under `/tmp/oec/pequalnp-pilot-101/sat-and-edge/`.
- AND of nonadjacent inputs first: 192 explicitly added rows, 408,366 clauses. Complete logs are under `/tmp/oec/pequalnp-pilot-101/counterexample/sat-and-nonedge/`.

The original 30 rows are also included by the reference CNF. UNKNOWN is not an exclusion. A duplicate OR-nonedge run briefly shared the semantic-audit agent's scratch path; those shared logs are uncertain and are excluded from every claimed result.

## Smaller hexagon construction

Deleting Petersen vertex 0 and its neighbors 1, 4, 5 leaves a six-cycle on the ordered vertices `[2,3,8,6,9,7]`. Let H be this cycle's edge function, and set U = x2 OR x6, V = x3 OR x9, W = x7 OR x8. Then the Petersen function is:

    H OR (x1 AND (U OR x0)) OR (x4 AND (V OR x0)) OR (x5 AND (W OR x0)).

Consequently a ten-gate circuit exposing H, U, V, W would give a nineteen-gate Petersen circuit. `lemmas/search_hexagon.py` encodes this smaller search over all 64 rows. Sources are existing wires, AND and OR inputs are distinct, NOT reads one source, and every non-output gate except the three exposed ORs is used later. The output H is last.

With U, V, W fixed as the first three OR gates, the ten-gate search was UNSAT both with exactly one NOT (6.52 seconds) and with one through seven NOTs (10.67 seconds). This excludes only the stated restricted construction. It is not a proof that every possible circuit has that form.

Generate the two encodings from the repository root:

```sh
python3 results/orch/lemmas/search_hexagon.py /tmp/oec/pequalnp-pilot-101/counterexample/hexagon10.cnf
python3 results/orch/lemmas/search_hexagon.py /tmp/oec/pequalnp-pilot-101/counterexample/hexagon10-allnot.cnf --not-count 7
```

Solve using the bundled CaDiCaL executable, preserving complete stdout and stderr:

```sh
/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/cadical -t 300 -w /tmp/oec/pequalnp-pilot-101/counterexample/hexagon10.sol /tmp/oec/pequalnp-pilot-101/counterexample/hexagon10.cnf > /tmp/oec/pequalnp-pilot-101/counterexample/hexagon10.log 2>&1
```

The `--free-prefix` variant permits the three exposed pair-OR outputs to be any wires while still placing H last. It returned UNKNOWN at its 300-second wall-clock limit (238.11 seconds CPU); no witness or exclusion was obtained.
