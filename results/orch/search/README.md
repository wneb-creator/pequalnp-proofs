# Frozen counterexample search snapshot

This directory preserves search code and a known baseline, not a proof of L-meta-1477. No circuit with at most 124 gates has been found. All UNSAT results below are computational results for the stated finite encoding; they are not Lean-checked lower bounds.

The task scratch directory in these commands is `/tmp/oec/pequalnp-pilot-29`. The bundled solver is `/tmp/oec/pequalnp-pilot-29/lean-4.36.0-linux/bin/cadical`. Complete live logs remain in task scratch. Files ending `.snapshot` are explicitly incomplete snapshots of running searches. Source hashes and freeze time are in `manifest.json`.

## Main hyperoval search

The target has six point inputs 0 through 5 and fifteen pair inputs 6 through 20 in lexicographic pair order. Its 30 minterms are incidences of a point with a pair containing it. The 58 maximal false inputs are encoded exactly by all subsets of the six point inputs and closure of their allowable pair inputs. Thus the SAT problem has 88 positive/negative test assignments. Every candidate is an AND/OR circuit, so correctness on these extremal inputs implies correctness on all inputs. The decoder independently checks the 30 positive inputs and all 64 point-subset negative inputs, including nonmaximal ones.

Generate the ordinary 34-gate search:

```sh
python3 results/orch/search/code/Search.py --case k6 --gates 34 --output /tmp/oec/pequalnp-pilot-29/search-k6-34.cnf
/tmp/oec/pequalnp-pilot-29/lean-4.36.0-linux/bin/cadical -t 1800 /tmp/oec/pequalnp-pilot-29/search-k6-34.cnf
```

This model uses two distinct ordered prior-wire inputs per gate, AND/OR choice, and requires every nonfinal gate to be used. Adjacent independent gates have lexicographically ordered input pairs. The first gate input pair is restricted to a representative of its orbit under the six-point permutation group. Pruning requires every gate to fire on some positive test and fail on some negative test, and requires its operand signatures on the tests to be incomparable. These minimality restrictions are safe for a globally smallest witness. Consequently UNSAT at exactly 34 gates would not automatically exclude a smaller minimum circuit. The optional `--no-incomparability` variant permits absorbing output padding and is prepared but was not running at freeze time.

## Compressed restricted search

```sh
python3 results/orch/search/code/SearchFactored.py --ands 7 --size 34 --output /tmp/oec/pequalnp-pilot-29/search-factored-and7-size34.cnf
/tmp/oec/pequalnp-pilot-29/lean-4.36.0-linux/bin/cadical -t 1200 /tmp/oec/pequalnp-pilot-29/search-factored-and7-size34.cnf
```

This searches a restricted architecture: exactly seven AND nodes, each operand an OR of selected primary inputs and earlier AND outputs; the final output is an OR of selected AND outputs. OR subcircuits are not shared. If the total number of selected sources is S and there are a AND nodes, the emitted circuit has S-a-1 gates. A sequential cardinality encoding imposes at most 34 gates. Operand inclusion vectors are ordered to remove AND commutativity. Every AND must fire on a positive test and fail on a negative test. A SAT answer would be a valid counterexample candidate; UNSAT would only concern this restricted architecture.

Decode either format:

```sh
python3 results/orch/search/code/SearchDecode.py --map INSTANCE.map.json --log COMPLETE_SOLVER.log --output WITNESS.json
```

The decoder checks gate indices and gate count and evaluates all positive tests plus all point-subset negatives. The resulting tuples are directly usable by the Lean verifier prepared by the geometry agent.

## Calibration and completed results

- `baseline35.json` is the known six-star circuit: 21 inputs, 35 gates, 6 ANDs, 29 ORs, output wire 55. Its tuple list matches the independently Lean-checked hyperoval baseline artifact.
- The ordinary 35-gate encoding was checked clause by clause against this baseline: all 816,772 clauses passed, including symmetry and minimality restrictions.
- A C6 eight-gate circuit padded by one absorbing final OR was checked against all 6,146 clauses of the `--no-incomparability` nine-gate encoding.
- `logs/search-c6-7.log`: solver UNSAT for the original exact-seven-gate, all-gates-used binary model on all 64 inputs. Reproduce generation with `Search.py --case c6 --gates 7 --truth exhaustive --no-ordering --no-pruning`.
- `logs/search-c6-8.log`: SAT for the corresponding eight-gate model; the extracted circuit was independently evaluated on all 64 inputs.
- `logs/search-concurrent3-7.log`: UNSAT for the seven-gate core of three concurrent projective-plane stars. Reproduce generation with `Search.py --case plane_local --points 0,1,4 --gates 7 --no-ordering --no-pruning`. The source edge list is read from the saved task statement in scratch.
- `logs/search-factored-calibration.log`: forced six-star baseline SAT. Reproduce with `SearchFactored.py --ands 6 --size 35 --baseline`; the decoder independently checked all 94 test assignments.

The C6-with-private-leaves searches, K4-incidence search, and ordinary exact-seven-AND K6 search were stopped or timed out without a verdict. They produced no UNSAT claim and no witness. Their complete diagnostic logs remain in task scratch. There are at most two active solver processes because the environment has five CPUs.
