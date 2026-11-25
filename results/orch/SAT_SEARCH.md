# Semantic-audit SAT experiments

No full Petersen model or UNSAT result was obtained. All runs below returned UNKNOWN at their time limits. These are exploratory computations, not Lean certificates. Exact-size normal forms and NOT preservation would require additional proof before any UNSAT result could imply the posted statement.

The independent decoder `lemmas/sat_validate.py` evaluates every decoded circuit on all 1,024 inputs. The initial 30 boundary rows are insufficient when NOT gates are allowed: the original first-NOT partial model disagrees on 682 inputs.

The batch CEGAR driver is `lemmas/sat_cegar.py`; the incremental CaDiCaL C-API driver is `lemmas/sat_incremental.cpp`. Both impose unique operation/source selectors and validate full truth tables before accepting a functional match. Native driver exit status zero means the driver completed; the logged solver result is 0 = UNKNOWN, 10 = SAT, 20 = UNSAT.

Create the base formula from the repository root, after creating the scratch directory:

```sh
python3 notes/data/lrat-link/gennot.py 10 19 '01,12,23,34,40,05,16,27,38,49,57,79,96,68,85' /tmp/oec/pequalnp-pilot-101/counterexample/petersen19rows.cnf rows > /tmp/oec/pequalnp-pilot-101/sat-base-generation.log 2>&1
```

The incremental driver was linked against the bundled static CaDiCaL library:

```sh
g++ -O2 -std=c++17 results/orch/lemmas/sat_incremental.cpp /tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/lib/lean/libcadical.a /tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/lib/libc++.a /tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/lib/libc++abi.a -lpthread -ldl -o /tmp/oec/pequalnp-pilot-101/sat-incremental-pruned > /tmp/oec/pequalnp-pilot-101/sat-incremental-build.log 2>&1
```

Run a 900-second singleton-neighbor case:

```sh
/tmp/oec/pequalnp-pilot-101/sat-incremental-pruned /tmp/oec/pequalnp-pilot-101/counterexample/petersen19rows.cnf not_one_single1 /tmp/oec/pequalnp-pilot-101/sat-incremental-single1-pruned 900 > /tmp/oec/pequalnp-pilot-101/sat-incremental-single1-pruned.log 2>&1
```

Replace `not_one_single1` with `not_one_single2` and use a distinct output prefix for a singleton nonneighbor. Both modes fix the sole NOT as the first gate, negating input 0; all later gates are monotone. The 38 cofactor boundary rows from `OneNotSamples.lean` suffice for these circuits and are included, with other reference rows, in the 50 encoded rows. The singleton restrictions and first-binary-mate pruning are additional assumptions, with finite semantic checks supported by the separate Lean lemmas. They do not cover arbitrary circuits with one or more NOT gates.

Recorded runs:

| Run | Time limit | Result | Complete log |
| --- | ---: | --- | --- |
| Batch first NOT, at most four NOTs, 187 explicit rows | 240s | UNKNOWN | `logs/sat-not-run.log`, `logs/sat-not-0.log` |
| Incremental first NOT, at most four NOTs, 42 rows | 1200s | UNKNOWN | `logs/sat-incremental-not.log` |
| Incremental sole first NOT, 50 rows | 1200s | UNKNOWN | `logs/sat-incremental-one.log` |
| Sole first NOT, singleton neighbor, before mate pruning | 600s | UNKNOWN | `logs/sat-incremental-single1.log` |
| Sole first NOT, singleton nonneighbor, with mate pruning | 900s | UNKNOWN | `logs/sat-incremental-single2-pruned.log` |

The pre-pruning singleton run used an earlier version of the incremental source; the current source includes the finite first-binary-mate cuts. Complete earlier logs are retained as observations. The other drivers retain their relevant modes. An accidentally shared OR-nonedge scratch log was overwritten; it supports no claimed result.

The second pruned singleton run (neighbor v1) also completed at its 900-second cap with UNKNOWN, retaining 50 rows and 189091 clauses. Its complete output is `logs/sat-incremental-single1-pruned.log`. No candidate was produced.

The batch first-NOT run saves both the driver and complete child-solver diagnostics. Its solver status (`logs/sat-not-0.sol`) is UNKNOWN and its full summary is `logs/sat-not-summary.json`.
