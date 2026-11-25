# Joint selectable cut-family encoding

2026-11-25 UTC. Root proposed sharing one cone structure across all cut-pattern representatives. Constructive implemented separate files; no active encoder, decoder, input, or solver run was modified.

## Encoding

`joint_correlated.py` first revalidates each family's complete monotone boundary rows and every correlated cut column. All representatives must have identical underlying input order, target edges, and ordered underlying rows. A single one-hot selector chooses one whole representative. Every cone gate's operation and input selectors are shared across all representatives.

For each cut truth cell that is identical across all representatives, the encoder uses a fixed truth literal. Only varying cells receive new Boolean variables. A selected representative implies the corresponding constant value of every varying cell. Thus a model cannot combine cut columns from different variants. The gate-selection, AND/OR truth, commutative input order, and optional adjacent topological lex clauses follow the already reviewed separate-family encoding. Repeated operands and trivial intermediate gates remain allowed; no liveness, shadow, dirty-gate, or fixed-prefix restrictions are added.

The prepared production inputs are:

| File | Cone gates | Variants | Rows | Varying cells | Conditional cut clauses | Variables | Clauses |
|---|---:|---:|---:|---:|---:|---:|---:|
| `joint-ten10.cnf` | 10 | 6 | 17 | 14 | 84 | 1,423 | 24,789 |
| `joint-noncollinear14.cnf` | 14 | 7 | 27 | 29 | 203 | 2,476 | 51,096 |

The selector controls the complete reviewed variant, including its fixed prefix, support definitions, and wire mapping. The search scope is the union of those restricted cone families; no general circuit lower bound follows from an UNSAT result.

## Decoder and runner

`joint_decode.py` requires a complete SAT model and exactly one selected branch. It checks the CNF hash and every clause, then checks each selected input truth cell and every gate's encoded row value against direct evaluation. It exhaustively validates the decoded cone on all 1,024 TEN or 2,048 noncollinear underlying assignments, selects the matching full fixed prefix, checks every free-cut identity, and validates the embedded circuit on all 16,384 full inputs.

`joint_run.py` records the solver command, timestamps, CNF/map/solver hashes, CPU/wall statistics, and complete solver output. A SAT result is decoded into a structured verification JSON and a full-circuit witness JSON. The witness includes its full gate count, so the 27-gate known-baseline smokes cannot be mistaken for target witnesses. No production target-budget solve has been launched by constructive.

## Completed smokes

The TEN baseline suite passed 15 cases: a free-selector SAT baseline, six forced-selector SAT baselines, six opposite-cut-bit contradictions, and contradictions from zero or two selected branches. Every SAT baseline was decoded and exhaustively checked.

The noncollinear baseline suite passed the analogous 17 cases. These 32 tests use known 11- or 15-gate cone baselines and immediate contradictions, not target-budget synthesis searches. An additional runner smoke selected TEN branch 0, decoded the known baseline, and recorded an exact 27-gate full circuit. Its solver exit was 10, with full truth-table verification true.

Source and production artifacts are under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `joint_correlated.py`
* `joint_decode.py`
* `joint_smoke.py`
* `joint_run.py`
* `joint-ten10.cnf` and `.map.json`
* `joint-noncollinear14.cnf` and `.map.json`
* `joint-ten10-generation.log`
* `joint-noncollinear14-generation.log`
* `joint-ten11-smoke-v1-result.json` and its complete smoke logs/verified JSONs
* `joint-noncollinear15-smoke-v1-result.json` and its complete smoke logs/verified JSONs
* `joint-runner-smoke-v1-result.json`, log, verification JSON, and baseline witness JSON

The scripts use only Python's standard library plus the already installed Kissat executable. Independent review was requested from sat_review after all source files and production inputs were frozen.

## Independent review and optional phases

Both families subsequently received independent PASS verdicts in `sat-review/joint-ten-review.json` and `sat-review/joint-noncollinear-review.json`. The reviewer exhaustively checked the selector encodings, every varying cell and implication, exact preservation of the separate-family base gate/output clauses, all SAT smoke models clause by clause, and every residual/full truth table. The four reviewed sources and production inputs remain unchanged.

The optional `joint_phases.py` separately generated `joint-ten10-branch3-near.phases` from the validated ten-gate seed missing edge (1,13). It contains 991 unique nonzero signed phase preferences for the global selector, cut cells, gate choices, and boundary values; 432 auxiliary variables are omitted. The seed has one boundary mismatch, 16 residual false negatives, and 47 full Heawood false negatives, checked exhaustively. Exactly one fully assigned CNF clause is false under these near-seed preferences: the missing positive output. This is intentional and is not a satisfying model.

The installed `phased` helper calls CaDiCaL's `solver.phase`, so the file adds no assumptions or clauses. The production CNF hash is unchanged. No CaDiCaL solve was launched during this preparation. The phase generator, `.phases`, adjacent `.json` report, and complete generation log are separate optional artifacts and do not change the reviewed encoder/decoder.
