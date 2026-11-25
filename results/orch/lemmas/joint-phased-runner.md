# Separate phased runner for joint cut families

2026-11-25 UTC. Root requested a separate CaDiCaL phase runner for a possible later portfolio. The next allocated joint TEN run remains Kissat. No target-budget phased search was launched during this task.

`joint_phased_run.py` is a new wrapper around the existing reviewed `circuit-search/phased` binary. It accepts `--cnf`, `--phases`, `--prefix`, and `--seconds`. It does not modify the frozen joint encoder, decoder, Kissat runner, solver helper, or active inputs.

Before starting the helper it checks the joint metadata and CNF hash/header, rejects zero phase literals, rejects IDs outside the CNF variable range, and rejects conflicting duplicate preferences. Identical duplicates are allowed and counted. It records hashes of the wrapper, decoder, helper binary and source, CNF, map, and phase file; captures complete solver stdout/stderr; and records wall/CPU/resource statistics. Every SAT result passes through the unchanged joint decoder, including complete-model and clause checks, selected-branch cut checks, exhaustive residual evaluation, and full 16,384-input embedding validation.

For the smoke, a complete satisfying assignment from the already verified fixed TEN branch-0 baseline was converted to 1,585 phase preferences. This exactly matches the fixed-baseline CNF, rather than reusing phase IDs from the ten-gate target. The phased helper returned SAT in 0.098 wall seconds and 0.058 CPU seconds. The decoder checked all 28,124 clauses, all 1,024 residual inputs, and all 16,384 full inputs. The reported full circuit has 27 gates: this is a known-baseline smoke, not a solution to the posted gap.

Three additional preflight smokes used a zero literal, an out-of-range literal, and conflicting duplicates. Each was rejected before any solver process or run record was created.

Circuit_search independently reviewed the frozen wrapper, matched all source/input hashes, rechecked every smoke clause, and re-evaluated the full truth table. Verdict: PASS. Evidence: `circuit-search/joint-phased-independent-review.json` and `.log`. Wrapper SHA256: `9825bffc5951099409b55c12d5324b8559147cb34a9021b1ea1c16b2d9ac2cb9`.

Separately, lower_bound independently reviewed `joint_phases.py` and the 991-literal branch-3 near-seed phase file. It reconstructed all preferences and validated the edge-deleted seed on all residual/full inputs. Verdict: PASS; see `joint-phases-review.md`. These preferences remain intentionally inconsistent with the one missing positive output, and are soft `solver.phase` hints only. They add no assumptions or clauses.

Stable artifacts under `/tmp/oec/pequalnp-pilot-70/constructive/` include:

* `joint_phased_run.py`
* `joint_phased_preflight_smoke.py`
* `joint-ten11-baseline-model.phases` and its provenance JSON
* `joint-phased-baseline-smoke-v1-run.json`, result/log/solve-log/verified/witness files
* `joint-phased-preflight-v1-result.json` and complete case logs
* the separately reviewed `joint_phases.py`, `joint-ten10-branch3-near.phases`, adjacent report, and generation log

The wrapper is ready for later allocation. The generic independent-input phased decoder must not be used on these correlated joint CNFs.
