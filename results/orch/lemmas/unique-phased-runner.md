# Phase-guided unique-input runner

Prepared 2026-11-25 09:33 UTC. This bundle prepares a solver run; it contains no new 26-gate witness and no production solve was launched by the constructive agent.

New, separate sources in `/tmp/oec/pequalnp-pilot-70/constructive/`:

- `unique_phased_run.py`: pinned CaDiCaL phase-guided runner.
- `raw_verify.py`: full SAT-model and raw-input circuit verifier.
- `unique_phased_preflight_smoke.py`: nine rejection tests that never launch a solver.

The runner defaults pin the exact reviewed `unique0-26-permissive-final.cnf`, its map, and `unique0-26-near.phases`. It also pins the existing `phased` binary, its `phased.cpp` source, and the new raw verifier. The wrapper's own hash is recorded in every run. Explicit expected CNF/map/phase hashes permit the retained fixed 27-gate baseline smoke without modifying production artifacts.

Before creating a run record or solver log, preflight checks all six pins, the CNF header against the map, and every phase token. It rejects empty or non-ASCII files, malformed integer tokens, zero, out-of-range IDs, and conflicting duplicates. Identical duplicate preferences are permitted and counted. The reviewed helper calls `solver.phase` only; preferences add no assumptions or clauses. Its steady-clock solver deadline starts after DIMACS parsing.

On SAT, a separate process runs `raw_verify.py`. It requires a complete, consistent SAT model and checks every CNF clause. It then verifies exactly one selected operand per side, sorted forward references, every encoded row output and recorded mux value, and all 16,384 inputs against an explicit copy of the posted 21-edge Heawood target. It does not derive the target from untrusted result text. The runner rechecks all pins and writes a plain full gate-triple witness only after the verifier reports `VERIFIED` with matching hashes and counts. Complete solver and verification stdout/stderr, commands, wall/CPU times, and RSS high-water marks are retained.

The fixed baseline smoke used the existing anchored-tail 27-gate CNF, all 7,582 soft phase preferences from its reviewed SAT model, and a five-second solver limit. It returned SAT in 0.489065 wall seconds / 0.307585 CPU seconds. Raw verification took 2.519928 wall seconds / 1.683922 CPU seconds and checked all 211,180 clauses and all 16,384 inputs. These checks concern the known 27-gate baseline only.

Nine preflight smokes rejected zero, out-of-range, conflicting, malformed, empty, and non-ASCII phase data, plus wrong CNF/map/phase hashes. Each test confirmed that no run record, solver log, verification output, or witness was created. The valid production inputs were checked separately without launching a solver: 26 gates, 7,253 variables, 208,826 clauses, and 5,928 distinct phase preferences.

Stable evidence uses these prefixes in the constructive scratch directory:

- `unique-phased-baseline-model.phases` and `.provenance.json`.
- `unique-phased-baseline-smoke-v1-*`: full run, solver log, verification log, verified circuit, witness, and result.
- `unique-phased-preflight-v1-*`: nine input/log pairs, the test summary, and wrapper log.
- `unique-phased-production-preflight.json`: read-only production pin/phase validation, explicitly recording that no solver was launched.

sat_review independently reported PASS for the exact wrapper, preflight and raw verifier. The review checked all production pins and 5,928 preferences, independently repeated the nine rejection-only preflights, ran eleven raw DIMACS/model parser tests, and rechecked every baseline clause, encoded row value and full input. Evidence is `sat-review/review_unique_phased.py`, `unique-phased-review.log` and `.json`, plus the independent preflight/parser logs under the job scratch directory. No active source or solver input was edited.
