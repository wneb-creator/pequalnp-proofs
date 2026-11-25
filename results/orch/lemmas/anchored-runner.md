# Anchored-tail runner

Prepared 2026-11-25. `/tmp/oec/pequalnp-pilot-70/constructive/anchored_run.py` is a separate runner for the independently reviewed anchored-tail encoding. It does not modify the encoding, decoder, solver, or active runs.

The runner pins the reviewed `anchored_tail.py` source and Kissat binary hashes. Its defaults also pin the production 26-gate CNF and map. Explicit expected CNF/map hashes allow the already reviewed fixed 27-gate baseline smoke. All four hashes are checked before solving and again afterward; SAT verification is followed by a third pin check.

Complete solver stdout/stderr is saved in `-solve.log`. On SAT, a separate subprocess invokes the frozen source's `verify` action, preserving its complete stdout/stderr in `-verify.log`. The verifier checks every CNF clause, all encoded rows, selected gate semantics, core inequalities, and all 16,384 full inputs. The runner requires a `VERIFIED` report with the expected gate count, clause count and hashes before creating `-witness.json`. The witness is only the full gate-triple array. Run/result JSON records commands, hashes, timestamps, solver and verification wall/CPU times, and process RSS high-water marks.

The known 27-gate baseline smoke used a five-second solver cap and returned SAT in 0.211513 wall seconds / 0.137220 CPU seconds. Verification took 3.000881 wall seconds / 1.991332 CPU seconds and checked 211,180 clauses plus all 16,384 inputs. These are baseline sanity checks, not a new 26-gate result.

Stable smoke files have prefix `/tmp/oec/pequalnp-pilot-70/constructive/anchored-run-baseline-smoke-v1` and suffixes `-run.json`, `-result.json`, `-solve.log`, `-verify.log`, `-verified.json`, `-witness.json`, and `-wrapper.log`.

No production solver run was launched by this agent. circuit_search independently reported PASS, including all baseline clauses, all 16,384 inputs, and a wrong-pin rejection before launch. Evidence: `circuit-search/anchored-run-independent-review.json` and `.log` under the job scratch directory.
