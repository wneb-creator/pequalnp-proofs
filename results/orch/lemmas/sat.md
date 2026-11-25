# SAT/CEGAR strategy for L-meta-2592

## Setup and scope

- Official CaDiCaL source was shallow-cloned into scratch from https://github.com/arminbiere/cadical (version 3.1.0); build logs are retained in `/tmp/oec/pequalnp-pilot-128/sat-cadical-*.log`.
- The newly restored Lean toolchain also contains CaDiCaL 2.1.2, usable immediately.
- No SAT result is a Lean result by itself. A witness must be checked on all 1024 assignments and formalized; an UNSAT result needs a checked certificate and a complete encoding link.

## Existing formally linked route

`notes/data/lrat-link/gennot.py` mirrors `PEqualNP.Library.LRAT.LinkN.enc2` for AND/OR/NOT circuits. Its normal form permits padding, constants, arbitrary output, and NOT sources; source ordering, used-gate, no-NOT-of-NOT, and lexicographic clauses have library justification. It does not require the circuit to contain a NOT gate, so UNSAT would establish the stronger full 19-gate lower bound.

Command shape: `python3 notes/data/lrat-link/gennot.py 10 19 '01,12,23,34,40,05,16,27,38,49,57,79,96,68,85' <scratch.cnf> rows`.

The `rows` option uses the fifteen minimal true assignments and maximal false assignments. With NOT gates this is a sound necessary condition, not enough for SAT to certify the complete truth table. Started a 600-second run with the bundled solver; complete output is `sat-linkn-19-rows.log`. Proof output is initially disabled because disk is constrained; if UNSAT is found, replay with LRAT output.

## Independent witness-search route

`sat_search.cpp` implements incremental selector/multiplexer CNF with one to four NOT gates. It begins with empty, singleton, pair, all-ones and all-but-one assignments; each SAT candidate is evaluated on all 1024 inputs, with failing rows added. Search includes connectedness and reduced-gate restrictions and optional source-ordering symmetry. These are explicitly search restrictions, not a formally proved complete encoding.

A built-in `selftest` fixes the known 20-gate vertex-cover construction and its deliberately corrupted version on all 1024 assignments, expecting SAT and UNSAT respectively. This must pass before interpreting search output.

Compilation and runs are in progress; no witness or UNSAT result yet.

## Results so far

- First exact LinkN boundary-row instance was SAT after63.51seconds; its19-gate,2-NOT candidate fails884 of1024 inputs. Full model and exhaustive decode are retained in scratch. It is not a counterexample.
- Strengthened exact linked instance uses102rows: all76false inputs, all15minimaltrue edge inputs, allones and ten all-but-one inputs. It has232885clauses and is running with a600second bound.
- CaDiCaL3.1 build completed after a temporary disk-full interruption. `sat-search selftest` passed: known20-gate full-table construction is SAT, corrupted construction UNSAT.
- Started full-table localSAT repair around the stochastic10-error candidate, freeing5gate descriptors per trial and fixing the other14. Each trial gets3000conflicts; total bound600seconds. Results are search evidence only.

## Stop after lease loss

2026-11-25T14:40:55.365348+00:00 — root reported HTTP410 and ordered an immediate stop. Both SAT processes were interrupted with SIGINT. No witness and no UNSAT certificate was found. Existing full logs, the spurious30-row candidate, row list, source, and selftest output are copied beside these notes for preservation. Search work is paused pending a new live lease.
