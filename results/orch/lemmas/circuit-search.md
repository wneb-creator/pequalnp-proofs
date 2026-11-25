# Circuit search: L-meta-2732

Started 2026-11-25 around 05:28 UTC. Scratch directory:
`/tmp/oec/pequalnp-pilot-70/circuit-search/`.

## Verified setup

- Heawood target has 21 minimal true rows and 37 maximal false rows (21 of weight 4, 14 of weight 5, 2 of weight 7).
- The 58-row vectors match the existing reduction `R_meta_2732_3.lean` (independent check by sat_review).
- All 65 canonical first-two-gate wiring patterns match the 336-element Heawood automorphism group (independent check by sat_review).
- Built official CaDiCaL source from GitHub in scratch. Version `3.1.0`, commit `e4d9bd93af444c6575a908a24da2c4130cb2a1c7` of `arminbiere/cadical`. Configured with plain `./configure`, compiled by `make -j4`. Compiler: `g++ (Debian 14.2.0-19) 14.2.0`; generated flags: `-Wall -Wextra -O3 -DNDEBUG`, with include paths `-I../build -I../src`. No external Python solver package was installed.
- `synthesize.py` constructs a one-hot fan-in CNF for AND/OR DAGs. The `sat_review` agent checked the mux, operation, and one-hot clauses independently.
- Added sound boundary nontriviality, adjacent-independent lexicographic ordering, and liveness constraints. A `--minimal` variant additionally excludes domination by earlier wire boundary signatures. The minimal variant only covers actual size-26 minimal networks, not padded smaller ones; the general search remains active independently.

## Checked baseline outside Lean

The fixed 27-gate star network satisfies the CNF, and `decode.py` independently verified all 16,384 input assignments. The explicit network is in `star27.json`; it was sent to formalization for a Lean baseline.

Its first two gates are OR(0,1), OR(0,2), canonical score 227. Its packed gate codes are:

`[4160,4224,4352,4225,4417,4290,4355,4995,5188,5125,5317,5062,5254,5382,1351,1608,1673,1482,1739,1548,1421,5980,6366,6431,6496,6561,6626]`

## Active searches

- `heawood26.cnf`: general 26-gate network, 7,381 variables and 201,740 clauses. Complete solver log: `heawood26-solve.log`. Initial wall budget 1,800 seconds.
- `minimal26.cnf`: liveness and semantic non-domination variant, complete solver log `minimal26-solve.log`. Initial wall budget 1,800 seconds. Paused at 05:34:31 UTC at root's request to reserve CPU for Lean builds; pause time is not search evidence.
- `live-dirty26.cnf`: prepared but not yet launched. Adds liveness and the necessary existence of an AND gate accepting some maximal false row (a consequence of the existing pair-clean lower bound for size26).

No 26-gate witness or exhaustive nonexistence certificate has been found yet.

At 05:40 UTC the general search had about 2 million conflicts and 253 CPU seconds, still running without a verdict.

## Induced-subgraph round

At 05:43:44 UTC the general solver was paused for a bounded exploratory round. The generic graph encoding was independently reviewed; fixed baseline circuits passed SAT plus full truth-table checks for every case.

- Three retained left vertices, orbit `(0,1,2)`: sought 10 gates; UNKNOWN after 60 seconds.
- Three retained left vertices, orbit `(0,1,3)`: sought 10 gates; UNKNOWN after 60 seconds.
- Four retained left vertices, orbit `(0,1,2,3)`: sought 14 gates; UNKNOWN after 120 seconds.
- Four retained left vertices, orbit `(0,1,2,5)`: sought 14 gates; UNKNOWN after 120 seconds.

These are sufficient subproblems: a one-gate improvement over their standard star circuit extends to a 26-gate full circuit by appending omitted stars. UNKNOWN is not a nonexistence claim. Complete logs and pause timing are in `subgraph-round.log` and `subgraph-round.json`.

The general solver resumed at 05:49:47 UTC after a pause of 362.57 seconds.

Also prepared a phase-guided CaDiCaL API driver (`phased.cpp`) and a canonical 26-gate network missing exactly one target edge (`near26.json`). The API driver passed a fixed-star SAT smoke test; its longer run is recorded below.

The API driver compilation uses `g++ -std=c++11 -O2 -I cadical/src phased.cpp cadical/build/libcadical.a -o phased` (paths resolved under the scratch search directory).

## First full-run result and rotation

The original general run ended at 06:02:13 UTC with UNKNOWN: 1,800 real seconds, 1,104.63 CPU seconds, 6,214,151 conflicts, and 100.54 MB maximum resident memory. Its 362.57-second pause is included in the real time. No SAT model or UNSAT certificate was produced. Complete log: `heawood26-solve.log`; metadata: `general26-result.json`.

To reproduce the original general CNF with the current generator, use `--gates 26 --no-liveness`. Byte equality was checked; SHA256 is `aea6b6c49eef86d3f33291c451834688d0afe697c24e2ff19832cf9fbc44875e`.

After root renewed the lease at 06:02:08 UTC, the phase-guided live+dirty search started around 06:02:31 UTC with a 1,800-second wall budget. It still allows repeated tail operands and smaller circuits padded by output copies. Complete log: `guided26-solve.log`; hashes and command: `guided26-run.json`.
