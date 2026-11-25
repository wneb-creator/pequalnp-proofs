# Circuit search: L-meta-2732

Started 2026-11-25 around 05:28 UTC. Scratch directory:
`/tmp/oec/pequalnp-pilot-70/circuit-search/`.

## Verified setup

- Heawood target has 21 minimal true rows and 37 maximal false rows (21 of weight 4, 14 of weight 5, 2 of weight 7).
- The 58-row vectors match the existing reduction `R_meta_2732_3.lean` (independent check by sat_review).
- All 65 canonical first-two-gate wiring patterns match the 336-element Heawood automorphism group (independent check by sat_review).
- Built official CaDiCaL source from GitHub in scratch. No external Python solver package was installed.
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
