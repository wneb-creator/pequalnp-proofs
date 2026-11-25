# Constructive search for L-meta-2732

Started 2026-11-25, assigned by root; no independent desk calls.

The standard construction has seven three-neighbor stars. Each star needs two OR gates and one AND gate; joining the seven stars needs six OR gates, for 27 gates total. The assigned bound is 26. The graph is the incidence graph of the Fano plane.

Root reports the existing `L_meta_1983` lower bound applies to circuits with no AND in the cone of another AND. Therefore a possible 26-gate witness must exploit nested AND gates. This does not establish impossibility for the assigned circuit class.

Primary-source search, read 2026-11-25: Jukna's *On Graph Complexity* (https://eccc.weizmann.ac.il/eccc-reports/2004/TR04-005/index.html) and *Disproving the single level conjecture* (https://eccc.weizmann.ac.il/report/2005/021/) distinguish graph representations/formulas/single-level models from unrestricted monotone circuits. I have not found a source proving a 27-gate lower bound for this Heawood function. That putative lower bound remains UNVERIFIED.

The independent computational route uses all 21 minimal true rows and all 37 maximal false rows (58 total). Since the candidate gates are monotone, agreeing on these extrema is sufficient for full truth-table equality. Every row signature fits in one 64-bit word.

Scratch source: `/tmp/oec/pequalnp-pilot-70/constructive/search.cpp`. It performs bounded stochastic synthesis of 26 gates, seeded by deleting one gate from random 27-gate star circuits. It uses neutral drift, annealing, and adaptive error-row penalties. All source choices allow nested AND gates. Complete run output: `constructive/run1.log` in job scratch. No witness yet; fitness one is easily attained by omitting one required edge.

A second algorithm (`constructive/neutral.cpp`) uses 54 physical gate slots with 27 initially active gates, leaving free intermediate slots for neutral circuit rewrites. It maintains exact agreement on the 58 rows while seeking an active cone of at most 26 gates. This explores a different fitness landscape from the first fixed-size, near-correct search.

No Lean file changed, compiled, or claimed as a proof by this strategy.

## Run log

- Fixed-size stochastic run 1: 600 seconds, 1,573,204,800 mutations, 6,292 restarts, best result one incorrect extremal row. No witness. Complete log `constructive/run1.log` in job scratch.
- Neutral-rewrite smoke run: 30 seconds, 33,483,328 mutations, 33 restarts, 15,656,236 accepted changes, 1,939 changes to the active cone. Best active gate count 27. An independent Python evaluator verified its saved 27-gate candidate on all 16,384 assignments, with zero errors.
- Neutral-rewrite run 1 started around 05:41 UTC for a 600-second budget after root confirmed lease renewal at 05:40:04 UTC (expiry 06:00:04 UTC). It uses 54 physical gate slots; temporary active gate counts up to 32 are permitted during annealing. Every accepted candidate agrees exactly on all 58 extremal rows. It also records any 27-gate candidates containing AND gates that accept false inputs of weight at most two. Full log `constructive/neutral-run1.log`.
- Neutral-rewrite run 1 finished around 05:51 UTC: 600 seconds, 1,110,749,568 mutations, 222 restarts, 513,339,670 accepted changes, 741,217 active-cone changes. Best gate count remained 27. No 26-gate witness and no 27-gate pair-dirty candidate were recorded. Long stochastic runs paused at root's request to free CPU for CEGIS.
- Independently evaluating the fixed-size phase's saved near-witness showed 47 incorrect assignments out of 16,384. Its sole missing minimal edge is (5,12); it is not a valid proof witness.
- `constructive/neutral-v4` is prepared with simultaneous semantic domination folding. If an earlier wire is greater on every positive row and smaller on every negative row, replacing a gate by that wire preserves output correctness by monotonicity. The normalizer rewires all fanouts together and removes dead gates when counting the active cone. A two-second smoke run made 688,128 mutations without a normalization assertion failure; no long run has been started for this variant.

The first phase did not exhaust any finite search space; its negative result is only a heuristic search outcome, not evidence of nonexistence sufficient for a theorem.

## Smaller sufficient synthesis problems

Retain k vertices on the left and all their incident edges. The obvious circuit has 4k−1 gates. A circuit with 4k−2 gates for that subfunction extends to the full function in 26 gates: append the omitted 7−k three-edge stars (three gates each), then join those outputs to the subfunction using 7−k OR gates. This is only a mathematical sufficiency argument so far; prefix canonicalization remains the same separate task as for any found witness.

`constructive/induced_subproblems.py` prepared six relabeled instances in scratch. Every stored baseline was checked against its full truth table. Each JSON contains essential input labels, edges, extrema, the baseline, and the desired bound.

| Instance | Inputs | Positive rows | Negative rows | Desired gates |
| --- | ---: | ---: | ---: | ---: |
| k3_collinear | 10 | 9 | 8 | 10 |
| k3_noncollinear | 9 | 9 | 8 | 10 |
| k4_complement_collinear | 10 | 12 | 12 | 14 |
| k4_complement_noncollinear | 11 | 12 | 15 | 14 |
| k5 | 12 | 15 | 22 | 18 |
| k6 | 13 | 18 | 30 | 22 |

The k4 complement-of-line case is the incidence graph of K4: four retained points and six lines, each line joining one pair of retained points. This identification follows directly from the listed edges. No improved circuit has been found for it.
