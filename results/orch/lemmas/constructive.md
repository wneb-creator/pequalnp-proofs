# Constructive search for L-meta-2732

Started 2026-11-25, assigned by root; no independent desk calls.

The standard construction has seven three-neighbor stars. Each star needs two OR gates and one AND gate; joining the seven stars needs six OR gates, for 27 gates total. The assigned bound is 26. The graph is the incidence graph of the Fano plane.

Root reports the existing `L_meta_1983` lower bound applies to circuits with no AND in the cone of another AND. Therefore a possible 26-gate witness must exploit nested AND gates. This does not establish impossibility for the assigned circuit class.

Primary-source search, read 2026-11-25: Jukna's *On Graph Complexity* (https://eccc.weizmann.ac.il/eccc-reports/2004/TR04-005/index.html) and *Disproving the single level conjecture* (https://eccc.weizmann.ac.il/report/2005/021/) distinguish graph representations/formulas/single-level models from unrestricted monotone circuits. I have not found a source proving a 27-gate lower bound for this Heawood function. That putative lower bound remains UNVERIFIED.

The independent computational route uses all 21 minimal true rows and all 37 maximal false rows (58 total). Since the candidate gates are monotone, agreeing on these extrema is sufficient for full truth-table equality. Every row signature fits in one 64-bit word.

Scratch source: `/tmp/oec/pequalnp-pilot-70/constructive/search.cpp`. It performs bounded stochastic synthesis of 26 gates, seeded by deleting one gate from random 27-gate star circuits. It uses neutral drift, annealing, and adaptive error-row penalties. All source choices allow nested AND gates. Complete run output: `constructive/run1.log` in job scratch. No witness yet; fitness one is easily attained by omitting one required edge.

A second algorithm (`constructive/neutral.cpp`) uses 54 physical gate slots with 27 initially active gates, leaving free intermediate slots for neutral circuit rewrites. It maintains exact agreement on the 58 rows while seeking an active cone of at most 26 gates. This explores a different fitness landscape from the first fixed-size, near-correct search.

No Lean file changed, compiled, or claimed as a proof by this strategy.
