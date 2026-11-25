# Multi-level circuit research, 2026-11-25

These are research notes, not a proof of L-meta-2056 or a circuit lower bound.

Read on 2026-11-25: Stasys Jukna, *Disproving the Single Level Conjecture*, author-hosted original paper, <https://web.vu.lt/mif/s.jukna/ftp/single1.pdf>.
The paper distinguishes representing a graph on two-element inputs from computing its quadratic Boolean function on every input. Its explicit separations use saturated extensions, which add edges within the two parts of a bipartite graph. Consequently those constructions do not directly yield a circuit for the bipartite projective-plane function here. The paper also distinguishes total gate count from AND-gate count; an argument about one must not silently be applied to the other.

Read on 2026-11-25: Kazuyuki Amano and Akira Maruoka, *The Monotone Circuit Complexity of Quadratic Boolean Functions*, publisher abstract, <https://doi.org/10.1007/s00453-006-0073-0>. The abstract reports an exponential separation between single-level and general conjunctive complexity. Full text was not accessible through the browsing tool. No exact finite construction or constant from that paper has been imported into our search.

UNVERIFIED: any claim that this projective-plane function requires at least 13 AND gates in arbitrary multi-level monotone circuits. No applicable theorem establishing that claim has been found. It is not an authorized constraint in the general SAT searches.

At the 17:09 UTC research checkpoint, the independently checked exact seeds use at least 64 gates. The 63-gate search candidates are incomplete. A finite SAT timeout is recorded as UNKNOWN, not as nonexistence. The compiled finite-test completeness bridge establishes that a monotone circuit passing every posted test computes the full incidence function, so a genuinely correct 63-gate candidate cannot exploit omitted larger inputs.

The next structural experiment uses two AND intermediates that admit false inputs before subsequent filtering. Existing single-intermediate seeds can lose this structure during local search and return to a conventional star circuit. Keeping such structure in a search population is a heuristic only; every reported witness must still pass all boundary rows and the Lean checker.
