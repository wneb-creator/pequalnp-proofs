# L-meta-1031 search checkpoint, round 2

These are external finite searches, not Lean certificates or a solution of L-meta-1031. This directory supplements the independently reviewed first snapshot in `../search`; it contains all current program sources and graph inputs, plus complete new or changed solver logs and witnesses. Every included run has finished. Later runs remain in scratch until another checkpoint. Source filenames and graph names identify matching logs. The original Z3 executable and completed generated CNFs were deleted for disk space; Python bindings, source encodings, full solver stdout/stderr, and witnesses remain available. CNFs are reproducible from sources.

## New encoding changes

`counter_count_only.py --disjoint` counts only one gate type while the dual type is free. Each charged gate has two arbitrary free-cone subsets over inputs and previous charged outputs. Constants are removed and fanin subsets are nonempty and disjoint. For AND counting, overlapping sources can be pulled into a free OR term by distributivity: `(T OR A) AND (T OR B) = T OR (A AND B)`; propagate the free expression into later cones. The OR-counting argument is dual. Gates with an empty remaining side can be eliminated, and unused charged gates pad to the requested upper bound (graphs here have at least two inputs). Automorphisms reduce the first subset-pair choices. The original unrestricted mode is retained. This normalization has been independently discussed, but is not kernel-checked.

`counter_sat.py --dominance` excludes a gate dominated by an earlier source on the graph-decisive test rows: the source is pointwise at most the gate and agrees with it on every positive edge row. Replacing the gate by that source preserves positive tests and cannot turn a negative test true, yielding a smaller valid circuit. Each gate must also be true on some positive edge row. This pruning applies to a minimum total-size circuit. It is not used in the padded count-only or auxiliary-output models. Other total-size normalizations are described in the first snapshot; no proof of their completeness is encoded in Lean.

Graph function equality uses all edge pairs and all maximal independent sets. Monotonicity makes those tests decisive. SAT witnesses are additionally checked on all input assignments by the programs. A dirty minimum would not refute the posted existential statement: another minimum might have the requested star profile.

## New results

* Count-only disjoint encodings: C8 with at most 6 OR gates UNSAT (6.22 seconds); Theta(2,3,3) with at most 6 OR gates UNSAT (34.43 seconds); Petersen with at most 5 AND gates UNSAT (28.09 seconds).
* Positive controls C5 with 3 AND gates and C5 with 4 OR gates are SAT; both included witnesses pass full truth-table checking. The 3-AND witness uses dirty intermediate gates but expands to 10 total gates, so it is not a minimum-total-size counterexample.
* Fano incidence with at most 6 AND gates: UNKNOWN at the 120-second wall limit.
* C6 with 8 total gates and a dirty AND: UNSAT with dominance pruning (1.46 seconds), agreeing with the earlier unrestricted result.
* Dirty-at-canonical-cost queries on seven cyclic seven-vertex graphs, Theta(2,3,3), and the bowtie of two C5s: UNKNOWN at their wall limits. Several seven-vertex runs shared CPU; their short CPU times do not support a hardness conclusion.
* Once-subdivided K4 (10 vertices, 12 edges, minimum vertex cover 4): both total size 14 with dominance and at most 10 OR gates with free AND gates were UNKNOWN at 120 seconds. Canonical star construction has size 15.

SAT, UNSAT, and UNKNOWN are reported exactly as external solvers returned them. No below-canonical circuit, graph counterexample, or kernel-checked lower-bound certificate has been found. No source in this directory is a proof submission.
