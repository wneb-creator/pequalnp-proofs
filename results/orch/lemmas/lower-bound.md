# L-meta-2732 lower-bound strategy

Started 2026-11-25 around 05:28 UTC. Root owns the lease and submission.

## Established repository facts

- The standard star circuit has 27 gates; this is only an upper bound for unrestricted circuits.
- `lean/PEqualNP/Outside/L_meta_1983.lean:842`, `pairCleanBound`, proves that a circuit for a C4-free graph with every AND gate rejecting every false input of weight at most two has size at least `edge_count + vertex_cover_number - 1`.
- For Heawood, the edge count is 21 and vertex-cover number 7. The same file proves the 27-gate bound for circuits with no nested AND gates. Consequently a 26-gate circuit needs a nested AND and an AND accepting a false input of weight at most two.
- Existing unrestricted bounds in `L_meta_1483.lean` and `L_meta_5670.lean` give 20 gates, not 27.
- All three live reductions for this gap already exist: `R_meta_2732_3`, `_427`, `_773`. The first contains 58 extremal input rows and 65 canonical first-two-gate patterns.

## New checked partial

`DirtyFilter.lean` (59 lines) compiled on 2026-11-25 around 05:34 UTC using `lake env lean`, exit 0 and empty diagnostic output. The complete log is `/tmp/oec/pequalnp-pilot-70/lower-bound/dirty-filter-lean.log`.

Its main lemma `safeFilter_doubleStar` says: for a rectangle-free bipartite relation, if a union of selected rows and selected columns inside A×B consists only of edges, and both A and B have at least two vertices, the selected pairs lie in one row together with one column. Supporting lemmas prove uniqueness of selected rows and columns. This is a generic combinatorial building block, not a proof of the assigned gap or a circuit lower bound. Independent review by `sat_review` passed.

## Open obstruction

Conjectural route: a circuit with only one pair-dirty AND can be converted without increasing size to a pair-clean circuit; this would force at least two pair-dirty ANDs in any 26-gate witness. Filtering a raw dirty rectangle is controlled by the new double-star lemma. Two unresolved issues are previously computed clean-edge contributions inside its operands and gate accounting when the dirty gate feeds several later filters. No claim that the normalization theorem is true has been established.

The finite geometry is now completely checked: `DirtyFilterOverlap.lean` handles overlapping supports, and `DirtyFilterCover.lean` (203 lines, containing all previous helpers unchanged) proves `safeFilter_coverTwo`. For any symmetric triangle-free C4-free relation and arbitrary supports A,B,S, if every pair satisfying Ahit AND Bhit AND Shit is an edge, all such pairs have a vertex cover of size at most two. No apartness, bipartition, cardinality, or nonemptiness assumptions remain. Both files compiled with exit 0 and empty logs, and `sat_review` independently approved their mathematics and format. Logs: `dirty-filter-overlap-lean.log`, `dirty-filter-cover-lean.log` in the lower-bound scratch directory.

This does not by itself count circuit gates. Existing pair-clean accounting separates gates with large singleton support from gates with at most one singleton: `L_meta_1983.cover_half` bounds the cover number by one plus the number of small-support OR gates; `edge_finset_gate_bound` bounds edges by AND gates plus large-support OR gates. A sole dirty AND can break these separate inequalities, so the extension needs combined accounting. Dirty rectangles appear to introduce slack because their first clean filters consume gates, but preservation under shared precursor OR computations is not proved.

## Auxiliary finite search prepared

`/tmp/oec/pequalnp-pilot-70/lower-bound/pairdirty_synthesize.py` extends the reviewed synthesis encoding with 85 additional negative rows: zero, 14 singletons, and 70 nonedge pairs. Each gate has a flag equivalent to being an AND that accepts one of these rows, and at most one flag may hold.

The 26-gate instance has 143 distinct rows, 14,063 variables and 451,723 clauses. Exact files: `pairdirty1-26.cnf`, `pairdirty1-26.map.json`; complete generation log `pairdirty1-generate.log`. Independent review checked all flag/cardinality semantics and the 85 row additions; the sanity log is `/tmp/oec/pequalnp-pilot-70/sat-review/pairdirty-sanity.log`. Root requested preparation only until a CPU slot is free. An UNSAT result would address only this restricted search and would still need a Lean certificate bridge.

## Research caveat

Read 2026-11-25: Stasys Jukna, *Disproving the single level conjecture*, https://eccc.weizmann.ac.il/report/2005/021/ . It shows that assuming all quadratic functions have comparably small single-level circuits is invalid in general. No same-size normalization for the bipartite C4-free Heawood case was found. Such a normalization remains UNVERIFIED here. The ECCC PDF text extraction was corrupted; only the readable landing-page abstract and repository proofs support the statements above.

## Incremental CEGIS route

Root reassigned the search preparation around 05:47 UTC. The driver `lower-bound/cegis.cpp` links the existing CaDiCaL static library. Preparation script `prepare_cegis.py` asserts that the final 58 clauses are exactly the target output units and removes only these clauses. All gate-evaluation constraints on all 58 rows remain.

The initial query constrains all 21 positive rows and the two bipartition negative rows (row indices 21 and 57, masks 127 and 16256). The same solver retains learned clauses between calls. After each model, the driver decodes the gate selectors and independently evaluates all 58 rows, checking agreement with the encoded output variables. It adds output units for all new violations. A full candidate is evaluated on every one of the 16,384 inputs before a witness file is written.

Compilation passed. Two smoke tests passed: a fixed exact 27-gate circuit immediately yielded a fully verified witness; a fixed complete-bipartite 26-gate overapproximation satisfied the initial 23 rows, then produced 35 violations, and the same solver returned UNSAT after those units were added. Complete logs are `smoke27.log` and `smoke26complete.log`. The general base is `cegis26.cnf` with matching `cegis26.meta` (201,682 clauses, 7,381 variables). No general solver run had started when this entry was written; root controls the two available CPU slots and lease renewals.

### CEGIS refinements, 06:07 UTC

The first run added all 35 violated rows at once and was stopped after 117 seconds. The second run adds just one violated negative row (largest weight, then largest minimum Hamming distance to active negative rows). It found SAT models for 23, 24, and 25 active rows in 4, 29, and 102 seconds respectively, then spent several minutes on the 26-row query. Complete logs and candidate JSON files remain in scratch.

A new warm driver, `cegis-warm.cpp` with `cegis-warm.hpp`, addresses this search overhead. It builds the maximal bipartite supergraph consistent with all active false rows, groups right columns with identical neighborhoods, shares raw OR sums, preserves canonical prefix OR(0,1), OR(0,2), and lexicographically topologically orders the remaining gates. The first seven partial graphs use 14, 15, 16, 19, 21, 24, and 24 gates; the next constructed graph uses 27. Each candidate is checked against every active row before becoming a heuristic phase assignment. It imposes no circuit restriction. Thirty-second solve slices retain all learned clauses and respect one overall deadline.

All seven phase candidates were independently fixed into the full general CNF plus the corresponding active output units. Each was SAT, then correctly UNSAT when a violated output unit was added. Fixed exact27 and complete-bipartite smoke tests also passed. Logs: `warm-fixed-0.log` through `warm-fixed-6.log`, `smoke27-warm.log`, `smoke26complete-warm.log`, and `warm-check.log`. The new driver awaits independent review and a fresh lease beat before restart.

### Homogeneous-shadow obstruction (mathematical only)

Independent review of the constructive agent's argument supports this strengthening: a constant-free 26-gate Heawood witness must omit at least three target squarefree degree-two monomials from its formal arithmetic polynomial. If the proper homogeneous shadow loses only one gate, that gate is the unique unequal-degree OR. Its earlier high-degree operand is homogeneous, remains productive, has degree exactly two, and reaches the shadow output through only OR gates. Hence it already implies the shadow output and restoring the deleted OR cannot change Boolean behavior, a contradiction. A proper shadow therefore removes at least two gates. Deleting at most two Heawood edges leaves a perfect matching (there are three edge-disjoint perfect matchings), and the pair-clean bound forces the shadow to have at least 25 gates. The formal degree/pruning and graph-cover bridge is not yet implemented; no Lean theorem claims this obstruction.

### Reviewed warm run and live hints, 06:16 UTC

Independent review passed the final warm driver, including temporary selector/op assumptions. Warm UNSAT and UNKNOWN are only candidate failures; the driver always retries unconstrained before any general UNSAT claim. Smoke tests deliberately force a warm UNSAT against a fixed exact27 circuit and then observe unconstrained SAT with exhaustive validation. The refinement distance now ignores the two bipartition rows.

The warm run began at 06:12:00 UTC, PID8734, log `cegis26-warm-run.log`. It advanced from 23 to 30 active rows in 59 milliseconds, using 14, 15, 17, 18, 21, 23, and 26-gate partial witnesses. The next maximal-supergraph construction uses 27 gates. At this point the allowed pair graph has six exact Heawood columns and column13 unrestricted, for 25 allowed edges.

A separate weighted biclique-cover helper `biclique_warm.py` found a 26-gate partial witness for these 30 rows in about 0.1 seconds. It covers only the 21 required edges, using bicliques allowed by the active negative rows; unnecessary allowed edges need not be generated. The candidate also passes the actual canonical CNF when its gates are fixed. Files: `biclique30.json`, `biclique30.hint`, `biclique30-fixed.log`. It violates 11 of the full58 boundary rows and is not a full witness. Current refinement next selects row46/mask8297, after which the allowed pair graph is exactly Heawood; the weighted cover search then exhausts its cost26 model with no candidate (22,378 nodes).

The new `cegis-hints.cpp` / `cegis-hints.hpp` extension has independently passed review. It reads an optional plain gate-list hint at each solve slice boundary, verifies gate shape and every active row, and tries it under temporary assumptions. Rejected, malformed, UNSAT, or UNKNOWN hints cannot produce a general UNSAT claim. Full model decoding and all16,384-input validation remain mandatory. Smoke tests cover hint acceptance, failed-hint-to-exact27-SAT fallback, and malformed hint rejection. It allows future external candidates without discarding learned clauses; root controls its restart and lease beat.

### Adjacent-center geometry checked

`TripleFilterCross.lean` compiled with exit0 and empty diagnostics. Its pure propositional theorem says that if two pairs each hit all three supports A,B,S, one of the four cross pairs also hits all three. Independent review passed, including exhaustive enumeration of all4,096 membership patterns. This is specific to three supports; four supports admit an induced matching of two pairs.

`DoubleStarCenters.lean` then proves that two distinct nonadjacent cover vertices in a loopless symmetric C4-free graph with this cross-edge property cannot both have two neighbors. `DoubleStarAdjacent.lean` upgrades a nonempty two-vertex cover to a cover by the endpoints of an actual edge. Both compiled with exit0 and empty logs and passed independent review; finite five-vertex graph enumeration supplied a separate sanity check.

The standalone assembly `DirtyFilterAdjacent.lean` includes the previously checked helpers unchanged and the final `safeFilter_adjacentCover` bridge. For any triangle-free C4-free relation R and a nonempty pair family accepted by three OR filters, if every accepted pair is an R-edge, every accepted pair is incident to one endpoint of a fixed R-edge. The whole assembly compiled with exit0 and empty `dirty-filter-adjacent-lean.log`. Independent review of the final bridge is pending at this writing. In a cubic graph this implies at most five distinct surviving edges, since the two degree-three stars share their center edge. The numerical edge count and any circuit gate-count lower bound are not separately formalized.

The live-hint CEGIS run began06:16:37UTC (PID8981) and advanced to31 active rows in52 milliseconds. Its 31-row query allows exactly the Heawood pair graph, but **no satisfying26-gate circuit for that query has been found**. The last actual circuit is the30-row biclique candidate with extra allowed pairs. Complete log: `cegis26-hints-run.log`; arbitrary multilevel candidates can be supplied through `cegis26-hints.hint` and are checked before use.

### Completed solver phases and storage, 07:04 UTC

The live-hint CEGIS phase finished UNKNOWN after 1,200.308 seconds wall time and 1,135.75 seconds CPU, with peak RSS121.22MB and8,309,565 conflicts. It reached31 active rows but found no SAT model for that query. Its last actual26-gate model satisfies30 rows and still has extra pairs.

The reviewed at-most-one pair-dirty AND instance with first-dirty prefix clauses ran from06:37:13.704 to06:57:13.769UTC and finished UNKNOWN. It used1,200.065 seconds wall time and992.343 seconds CPU, with peak RSS130,460KiB. Complete output and status are `pairdirty1-first-26-run.log` and `pairdirty1-first-26-status.json`. The exact timeout line is `c UNKNOWN`. The incomplete binary DRAT was483,164,081bytes; root authorized lossless gzip compression, decompression was verified against the original SHA256, and only then was the uncompressed scratch copy removed. The remaining `.drat.gz` is287,541,453bytes. It is explicitly not an UNSAT certificate and is excluded from git. Full hash/size provenance is in `pairdirty1-first-26-proof.json`.

Both CPU slots are now assigned by root to circuit_search. No further solver was launched here.

### Checked accounting and robustness pieces

`DirtyMixedSupport.lean` and `MixedSupportOwners.lean` compiled with empty logs and passed independent review. Rejected outer pairs force one support to contain both middle endpoints. In a triangle-free graph, such a support cannot cross into any nonempty support. If a mixed support contains the endpoints of an accepted center edge, loop rejection splits those endpoints between the two other supports, and safety places those entire supports inside opposite center neighborhoods.

`GoodOrEdgeBound.lean` strengthens the library edge budget by charging only large-support OR gates with a common graph neighbor. `GoodOrGrowthBound.lean` further excludes OR gates whose support equals either child's, using the unary DAG branch. Both compiled with empty logs and passed independent review. These are actual inequalities, but their integration with a dirty gate's source accounting remains unfinished.

`RobustMatchingCounts.lean` verifies three explicit edge-disjoint perfect matchings and proves that any graph containing at least19 of the21 indexed Heawood edges has edge-count plus vertex-cover size at least26. It compiled with an empty log and passed independent review. The formalization agent combined it with its generalized ambient/target pair-clean bound and two-gate pruning in `OneDirtyLoss.lean`, then removed the liveness premise in `LiveLoss.lean`; these compiled and were independently reviewed. Consequently, a26-gate full witness with one exceptional dirty slot must reject at least3 indexed Heawood edge pairs when that slot is forced false. This is now a Lean-checked necessary condition, not just a paper argument.

### Three-loss CNF prepared

`add_pairdirty_loss3.py` appends a shared-selector zeroed evaluation on only the21 positive rows to the reviewed `pairdirty1-first-26` instance. It preserves all original variable IDs. A flagged gate's new output is forced false; every other gate follows the ordinary AND/OR recurrence. The final zeroed outputs must contain at least3 false values, encoded by210 clauses, one for each omitted pair of positions. No nontriviality, liveness, domination, or prefix-minimality restriction is imposed on the zeroed evaluation.

Prepared files `pairdirty1-loss3-26.cnf/.map.json/.delta.cnf` have15,701 variables and499,305 clauses, with46,620 appended clauses. The source and necessary-condition justification have been sent for independent review; no solver run has started. Small-case validation is saved separately in `pairdirty-loss3-validation.log`.

### Additional geometry and primary-source check, 07:13 UTC

`CommonSingletonFilter.lean` compiled with exit 0 and an empty log, and constructive independently reviewed it. Two distinct points shared by dirty operand supports A and B force the union of every safe filter support to have size at most one. A second lemma shows that a support containing two neighbors of p and one nonneighbor cannot have any common-neighbor owner in a C4-free relation. These are local geometry facts, not a complete circuit accounting argument.

Read 2026-11-25: Jukna's readable author PDF, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf , was available after the ECCC extraction failed. Its exact-function counterexamples use saturated bipartite graphs, adding cliques within both parts. The K2,2-free lower bound discussed there is explicitly for single-level circuits. The separate primary paper https://web.vu.lt/mif/s.jukna/ftp/dagstuhl2006.pdf defines graph representation using only cross-part pairs; this is weaker than exact computation of our edge-existence function. No sharp unrestricted Heawood bound or same-size normalization was found. Current status of the historical general open problems remains UNVERIFIED; no claim is made that a 2006 open problem is still open in 2026.

### Reviewed loss3 encoding and accounting refinements, 07:21 UTC

The SAT reviewer independently passed the loss3 extension. It reconstructed all 46,620 added clauses, checked preservation of all 452,685 original clauses and original variable IDs, verified all 32 conditional-operator assignments and 1,562 final-output patterns with zero through three misses. There are exactly 1,638 fresh variables. No solver has been launched for this instance. Independent log: `sat-review/loss3-independent-review.log`.

`GoodOrSmallAndBound.lean` compiled with exit 0 and an empty log, and constructive independently reviewed its exact diff. The large owned strict-growth OR edge budget requires only that every AND's singleton support have size at most one, rather than be empty. All other cross-support and edge-cover premises remain explicit.

`OwnerOverlapBudget.lean` compiled with exit 0 and an empty final log. It proves that a shared element in two distinct owner sets gives one unit of savings in the union cardinality, then combines that with local root/paid bounds. In particular a total root budget A+1 is sufficient for a target bound A+O when the duplicate edge is present. Independent review is pending; the mapping from the dirty circuit to these abstract owner sets remains an explicit outstanding obligation.

### Live-DAG fanout credit checked, 07:24 UTC

`OwnerOverlapBudget.lean` independently passed review. `LiveDagCredit.lean` also compiled with exit 0 and an empty final log and passed independent review: if all live nonroots have an incoming parent arc, leaves have no children, and internal vertices have at most one plus their paid indicator many children, then an incoming arc at a root or two distinct incoming parents at any vertex implies leaves+1<=roots+paid. The repeated vertex need not be the exceptional leaf. Ordered-pair arcs count distinct parents correctly.

`LiveDagSupportBound.lean` extends that unchanged source with acyclic label propagation and a single leaf label of size at most two, all others at most one. It proves the union of all root labels has size at most roots+paid. It compiled first attempt with exit 0 and an empty log, and constructive independently reviewed the assembly. The actual circuit-to-selected-DAG bridge remains unproved here; this result supplies its cardinality endpoint only.

### Restart and concrete path bridge, 07:40 UTC

`TwoPathFork.lean` and `CoverStarOrOuter.lean` compiled with exit 0 and empty logs before the restart and passed independent review. The first extracts distinct parents of a shared child from two finite paths with a common endpoint and cross-start exclusions. The second turns a two-center cover into either a one-center cover or two accepted outer edges with their outer pair rejected.

The environment restarted around 07:28 UTC. `FirstMixedGrowth.lean` had started checking and its log is empty, but its process status was lost before an exit code was observed. It remains prepared/unconfirmed, not reported as checked. Mathematical independent review passed. It identifies a large strict-growth ownerless OR by taking the first support containing an edge, under small input/AND supports and triangle-freeness.

`SelectedDirtyPaths.lean` is prepared and deliberately uncompiled while the focused cache is restored. It reuses the checked path-merge helper unchanged and adds generic descending selected-path extraction, attachment of a D=false clean consumer, two-consumer fork extraction, and the maximal-live-D argument proving that a live dirty label forces a clean transition. The generic path predicate can also encode acceptance plus a missed cover label, supporting the concrete escape trace. Formalization owns the D=false clean frontier and selected-parent construction; constructive owns the semantic cover plan. No complete one-dirty bound or unrestricted lower bound is claimed.

### Focused-cache recheck completed, 07:47 UTC

After the focused cache was recovered, the serial Lean slot passed from formalization to lower_bound. `FirstMixedGrowth.lean` compiled with confirmed exit 0 and an empty `first-mixed-growth-lean-after-restart.log`; its earlier unknown restart status is now resolved. The unchanged source had already passed independent mathematical and format review.

`SelectedDirtyPaths.lean` also compiled with confirmed exit 0 and an empty `selected-dirty-paths-lean.log`. The only correction was explicitly typing the first existential binder in two signatures. All five appended path/transition lemmas are now checked; mathematical interface review had passed, and final independent artifact review is pending. Source SHA256: `77ccf0da4bc6d6e05f2d81f822b2a812bec2c1b06b9044bb798c5072e2022190`. No Lean process remains active on this agent's side.

Formalization reused the generic path extraction in its checked `AcceptingPath` assembly, obtaining a concrete selected acceptance trace from a minimal accepting root, with earlier clean boundary escapes excluded by minimality. These are necessary bridge components, still not a complete proof of the posted unrestricted circuit bound.

### Concrete selected labels and root coverage, 07:55 UTC

`SelectedLabels.lean` now compiles with exit 0 and an empty `selected-labels-lean-4.log` (76 lines). It constructs the labels explicitly: the distinguished dirty wire receives Z, base wires receive their singleton supports, and every other wire receives the union of its earlier selected-child labels. Checked interface lemmas give base/dirty equations, child-label inclusion, internal union coverage, and size at most one for every non-dirty leaf. Constructive reviewed the mathematical interface; final artifact review is pending. Source SHA256: `0ac444f84ac4286d583948d85763b1154e2e042dddcca306be22abaccabfda23`.

Lower_bound independently reviewed formalization's `RootCover.lean`, stable SHA256 `d56457c7b36fac72b1117bfd4e20a5709516f36a6137abd201699da73fc65107`, and passed it after the live-set correction. Its raw-filter cover premise applies only to live selected false-to-true clean transitions, so nonlive consumers cannot force unnecessary centers. The result is conditional coverage of accepted root pairs. It is not a full edge count, a complete one-dirty bound, or a solution to the unrestricted posted gap. Full review is in `root-cover-review.md`.

### Later review status and scope, 08:44 UTC

Final independent reviews passed for `SelectedDirtyPaths.lean`, `SelectedLabels.lean`, and formalization's checked `ForkCover.lean` assembly; the dedicated review notes record stable hashes and empty logs. These remain conditional components, not a complete one-dirty size bound or an unrestricted Heawood lower bound. The separate cubic gate-elimination experiment reached only the existing 20-gate bound and produced no new Lean theorem; details and primary sources are in `cubic-gate-elimination.md`.

The raw-input fanout postprocessor and its final general-OR composition independently passed exact clause/ID preservation and the 27-gate full-truth smoke; see `raw-fanout-review.md`. The optional joint TEN branch-3 phase artifact also independently passed; see `joint-phases-review.md`. Its 26-gate near-seed computes Heawood with edge `(1,13)` removed and has 47 full-target errors. Those phase preferences are not assumptions, added clauses, or a satisfying witness. The posted unrestricted 26-gate existence gap remains unresolved. No full-instance UNSAT certificate has been obtained by this agent.
