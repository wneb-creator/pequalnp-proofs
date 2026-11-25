# L-meta-4970 counting route

The posted star-OR witnesses may be unused gates. They assert exact pure disjunctions, not an output-cone condition. The `tCount` hypothesis is syntactic OR-reach: an AND barrier stops the reach, even if its function still has singleton support. Therefore T=0 must not be confused with semantic color homogeneity or with the existing clean-circuit assumptions.

Checked component: `/tmp/oec/pequalnp-pilot-99/gap4970/lower_bound/Neighbourhoods.lean`, 92 lines, SHA256 `65937c9e89fa9a5c4b1397655affcdace97090b774cdab231f0a4f61777cfeda`. It imports only PEqualNP.Defs. Compile/export exit 0; neighbourhoods.stdout and neighbourhoods.stderr are empty. Frozen source.

The file defines the bipartite neighborhood family on Fin(p+l), proves its two embedding equations, and proves that distinct neighborhoods intersect in at most one vertex from the exact posted no-four-cycle hypothesis. This is the separation premise for sat_encoding's checked SupportFamily support ledger.

Counting obstacle: a family of several disjoint witness OR supports at one center gives leaves minus components, not leaves minus one. If K is the number of support components and d the total covered leaf incidences, a pure-OR lower bound d−K still needs a computation/connectivity argument to finish the target.

The tempting unqualified remainder bound `remaining gates ≥ K + minimum cover size − 1` is FALSE when all available components are counted. Counterexample agent checked C6 on 3+3 vertices: a canonical all-point-star circuit has 3 pure-star OR gates, 3 ANDs and 2 output ORs. Appending the 3 unused opposite-side neighbor ORs gives K=6, d=12, 6 pure OR gates, 5 remaining gates and cover number 3. The claimed remainder bound asks 5≥8. The posted target remains true. Exact computational source and result are under gap4970/counterexample/dead_star_ledger.py and .json.

A sufficient corrected ledger would retain overcoverage credit: `remaining + (d − |E|) ≥ K + |S| − 1`, or select an appropriately reduced witness family before counting. Neither statement has been proved for the actual circuit.

Do not assume generic C4-free AND-count ≥ minimum vertex cover. Existing L_meta_217 and L_meta_2399 establish that statement only for cover lower bounds t≤5, via about 7300 lines of finite certificates. No unrestricted counterpart was located. A direct final proof should use the no-mixed-OR and star-witness hypotheses jointly.

An input-restriction idea also remains incomplete: deleting a vertex that occurs as a leaf in several uniquely centered witness stars can collapse distinct OR cones, but some surviving size-two witness supports become singletons. Thus the exact bare-free premise is not preserved by straightforward vertex deletion.

## Strength of the posted statement

There is a direct reduction from arbitrary monotone circuits to the posted class, using precisely the syntactic nature of tCount and the permission for dead witnesses.

Replace every original OR gate OR(u,v) by three gates AND(u,u), AND(v,v), OR(the two copies), renaming later references. The circuit function is unchanged, all gates still have fan-in exactly two and read backwards, and every original OR gate now has empty OR-reach because its operands are AND outputs. Thus tCount=0. The size increases by twice the number of original OR gates, and is at most 3 times the original size.

For a bipartite incidence graph whose degrees on the left are even, partition each left vertex's neighbors into pairs and append one unused OR of the two corresponding right inputs per pair. These are all one-color OR gates, so tCount remains zero. Each edge has a posted star witness of size two. Exactly |E|/2 gates are appended.

Consequently L-meta-4970 would imply, for any original AO2 circuit C for this graph, `3*C.size + |E|/2 >= |E| + tau - 1`, or `C.size >= |E|/6 + (tau-1)/3`. For projective planes of odd order, left degrees are even and |E| grows as n^(3/2) in the number n of vertices. Thus this posted statement would yield a superlinear unrestricted monotone circuit lower bound for those C4-free graph functions. This is a sound mathematical reduction sketch, not a Lean proof and not a refutation of L-meta-4970. It explains why a complete elementary outside-cost ledger would be substantial.

## Checked conditional transfer

The conditional transfer is now Lean checked, using the existing factor-six transformation from L_meta_4791 rather than implementing the factor-three sketch. All listed files are frozen:

- Shield.lean, 1320 lines, SHA256 d6582a1718887e86ade01e6415b844183cfb8bfdd4618e071a8d705bda2e3c44. Copied helper namespace from L4791, renamed, full-line comments removed, only PEqualNP.Defs imported. It gives an equivalent T=0 AO2 circuit D with D.size+4≤6*C.size for nonempty singleton-false functions. Export passed; only inherited deprecated-if tactic warnings.
- PairDecomposition.lean, 112 lines, SHA256 567f3375f84d09d8bc0cd9b44de68b37d814c91534846fd1ac826781b260ca74. Even left degrees yield a valid covering list of neighbor pairs with twice its length equal to |E|. Export passed with empty logs.
- AppendPairs.lean belongs to reduction_strategy and is separately checked/frozen. It appends exactly one dead monochromatic OR gate per neighbor pair, preserves the function and T=0, and supplies the exact posted star witnesses.
- StrengthTransfer.lean, 103 lines, SHA256 0ea5682234116387c51f6758e709787b724324ebb10eec9a37a3f5c46173a660. Export passed with empty logs. Its Posted definition is the desk statement copied verbatim as an explicit hypothesis.

The checked conclusion is: assuming Posted, every AO2 circuit C for a nonempty C4-free bipartite graph with all left degrees even admits a vertex cover S such that `|E| + 2*|S| + 6 <= 12*C.size`. Hence every lower bound t on vertex-cover size satisfies `|E| + 2*t + 6 <= 12*C.size`. No circuit-size, T=0, or witness assumption is added to the original C. This is a conditional consequence, not a proof of Posted.

The complete self-contained artifact is StrengthTransferStandalone.lean, 1873 lines and 87786 bytes, SHA256 9c58f3b3c4d3ef48c2fcff24ebd04918790c3550c3cfce16ed73fb3842a9322e. It imports only PEqualNP.Defs and compiled successfully; its full stdout contains only inherited deprecated-if warnings and stderr is empty.

## Near-miss post-processing

Own scratch directory: gap4970/lower_bound/postprocess. No live search-engine files are modified. The scripts derive a candidate graph from every accepted two-input row, verify the complete truth table against that graph, recompute its vertex-cover number, enumerate all exact pure-star OR witnesses for that graph, and optimally select an ancestor-closed union of witness cones plus the output cone. They then check the pruned circuit's full function, T count, and star coverage again.

The Fano-minus-incident smoke candidate computes exactly the graph obtained by deleting the two edges incident to point 0. It has 14 edges and cover number 5. Pruning removes 2 gates and yields 18 gates, exactly the posted bound. All 4096 assignments were checked.

The five immutable subdivision-of-K4 improvement snapshots yielded three exact smaller graph functions: 6 edges/cover 2/pruned size 9/bound 7; 9 edges/cover 3/pruned size 11/bound 11; and 10 edges/cover 4/pruned size 13/bound 13. The other snapshots have higher-degree or non-bipartite/non-C4-free behavior. All 1024 assignments were checked for each snapshot.

Every gate output was also considered as a possible different graph function. A further bounded exhaustive pass tried one operand replacement, one AND/OR flip, and redirecting all uses of one gate to an earlier wire. Across the smoke and five subdivision snapshots this examined 4671 variants. It found no counterexample; the minimum valid pruned-size minus posted-bound margin was zero. Matching and covering sets of equal size certify the cover numbers in these probes; a prospective counterexample additionally triggers brute-force cover enumeration.

All original snapshot bytes, full logs, derived graphs, pruned circuits, and mutation summaries are retained under postprocess. These are computational searches, not Lean proofs or an exhaustive search over all circuits.

The later irregular11 and Fano-minus-incident portfolio snapshots likewise reduce to equality cases: irregular H has 12 edges, cover 4 and pruned size 15; Fano H has 14 edges, cover 5 and pruned size 18. Another 2224 one-change variants and 17 gate-output candidates found no refutation. Counterexample agent received four verified equality seeds for a variable-graph search. Their isolated raw inputs are completely unread and can be removed by renumbering: incident smoke becomes n=11,p=5,size=18; subdivision candidate03 becomes n=9,p=3,size=11; subdivision candidate04 stays n=10,p=4,size=13; irregular becomes n=10,p=4,size=15.
The next immutable batch contains seven irregular11 and four Fano-minus-incident improvements. Complete truth-table and pruning checks found six equality snapshots, one valid graph with margin two, and four snapshots failing exact graph shape or star coverage. The batch examined 81 gate-output records and 11,755 local variants; 544 variants passed all graph/star checks and none violated the posted bound. Counts are scoped to this batch: its latest snapshots overlap earlier snapshot tests. Results are frozen in postprocess/{irregular11-improvements,fano_minus_incident-improvements}, summarized in batch02-summary.json and recorded by postprocess-manifest-02.json. Earlier manifest01 files were hash-checked unchanged.

The six immutable Fano-minus-nonincident snapshots were also fully postprocessed before the desk withdrawal. Three prune to equality (10 edges/cover 4/size 13; 12 edges/cover 5/size 16; 13 edges/cover 5/size 17); one valid snapshot has margin one, and two fail the quadratic truth table on one row. This batch examined 7074 local variants, 54 gate-output records and 353 successful full-hypothesis mutation records, with no refutation. Across the 22 distinct immutable improvements and the distinct smoke circuit, excluding duplicate latest-snapshot reruns, there are 23,500 local variants, 172 output records and 1151 successful mutation records. These are bounded computational probes, not an exhaustive circuit census. All completed new files after manifest01 are frozen in postprocess-manifest-03-final.json; research stopped immediately on the parent STOP after HTTP410 at16:30UTC. The unfinished cubic phase was not postprocessed.

