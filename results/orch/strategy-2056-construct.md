# L-meta-2056 constructive route

The posted finite tests are complete for monotone circuits: checked L_meta_2054 proves every independent point/line input has a side of size at most three. No gate-arity or index shortcut was found. A witness therefore must compute the full q=3 plane incidence function.

The 64-gate point-star circuit has no direct repeated OR subexpression: each pair of distinct lines intersects at a unique point. A saving must exploit a mixed multilevel circuit, including Boolean absorption, or a smaller exact patch.

Affine control: points [2,4,5,6,7,8,10,11,12], lines [1,2,3,4,5,6,7,8,9,10,11,12]. Local21 inputs,36 true edges,197 maximal false inputs. All233 boundary checks pass for the44-gate star control. Files in affine2056/: affine-data.json, star44.txt, rows.txt, affine_local.cpp. The short43-gate local run was interrupted to prioritize smaller patches; best reported candidate misses one edge. This is not a result for the posted statement. Full logs local-002.stdout/stderr retained; the initial local run exited4 because its canonical diagnostic row was incorrectly chosen, then fixed without changing truth-table generation.

Quadrangle patch: points [0,1,2,5], lines [0,1,2,3,4,7,8,9,11,12]. Local14 inputs,16 true edges,16 maximal false inputs. All32 boundary checks pass for the19-gate control. An18-gate exact witness would extend to63 gates by adding nine omitted point stars, five gates each. Files in patch2056/: quad-data.json, quad-rows.txt, star19.txt, quad_local.cpp. The18-gate local search was stopped after312,922,850 proposals (~185s) with no witness, because proof_route found a structural obstruction: checked L_meta_723 gives subdivided-K4 core lower bound15, and each of four private leaf variables requires another gate, totaling19. The new specialization is a mathematical argument, not yet a newly compiled theorem here. It uses one worker and passed64 independently randomized star seed checks before search. Complete stdout/stderr saved.

Geometry census groups four-point subsets into degree-profile classes represented by [0,1,2,3], [0,1,2,5], [0,1,3,9], and five-point subsets by [0,1,2,3,4], [0,1,2,3,6], [0,1,2,3,9]. This is a profile census, not a proof of automorphism equivalence.

Further structural obstruction (proof_route/status_review): the triple-collinear4-point class has theta(3,3,3) core lower bound12 via L_meta_723.theta_lower1969 at t=4; seven private leaves force19. No time was spent searching that class after this finding.

Current local target: six points [0,1,2,3,6,7], lines [0,1,2,3,6,7,8,9,10,11,12]. This patch has no private leaf lines: nine lines have degree2 and two lines degree3. It has24 edges and52 maximal false inputs, using17 inputs. The29-gate control passes all76 boundary rows; a28-gate witness would extend to63 by addingseven omitted stars. Files patch2056/six-data.json, six-rows.txt, star29.txt, six_local.cpp. A300-second local run passed64 randomized star seed controls and is active. It tracks read1 witnesses on all24 edge rows simultaneously and softly favors an accepted edge with no read1 witness; no fixed-edge orbit is excluded.

## Six-point search and repair updates

The first six-point run completed300 seconds without a witness. Its best non-read1 state accepted all24 edges but had23 false positives. Complete logs: six-local.stdout/stderr.

Added an exhaustive repair tool, repair_three.cpp. For each gate, downstream evaluations with that gate forced false/true determine the exact relevant truth-table bits. The tool enumerates replacement expressions for one gate, two gates with a uniquely used inner gate, and three gates with two uniquely used inner gates. Deliberately corrupted29-gate controls were repaired for all three cases; full output is saved in repair-control*.stdout/stderr. No repair of the first two global-best six-point candidates was found after2,480,387 expressions.

The hybrid search invokes this exact local repair at each restart. It found a28-gate candidate missing two edges with no false positives and one accepted edge lacking a read1 witness. Symbolic inspection showed that this was still an absorption artifact: p1 AND((p1 AND l12) OR l2 OR l0). Replacing the nested product by l12 and removing the redundant gate gives27 gates for the same incomplete function. No clean wire covers both missing edges, and exhaustive enumeration of all1,980 possible appended binary gates found no completion to28. Files: six-near-best.json/txt, six-near-compacted27.txt, six-near-compaction-check.json. This is not a witness and should not be described as a substantive nonlinear improvement.

A structured variant is now compiled but not launched. It uses proof_route's verified30/31-gate mixed point/line-cover seeds; copies any input through an absorption gadget with all ten first-OR symmetry classes represented; and penalizes three certified normalization violations supplied by circuit_search: AND using a clean input, OR mixing clean and dirty inputs, and clean wires with multiple readers. Exact local repair remains enabled. Files: six_structured.cpp, six_seeds.hpp, repair_inline.hpp. Every run saves complete diagnostics and its final population.

## Subsequent portfolio work

The first hybrid run completed299,492,727 proposals in300 seconds, with4,641 exact repair calls examining4,828,380,691 expressions. No witness was found. Its26 distinct saved candidates were compacted and tested against all appended formulas of up to three new gates; no28-gate completion was found.

The normalized, structured mixed-cover run completed206,867,643 proposals, with3,293 repair calls and2,412,438,327 repair expressions, also without a witness. Its138 distinct final-population candidates were compacted and tested for up to three appended gates, again without a completion. Combining all166 distinct candidates from three runs by AND/OR with shared semantic wires produced730 correct combinations, but the smallest had36 gates.

The six-point set [0,1,2,3,4,5] is now excluded from28-gate search by an independent mathematical check: its six private leaves leave exactly the checked L_meta_9730 graph, whose minimum is23. The explicit edge-preserving map is recorded in six-orbit-a-L9730-isomorphism.json; status_review independently confirmed it.

Next full patch: points [0,1,2,3,4,9], all13 lines,19 inputs,24 positive edges and59 maximal false inputs. Its29-gate control and64 randomized mixed-star controls pass all83 critical rows. The14-input core has19 edges and33 maximal false rows, baseline24 and target23. A23-gate core is only a necessary search condition: adding five private edges costs one gate each only when appropriate point factors remain exposed. Therefore the actual28-gate full patch is searched. New source/data are frozen for independent review before a long run.

The next source adds a penalty for dominated gates: if an earlier wire a satisfies P_b subset P_a and N_a subset N_b, replacing later b by a cannot worsen any critical output error. This rule was independently approved by proof_route/status_review. Source: collinear6_structured.cpp.

Prepared an eight-point leafless control for not_elimination's independent search: points [4,5,6,7,8,10,11,12], lines1 through12,20 inputs,32 edges and136 maximal false rows;39-gate control passes all168 rows. Files eight-data.json and eight-control.txt.

## Exact nonlinear circuit optimization

The collinear six-point fixed28 run completed104,505,001 proposals and1,384,580,610 repair expressions without a witness. Its best normalized state missed one edge. All source/data controls were independently approved; the29-gate control was independently checked on all524,288 assignments.

Directed dominance applied after all730 exact pair combinations reduced the best shared circuit from36 gates to29, but none reached28. See combine-dominance-report.json.

Generated15 exact33-gate paired-star CNF seeds using pR OR qS = ((p OR q) AND(R OR S)) AND((p OR S) AND(q OR R)). They pass all83 rows, have no clean-wire violations or earlier-wire dominance, and eight accepted edges lack read1 witnesses. Independently generated19 exact31-gate adjacent-double-star seeds using bA OR bc OR cD = (b OR D) AND(c OR A) AND(b OR c); these have5–7 accepted non-read1 edges and also pass all normalization checks. proof_route independently generated matching families.

The frozen variable33 optimizer was independently reviewed and is running for1200 seconds. It stores33 gates but measures actual reachable-gate count; only proposals correct on all83 critical rows are accepted. Neutral CNF/DNF expansions and exact one/two/three-gate care-mask repairs explore equivalent circuits. HIT requires compact size at most28. Controls passed34 exact seeds,1000 scalar/bitset and compaction differential cases,33-to-29 shrink, and100 expansion checks. Source hashes: variable33.cpp fbf27c339424861ff42b9917e15ed0da2fe29704ef52ce352d5093f94bc0c9c0; repair_shrink.hpp44e53fbd5c582f0f1c436bec11077d00789f8da8730be934df0d6ac357e58037. No witness so far.

Prepared a future full-plane66-slot variant, not launched. It has52 verified66-gate adjacent-double-star seeds and the64-gate baseline. Its exact row list was regenerated from all8192 point subsets and equals52 minimal true edges plus704 maximal false inputs. Fast53-seed and1000 scalar/bitset+compaction controls pass. It generalizes care masks to12 words, adds one/two-gate distributive expansions, sometimes retains raw nonlinear seeds before shrinking, and emits minute progress. Full shrink/expansion controls and independent review are pending. No extra long worker was started while the33-slot run occupied this agent's CPU slot.

## Full-plane successor ready

The reviewed full-variable engine now has an additive105-seed variant:52 exact66-gate adjacent-double-star seeds,52 exact65-gate inverse-hoisting seeds, and the64-gate point-star baseline last. The delta was independently approved. Source: full_variable66_plus.cpp SHA4ea3b347499aeec66b001c37fd48ed39aef600597b5bcdaa1611af6775c50b58; seed header7ad6f1d5ef083b72680c9af29d90d4c8ecbe8878f16fab0e3dc80066b23d7bd4; care helper remains3e55cb3b72e8eedfc8c535052e7906dbf6f4df2be2d43986b90e6f58a83466b3.

All startup checks pass:105 exact seeds on all756 rows;1000 scalar/bitset and dead-compaction differential cases;66-to-65 exact shrink;100 exact distributive/CNF expansion checks. Finite startup verification completed in under one second at low priority. No full-plane long search has been started by this agent yet; it waits for the current33-slot run to finish.

The66-to-65 shrink control was separately exported and classified. It has14 AND and51 OR gates, all52 accepted edges have a read1 witness, and it has no clean-AND, mixed-OR, clean-fanout, or earlier-dominance violations. It is an ordinary mixed-star simplification control, not a new nonlinear seed. Details: full-control65-classification.json.

Added normalize_exact.py for finite postprocessing of exact-state snapshots. It validates references and critical truth tables, performs only strictly-earlier directed dominance replacements, checks exactness after every replacement, and counts actual remaining gates. The current33-slot baseline remains29 after this stronger normalization; no hit.


## Completed exact-state patch run and full-plane handoff

The33-slot run completed1,200 seconds with2,828,614,301 proposals,737,465,827 accepted exact-state moves,10,062 repair calls and20,191,866,837 repair expressions. No28-gate witness appeared. All65 saved exact circuits remain at least29 gates after directed dominance;14 circuits lack a read1 witness on some accepted edge, but these are32/33-gate circuits, not29-gate improvements. Complete source and logs are preserved.

At16:48UTC, after the parent renewed the lease at16:47:46, the approved105-seed full-plane66-slot optimizer began its1,200-second run on the freed CPU slot. Its source remains frozen. Separate postprocessing examines actual compact size, dominance, and dirty-AND reuse. Direct dirty-AND fanout is only a syntactic diagnostic: OR-only paths may carry a nonlinear ancestor to several later AND gates. No restriction requiring either form of reuse has been proved.


A separate one-gate neutral care-mask probe made11,500 attempts across all105 full-plane seeds but found zero alternative gates after excluding unchanged/commuted records. This move was not added to the running search. A two-gate probe requires a uniquely used inner gate and simultaneously resynthesizes both gates;626 attempts gave170 exact moves and338 alternatives, including two operator-changing alternatives. Controls pass explicit OR reassociation, all756-row checks, scalar differential checks, and10,500 spare-slot rebuilds whose compact reachable DAG remains exactly unchanged. A separately frozen future variant uses one two-gate attempt per16,384 proposals and scatters spare slots on half of restarts. The active full66-plus source has not been changed.


The next70-slot pair/scatter variant is independently approved at source67ec862e8e3c451f71ba789a1b0972b51aeb41d29ea1b13877eccd2a55ffbb39 and actual651-seed header4cf72b9093ce4dbb6de8bd0a0c305d01bd11d7e244689539f6038d75baa77bae. It includes52 double-star66g,52 inverse-hoist65g,78 paired-star68g,468 independently audited shared-dirty-AND67g seeds, and baseline64 last. Actual compact HIT remains≤63.26+70=96 wire bounds were checked; half of restarts retain raw nonlinear seeds before any eager shrinking. All651 header circuits were independently evaluated on756rows. Controls pass explicit reassociation, baseline64→68 CNF expansion, distributive expansion,65,100 exact compact-DAG scatter checks,3,356 pair attempts and scalar differentials. The full66 run remains active and unchanged; the wider successor waits for its CPU slot.


A further shared-rectangle family was proposed independently to the coordinator and proof_route: for adjacent centers b,c, take A⊆N(c) containing b and D⊆N(b) containing c, with both sizes at least two. H=(OR A) AND(OR D) can feed b AND(H OR OR(N(b)\D)) and c AND(H OR OR(N(c)\A)); their union is the same double-star. The OR cost is constant as A,D grow, so full-plane size remains67. The existing468 seeds use only2×2 rectangles. proof_route is preparing2×3,3×2,3×3 rectangles as an optional audited extension; the approved651-seed pool remains frozen.
