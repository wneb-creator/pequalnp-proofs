# pequalnp-pilot-64 — L-meta-2602

Lease is held and renewed only by the root agent. No other desk requests.

Exact statement: /tmp/oec/pequalnp-pilot-64/statement.txt
Desk metadata: /tmp/oec/pequalnp-pilot-64/desk-next-1.json

Goal: exclude 63–64 gate AND/OR circuits for the order-3 incidence graph whose formal derivatives in both directions of edge (0,0) vanish. Three reductions already live, so prioritize full proof or checked refutation.

All helper declarations must be inside the module namespace; final theorem fully qualified at top level, last. No strings, _root_, commands, new axioms, or native evaluation.

Agents append findings below; use distinct scratch lemma filenames. Root owns final Outside file and git operations.

## Structural attempt

- Double vanishing cannot be excluded semantically alone: separate gates g=xy, h=xy, then g AND h compute xy but both singleton derivatives vanish. Distinct input wire indices do not forbid this.
- Exact general lower bound for unrestricted monotone circuits of a C4-free graph is not an immediate biclique-cover argument; nested AND gates permit cancellation of unwanted monomials by absorption.
- Existing reduction R_meta_2602_2 separates a 56-gate bound on the endpoint-deleted face from a path theorem. R_meta_2602_926 has reusable evaluation, derivative-trace, and collision induction proofs. R_meta_2602_415 separates a generic monotonic guard lemma and a hard face/cut statement.
- Added unverified geometric helper candidate results/orch/lemmas/Structural.lean: degree 4, 52 incidences, 45 after deleting endpoints, no rectangle, diagonal matching. Awaiting toolchain for Lean checking.

## Existing reductions and checked descendants (reductions agent)

- `R_meta_2602_2`: exact goal follows from a 56-gate lower bound on the face with point 0 and line 0 false, plus a path theorem saying enough fresh gates on every incidence face force a singleton-sensitized path from one endpoint to output. Its proof provides a general face compression construction and sensitized-path derivative propagation.
- `R_meta_2602_415`: splits off an elementary monotonicity/guard fact; the other hypothesis is a 63–64-gate cut obstruction using fixed independent-set masks. No checked proof of that obstruction found.
- `R_meta_2602_926`: 4 cases on AND gates blocking the two derivative directions. This is a partition of the remaining hard obstruction; no completed descendant identified.
- Parent `R_meta_1482_3` would reduce our problem to unconditional size ≥64, no junk AND in a least circuit, and no nested AND when junk is absent. The third is checked in `L_meta_2393`; the first two remain core obstacles.
- `L_meta_2067` proves a derivative is true when `andPairs = 0`. `L_meta_2069` proves one directional derivative true if every AND gate is below the output function.
- Checked lower bounds `L_meta_4803`, `L_meta_1751`, `L_meta_2059`, `L_meta_5158` require no nested AND / `andPairs = 0`; they do not establish the unconditional bound.
- `L_meta_1961` gives shrinking with at most one nested AND pair and size <64. `L_meta_3799` gives shrinking when every AND has at least two readers, again size <64. They do not cover the critical 64-gate case.

All these Outside proofs would need inlining: the allowed project import is only `PEqualNP.Defs`, which gathers definitions rather than these results.

## Independent audit 2026-11-25T03:09:20.084655+00:00

- The posted gate condition enforces both operations and strictly earlier inputs, so derivative witnesses are unique on all real wires. A draft general proof is in `results/orch/lemmas/Audit.lean`, with wire length and output range lemmas; awaiting restored cache to compile.
- No direct semantic contradiction from two vanished derivatives: the 3-gate circuit a=x AND y, b=a OR z, c=a AND b computes xy with both derivatives zero at the singleton bases, despite distinct operand wires. Thus the size condition and global incidence structure are essential.
- Current repository format adds helper namespace discipline: all helper declarations under the module namespace, final theorem fully qualified at top level and last.

## Derivative route

- Both existential traces are exactly linear coefficients on the edge (0,13); no semantic/index loophole.
- Generic two-gate wrapper: A=C.output OR z; output=C.output AND A. It preserves the Boolean function and adds exactly two gates. If C and z reject both singleton base inputs, both derivative outputs become false. Thus a <=62-gate incidence circuit gives a target counterexample after padding.
- Distinct collision gates do not force three AND gates: x AND y; previous OR z; first AND second has 2 AND gates and both derivatives vanish.
- Draft generic wrapper lemmas: results/orch/lemmas/Derivatives.lean. Uses only PEqualNP.Defs.ReadK; awaits toolchain/cache validation.

## Counterexample audit and finite tests

The exact statement has no immediate output-index or trace-freedom loophole: output is forced valid by accepting input {0,13}; valid wire traces are unique. Ordinary star circuits do not satisfy either vanished derivative.

Exhaustively enumerated the 8192 point subsets and their forced line covers for the order-3 incidence graph. Minimum vertex cover is 13 with exactly two minimizers (all points; all lines). Thus a minimum ordinary edge partition into stars uses one entire side; all its edge derivatives are nonzero. The same two-minimizer result holds for orders 1 and 2. This does not prove a lower bound for general circuits.

Exact BFS through reachable truth-table/derivative signatures with distinct earlier input wires found minimum sizes for a vanished derivative pair at xy: xy = 3; x(y OR z) = 4; x(y OR z OR w) = 5; xy OR yz OR zw = 5; xy OR zw = 4; 4-cycle = 5; triangle = 5. In particular a universal +2 reread penalty is false: (z OR xy) AND (w OR xy) computes xy OR zw using only 4 gates and repeats both x and y. Full program and output: /tmp/oec/pequalnp-pilot-64/counterexample_search.py and counterexample-search.log.

A full-plane stochastic search is running for 20 minutes from star64 and double-read66 circuits with two gates removed, with exact monotone equivalence tested on all 52 minimal true assignments and every maximal independent set. Program /tmp/oec/pequalnp-pilot-64/plane_local_search.py; live best plane-best-64.json; complete output plane-search-64.log. No counterexample yet.

- Research checked 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://eccc.weizmann.ac.il/report/2005/021/download/ . General quadratic circuits cannot be flattened without cost: linear circuits versus nearly quadratic one-AND-level circuits exist. This does not itself settle the C4-free/order-3 case, but rules out using a universal flattening assertion.

Independent audit update 2026-11-25T03:15:27.411594+00:00: `Audit.lean` compiled via `lake env lean` exit0. Derivative witnesses agree on every real wire under fixed initial values and topological recurrences; any circuit accepting some input has its output in range. Full logs are scratch `audit-build-3.stdout.txt` and `.stderr.txt` (both empty).

### Checked structural partial at 2026-11-25T03:17:10.809115+00:00

`results/orch/lemmas/Structural.lean` passed direct `lake env lean` (exit 0). Proven: point/line degree 4, no rectangle, 52 incidences, 45 after deleting endpoints, vertex-cover bound 13, deleted-face cover bound 12, exactly two minimum covers (the full sides), all incidence bicliques are stars, all incidence bicliques have at most 4 edges. Log: `/tmp/oec/pequalnp-pilot-64/structural-build.log`. One harmless unnecessarySimpa warning. These are geometry/normal-form facts, not a lower bound for arbitrary circuits.

- Derivatives.lean CHECKED by Lean (exit0, derivatives-check-4.log): wrapper size/topology/eval/linear-zero lemmas. Frozen for early push; developing stronger distributive wrapper in Distributed.lean.

- Distributed.lean CHECKED firstpass (distributed-check-1.log, exit0): (F OR z) AND (F OR t) uses one more gate than F OR (z AND t), with exact eval equality on all inputs. Generic append-one-gate API included. Linear-zero and topology extensions next.

Counterexample update 2026-11-25T03:20:43.789290+00:00: 39-line Counterexample.lean compiled via lake env lean, exit0, empty counterexample-lemmas-build.log; independent review passed. Exact65-gate relaxed-threshold witness and64-gate one-edge near-miss saved as scratch plane-exact65.json and plane-nearmiss64.json, independently scalar-verified on52positive edges and704maximal independent sets. The near-miss lacks only edge(8,8), input wires(8,21). No posted-statement counterexample.

Searches active: three64-gate fullplane variants (seeds64,65,66), plus independent38-gate13-output OR-sums synthesis on26-row monotone boundary basis, plus C6 with4OR/unboundedAND to test a possible general OR-count lemma. Complete logs and scripts in job scratch.

## AND/OR count alternative (reductions agent)

- Enumerated all8192 point subsets and their closed opposite neighborhoods. The order3 incidence graph has704 maximal independent sets: side sizes (0,13):1,(1,9):13,(2,6):78,(3,3):52,(3,4):234,(4,3):234,(6,2):78,(9,1):13,(13,0):1. Generic negative-certificate counting gives only ANDcount≥10, not13.
- Built `and_count_search.py` under job scratch: normalized AND-count circuits with free OR sides; edge positives and all maximal-independent-set negatives characterize the exact monotone function. Matching3 controls:2AND UNSAT in0.01s,3AND SAT exact in0.05s. Fano6AND (37negative rows) timed out60s with/without symmetry normalization. Plane12AND full704negative rows timed out182.62s (no verdict).
- Dual control for OR count:6-cycle with4OR gates UNSAT in1.5s;8-cycle with6OR gates timed out30s. These are computational observations, not Lean proofs.
- A naive general C4free ORcount≥edges−1 invariant is false: checked `L_meta_1006` has16edges and a realization with14OR gates; graph has triangles. Restricting to bipartite graphs still needs a genuine absorption argument.
- Pivoting to bounded local SAT repair of the64-gate near-miss. `repair_nearmiss.py` fixes all but selected gate neighborhoods, enforces distinct earlier operands, all52edge positives, negative-basis CEGIS over704maximal independent sets, and both exact directional derivative recurrences false. Current neighborhoods6 and8 gates have first-round relaxed candidates, full negative refinement ongoing. Complete stdout/stderr are retained per run in scratch.

## Toolchain and independent circuit review

- Official Lean4.36.0 installed under job scratch. Targeted authentic Mathlib cache downloaded successfully; full PEqualNP.Defs and checklemma executable builds passed. No Mathlib source build performed.
- Full checker runtime imports all Mathlib, whose complete artifact closure exceeded the7.9GB filesystem. Targeted cache supports direct Lean checks only. A compressed FUSE storage test was refused by the OS (Operation not permitted); stopped with no mount and no memory-backed storage changes. Exact setup logs and limitations are in scratch toolchain-validation.txt.
- A second independent scalar circuit evaluator tested all52positive edges and all8192 negative assignments maximal for a fixed point subset. The65-gate artifact is exact with13AND+52OR; the64-gate artifact has13AND+51OR and misses only edge(8,8). Both have distinct earlier operands and both directional derivatives false. No false-positive negative rows were found. SHA256 and full results are in scratch independent-circuit-review.json. This is computational validation, not a Lean proof of the target.

### Checked structural v2 at 2026-11-25T03:25:45.918628+00:00

`Structural.lean` now additionally proves every complete-rectangle cover needs at least 13 blocks. If 13 blocks are indexed so block i contains the diagonal incidence (i,i), all blocks are exactly the full point stars, or all are exactly the full line stars. Direct Lean exit 0, log `structural-build-v2.log`; 255 lines.

Gate-elimination caveat: counting duplicate wire functions on a face is insufficient for the desired nine-gate reduction. Ordinary 64-gate star circuits lose six distinct wire functions on an incident-endpoint face; two more fresh OR helper gates become unused. Garbage collection / semantic rewriting must be included in the reduction.

## Root research and re-plan

Read2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, says: “We therefore need entirely new lower bound arguments for monotone circuits computing quadratic functions.” Generic single-level normalization is false; no source checked establishes the specific order3 bound. An arbitrary-circuit ORcount51 or ANDcount13 claim remains UNVERIFIED because no proof or complete finite certificate has been found.

Root conjectural elimination route for the13 pure-OR outputs only: eliminate the latest AND; if it feeds one output, choose a child below that output clause; if multiple outputs, pairwise intersection≤1 allows preserving singleton values with at most one input wire. This is not yet a formal circuit transformation and does not settle the single-output incidence gap.

## Boundary certificates and research audit 2026-11-25T03:27:42.837804+00:00

- `Boundary.lean` (77 lines) and `BipartiteBoundary.lean` (37 lines) compile with empty logs. The first proves maximal-independent-set sufficiency for graph-function semantics; the second uses all point assignments with saturated nonneighbor line assignments. The latter has 8192 assignments for 13 point inputs, avoiding enumeration of all 26 inputs. Both were independently reviewed by counterexample agent.
- Primary source read 2026-11-25: Jukna, Disproving the Single Level Conjecture, https://epubs.siam.org/doi/abs/10.1137/S0097539705447001?journalCode=smjcat . Its abstract establishes that generic quadratic-function single-level normalization fails. This does not settle the bipartite C4-free case here. A quantitative normalization using the actual incidence structure is still needed; no exact bound for this plane was verified from a public paper.

## Pure-OR family normal form progress

- PureClause.lean checked: if monotone f AND g equals OR(A), one child already equals OR(A).
- ClausePrune.lean checked: if (f AND g) OR r equals OR(A), one child can replace the AND. If f OR r equals OR(A) and r is monotone, replacing f by its singleton linear part preserves the output. If f feeds two target clauses whose sets meet in at most one variable, that linear part is constantfalse or oneinput.
- Proposed circuit normalform: remove the latest AND. Its downstream outputs have OR-only contexts. If one output is affected, bypass a child; if two or more are affected in a linear family, replace by its at-most-singleton support. Constantfalse means prune that OR branch rather than introducing a gate. Repeating should yield an OR-only circuit without more gates; the 13 degree4 neighborhood outputs then need39 OR gates. Circuit-level rewiring and counting are still unproved.
- Distributed.lean checked extension: linearParts appending, zero linear outputs of the distributed wrapper, and valid distinct-earlier-input topology.

## Independent audit of 10+56-1 cut 2026-11-25T03:31:19.283241+00:00

The local compression must preserve both formal derivatives and distinct operand wires. Ordinary Boolean simplification is insufficient: after a zero-specialization, bypassing an OR may identify two distinct input wires of an AND; simplifying the resulting AND(w,w) changes formal derivatives. With repeated operands allowed, an ordinary 8-gate double-star circuit followed by AND(output,output) is a 9-gate double-defect circuit. Consequently the proposed local lower bound10 is false in that relaxed model; duplicate-producing gates must remain or be explicitly charged.

### Structural cut analysis at 2026-11-25T03:36:07.219926+00:00

For the edge (point0,line0), take T={point0,line0}, N={point1,point3,point9,line4,line10,line12}, R=the other18 inputs. Restricting R=0 yields an8-variable double-star with7edges; restricting T=0 yields the45-edge face. A desired cut inequality would preserve the local formal derivatives and bound face-circuit size plus local-circuit size by original size plus1. This remains unproved. Distinct operand IDs are essential: restriction/constant pruning can alias two operands and dropping AND(w,w) changes formal derivatives. In the repeated-operand model, an8-gate ordinary double-star plus AND(output,output) already gives a9-gate defect. Thus the strict local10 lower bound cannot be applied after naive pruning.

The65-gate witness has form (G OR p4) AND (G OR N4), with G the other12 row stars. Its local restriction is G AND (G OR line4), explaining why one unit of cross-sharing must be allowed if one uses strict local cost10 and face minimum56. A generic C4-free cut inequality would itself imply strong unrestricted monotone lower bounds, so this is the hard theorem, not routine gate cleanup.

Finite exact-DNF check of face pruning is in job scratch face-collapse-check.py / face-collapse-check.log. Ordinary64-star: (duplicate gates, removable after pruning)=(6,8) on all52 faces. Wrapped66-star: (7,10) on48faces, (8,10) on4faces.

2026-11-25T03:42:41.900352+00:00 COMPLETE relaxed-threshold witness compiled: Witness65.lean (496 lines) proves all posted semantic, gate-legality and two derivative-trace clauses, with size exactly65. It does not refute threshold64. Combined lemma size65_double_read; empty build10 log, exit0. All five stochastic searches completed without a64-gate counterexample.

## Checked OR-family lower bound

- OrFamilyBound.lean now CHECKED (or-family-check-5.log, exit0): a common topological monotone AND/OR wire family computing m pure disjunctions, each on d inputs, with pairwise target intersections of size at most1, needs at least m*(d-1) OR gates. For the13 order3 line neighborhoods this is39.
- Proof extends upstream L_meta_5763 finite-set union charging to unary subset redirects. A wire below a targetclause contributes its singleton support; a large AND redirects to one child below that clause; large OR gates are charged. One output needs d-1 charges; a charged gate cannot be shared by two linear-family targets.
- This uses one common wire-function family F. It does NOT identify charges across different point/line cofactors of a single incidence-output circuit; that step would require an additional AND/OR accounting argument.
- CircuitAdapter.lean supplies actualCircuit evaluation/monotonicity/topology bridge; structural agent is specializing to13 neighborhood outputs.

### Circuit adapter checked at 2026-11-25T03:45:12.712234+00:00

`CircuitAdapter.lean` (195lines) passes Lean with empty output (`adapter-build-3.log`). For `TopForm.IsAO2 n C`, it proves the exact input-wire semantics, binary gate recurrence with natural-number operands, strict backward operand bounds, monotonicity of every wire, and a count bridge from abstract OR-gate indices to `ReadTwo.nOr C`. No distinct-operand assumption is needed by these adapter facts. Combined standalone plane-neighborhood39-OR application is now checking in `PlaneOrBound.lean`.

## Structural concrete OR-family lower bound (2026-11-25T03:47:30.185835+00:00)

Checked `results/orch/lemmas/PlaneOrBound.lean` (801 lines, exit 0; complete log `/tmp/oec/pequalnp-pilot-64/plane-or-bound-1.log`). The final theorem `PEqualNP.Outside.L_meta_2602_aux.PlaneOrBound.plane_or_lower_bound` says every legal binary AND/OR circuit on 13 inputs simultaneously computing the 13 plane-neighborhood OR functions as wires has at least 39 OR gates. AND gates are unrestricted. It combines the finite incidence geometry, the Circuit.wires adapter, and the generic OR-family bound. The independent reviewer passed the exact assembled file (SHA256 32f53c901432992c0a7585001d359f4203c28ef873df4c9f063bfb1e1c4822ce). This does not prove the single-output 26-input gap: the same original wire can have different functions under different point cofactors, so the simultaneous-output premise must not be assumed.

### Derivative strategy update, 2026-11-25 03:58 UTC

- `ProductiveBound.lean` (276 lines) compiles and has independent PASS review. Its generalized seed condition handles cofactor constants and projections. It proves 39 weighted productive point/OR charges; incomparable child singleton supports are required, so redundant OR merges can be bypassed.
- Raw productive multiplicity still cannot be upper bounded by gate count: duplicating a split and ANDing its result with an equivalent old wire adds productive charges for many cofactors at cost two. Selected witness forests are necessary for any amortization.
- A defensible local sharing consequence: if one wire is charged for at least two points, its zero-point singleton support has at most one line, and every charged point changes acceptance on some singleton line. This follows from cofactor support size at least two, monotonicity from zero points, and pairwise intersection at most one. It gives point-sensitive paths, but no gate-cost injection yet.
- Four-type classification by full point-only/full line-only assignments does not by itself prove an AND lower bound: P/L-type children can carry hidden mixed terms and higher-degree pure terms. The first zero-type AND need not have only its singleton rectangle as pair support.
- Primary source read 2026-11-25: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, Jukna, Disproving the Single Level Conjecture. Its Lemma 3.7 supports disjoint-family OR counting; page10 gives the K2,2-free edge lower bound for single-level circuits. General counterexamples there are saturated nonbipartite extensions. The author PDF says Tarjan disproved powerlessness of ANDs for Boolean sums (the ECCC text extractor misleadingly omitted the prefix). No general bipartite normalization theorem was verified.

## Actual-circuit point-cofactor productive count (2026-11-25T03:58:39.372136+00:00)

`CofactorProductive.lean` compiled exit 0 (full log `/tmp/oec/pequalnp-pilot-64/cofactor-productive-2.log`). The final `cofactor_productive_lower_bound` assumes a legal 26-input binary AND/OR circuit computing the full plane incidence function, constructs its 13 point-singleton cofactors, and proves a sum of at least 39 productive OR charges over those cofactors. Every cofactor seed is a constant or line projection; constants true are excluded by the Below hypothesis. The recurrence and monotonicity are adapted from Circuit.wires. This applies to the actual posted circuit model but is a weighted point/gate count: the same OR gate may occur for several points. No conversion to 39 distinct OR gates is justified. Independent review requested; file frozen.

### Why the cofactor charges do not directly give distinct OR gates

In the standard 64-gate column-star circuit (39 OR gates forming point neighborhoods, 13 ANDs masking each line, 12 outer ORs), every inner point-OR becomes a constant under a point-singleton cofactor. Such gates are never productive. Consequently all 39 weighted point-cofactor charges lie among the 12 outer OR gates. This already occurs in the size range of the posted gap (without its double-derivative defect). Deduplicating the charges is invalid; any successful accounting must also charge OR gates used to build point masks. Under line cofactors the roles reverse: the 39 inner point-OR gates supply the charges, while the outer ORs are unary after restriction.

2026-11-25T04:01:17.397996+00:00 Classification obstruction: 44-line ClassificationObstruction.lean compiled (empty classification-obstruction-build.log). The final P/L AND in (a OR by) AND (z OR by) computes the two-edge matching az OR by, so its full edge set is not rectangular. Earlier zero gate by carries one inherited edge. Derivatives agent then found a stronger seven-gate filtered matching with no earlier zero-type gate; its separate scratch formalization is in progress. Neither example violates the total-cost inequality.

2026-11-25T04:02:29.017319+00:00 Stronger classification obstruction compiled (81 lines, empty classification-obstruction-build-2.log): seven-gate circuit (p OR l) AND (q OR m) AND (p OR q) AND (l OR m) computes pm OR ql. Its final gate is type0 with P/L operands, every earlier gate is true on at least one pure-side assignment, yet the two matching edges form no rectangle. Thus subtraction of earlier zero-gate edges does not repair the proposed rectangle normalization. The example has extra nonzero-type AND gates, so a cost-accounting argument could still survive.

2026-11-25T04:06:44.619457+00:00 Alternative 66-gate seed verified: pick point4, L its four incident lines, A_out all36 incidences on nine other lines, A_in the12 incidences on L excluding point4. Formula (p OR A_out OR A_in) AND (L OR A_out) uses44+15+3+4=66 gates (14AND/52OR). Exact scalar checks on52 edges,704 maximal independent sets and both derivative traces pass. JSON/generator/log archived under results/orch/search; not a posted64 counterexample. Structural agent receives this distinct seed for the final neutral walk after root renewal.

### 2026-11-25 04:06:58 UTC — Existing-reductions agent: finite core and trusted replay

The unrestricted nine-gate eight-input double-star synthesis problem is computationally UNSAT. AND counts 0,1,2,6,7,8,9 have direct exclusions; counts 3,4,5 each have ten UNSAT first-gate cases under the verified 72-element leaf/side automorphism group. The ten-row monotone boundary basis is exhaustively tested against all 256 inputs. A ten-gate witness is fully scalar-verified. No connectedness or gate-order restriction is used in the complete coverage. Archive: results/orch/search/double_star_audit/. These are SAT results, not a Lean lower bound or a global plane argument.

A separate trusted replay now compiles: results/orch/lemmas/Reductions.lean proves UNSAT of the exact concrete five-gate, four-input path synthesis CNF. It copies the repo LRAT checker and uses decide +kernel with 1,274 trimmed RUP steps. Axiom audit lists only propext, Classical.choice, Quot.sound. Source is 341095 bytes. Archive: results/orch/search/kernel_lrat_control/. The circuit-to-CNF bridge is not yet proved; no statement about five-gate circuits follows formally until that bridge is supplied. Default bv_decide was rejected after a tiny test introduced a native axiom.

Current work: reconstructing a typed five-gate candidate and every Tseitin-variable expression to prove the semantic encoding bridge with ordinary Lean proofs. Regenerated CNF is byte-identical to the certified input. First 30 clause proofs compile; all clause kinds and output/derivative clauses are being checked before the full 2537-clause proof.

### 2026-11-25 04:12 UTC — AND-count bridge test

An incremental variant of the existing normalized AND-count SAT search started with only 28 pure/single-side maximal negative inputs, rather than immediately adding all 704. Plain12AND timed out at60.35s; symmetry/reduced variant timed out at180.31s. Both are UNKNOWN, no candidate or certificate. Complete sources, CNFs, stdout/stderr and limitations are archived in `results/orch/search/and_plane_incremental/`.

A reverse-formal-derivative route also loses too much information: in the distributed65 construction `(A∨p)∧(A∨L)`, point derivatives at all-point-zero have only16 accepted singleton incidence edges, and line derivatives at all-line-zero have only4. Thus one additional OR can erase most formal read-once supports. Missing derivative edges cannot be charged independently to many extra gates.

## 2026-11-25T04:16:59.619350+00:00 — Counterexample: exact small-graph and H1/H2 checks

Unrestricted C6 synthesis: ordinary 7 gates UNSAT (7.69s), ordinary 8 SAT (0.59s); both-direction defect at an edge: 8 gates UNSAT (113.71s), 9 SAT (22.62s). Controls independently checked on all64 inputs and derivative recurrences. Theta3 ordinary11 and defect12 on an internal path edge both UNKNOWN at30s. Encoder and solver UNSAT are not Lean proofs. Complete scripts, CNFs, solver streams, controls and provenance are in search/small_graph_cost_audit/.

Conditional alternative: H1 accepting52 edges and rejecting702 mixed maximal independent sets, if at most38 gates, combines with25-gate H2=(any point AND any line) and a final AND to refute63--64. Every singleton lies in196 mixed maximal negatives, so H1 and H2 are both false at both singleton bases; final AND derivatives vanish automatically. No such plane H1 constructed. See search/H1_H2_ROUTE.md and exhaustive finite checks in search/h1_h2_boundary_check.py +log. Point blockers have13 inclusion-minimal size4 sets and234 size6 sets. Matching control verified all16 inputs and both traces.

## Neutral-circuit search completed (2026-11-25T04:25:59.729226+00:00)

Four completed runs retained valid65/66-gate plane circuits at every accepted step and searched for legal compression to at most64 gates. Complete-run totals:88,777,735 proposals and5,613,331 accepted moves; no witness. Earlier interrupted prefixes preserve another5,681,362 logged proposals. Runs:65-state rotations/rewires (32,963,082 proposals),65-state dual-distributive relocation walk (33,168,082),66-state spare-gate walk (15,147,058), and genuine14-AND/52-OR alternate66 seed with canonical resets disabled (7,499,513). All complete logs, programs, seeds, final states, source hashes, and validation metadata are in `results/orch/search/neutral65/`. A fresh scalar evaluator independently checked each final saved circuit on all52 positive edges,704 maximal independent negatives, both derivative recurrences, and strictly earlier distinct operands. A separate bounded audit tried916 one-bypass candidates or two-bypass sequences with a valid first intermediate; two valid66-to65 first reductions and no64 result. These failed searches establish no lower bound. The `distinct` log field is cache-local, not a global unique-circuit census.

### 2026-11-25T04:36:03.958381+00:00 — completed local P4 certificate bridge

The concrete-CNF result is now connected to typed circuits by a fully compiled 2537-clause bridge in ReductionsBridgeChunks.lean (26 chunks), direct evaluator/derivative equalities, and checked operand-order normalization. ReductionsNoFive.lean proves noFiveDistinct: no exact-five binary AND/OR typed candidate on four inputs, with distinct earlier operands and output wire8, computes uv ∨ uA ∨ vD while both central formal derivatives vanish. The three final theorems use only propext, Classical.choice, and Quot.sound. Independent source, semantic, axiom, and archive review passed. Full logs and generation provenance are in search/p4_complete_bridge, manifest 6deea542ee429ce776af2eb8c8e83368dd2f0c9137ce92c5f424b2b3af3832cc.

P4SixWitness.lean separately checks the explicit actual six-gate circuit, its16 truth rows, binary/distinct/backward inputs, and both derivative zeros using ordinary decide. These are finite local controls, not a proof of L-meta-2602. The exact-five lower bound has no formal generic actual-Circuit extraction/prefix/padding lift, and the eight-input double-star computational exclusion remains without a kernel certificate. The original monolithic bridge was terminated after the chunked attempt exposed an assembly bug; first failure, corrected success, and termination outputs are all retained.
