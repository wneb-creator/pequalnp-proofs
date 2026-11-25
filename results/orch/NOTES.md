# Pilot 132 — L-meta-650

Goal: monotone fan-in-two circuit with at most 63 gates for the 26-variable point-line incidence graph of PG(2,3), 52 edges. Ordinary star construction costs 64. Lease owned by root only. Three reductions already live.

Each agent appends a timestamped short section; detailed artifacts go in results/orch/lemmas or job scratch. Read others before replanning.

## Circuit-search — exact finite tests
Enumerated the 52 minimal positive assignments and 704 maximal independent sets. Any monotone circuit matching these finite tests is correct on all 2^26 assignments by monotonicity. The files are in pilot-132/circuit-search/cases.json. Investigating 63-gate local resynthesis using these exact bit-parallel tests.

## 2026-11-25T14:40:33.146918+00:00 — Lean semantics

No apparent semantics shortcut: out-of-range/future wires read false, input list length fixed26, AND/OR fan-in≤2. Concrete correctness can be tested on52 positive edge assignments plus 704 maximal independent negative assignments. Exact data: `/tmp/oec/pequalnp-pilot-132/lean-semantics/extreme-inputs.json`. Existing reductions R_meta_650_1 and _713 already prove the monotonicity-based implication; _517 exposes the residual25-variable two-output strategy.

## 2026-11-25T14:40:44.839349+00:00 — pilot132_review: reductions and checker

- Three merged reductions already exist: R_meta_650_1, R_meta_650_713, R_meta_650_517. The explicit user/join limit is at most three live reductions per step, and desk says reductions_live=3. Therefore do not submit a fourth merely because reductions_open=true. Local guard checks reductions=true but does not enforce the public live-count cap.
- Updated upstream checker is version 4 and supports kind=reduce; initial version-3 observation became obsolete after upstream fast-forward.
- R_meta_650_713 splits into projective-plane geometry (nonincident subsets have one side of size at most three) and a 63-gate search satisfying edge positives and subset-completion negatives. Geometry is already checked in L_meta_6424.lean, whose ~36-line argument can be adapted into the permitted single file. Only Defs is allowed as project import.
- R_meta_650_1 uses the same geometry/tests and additionally restricts first gate to four symmetry representatives (one AND, three OR types).
- R_meta_650_517 deletes point 0, seeks a 61-gate residual circuit plus auxiliary wire agreeing with OR of neighbors when residual output is false, then adds one AND and one OR. Its hard child appears as L-meta-2215, itself reduced by R_meta_2215_37.
- Computed test compression: 756 raw small-side negative rows become 704 unique rows; only 704 are maximal. Together with 52 edge-positive rows they suffice for monotone correctness, using the checked geometry proof.
- L_meta_5254.lean establishes a 64-gate lower bound under HasLineDegree 26 (Ico 13 26) C 1 plus incident-pair/quad tests. A 63-gate witness must escape that syntactic line-degree-one class; focus on nonlinear sharing.
2026-11-25T14:40:51.711350+00:00
## Structural route — initial findings
- Existing reductions R_meta_650_1, R_meta_650_517, R_meta_650_713 already cover first-gate/certificate, residual-point/conditional-output, and maximal-independent tests.
- The circuit model is ordinary straight-line AND/OR fan-in≤2; invalid references read false. No semantic loophole found.
- Ordinary 13-star circuit needs 39 inner OR +13 AND +12 final OR =64 gates. A witness needs genuine sharing or nonhomogeneous intermediates.
- A blanket C4-free lower bound of |E|+vertex-cover−1 is not available from repository proofs; long-thread hypotheses fail (all 26 vertices degree4, girth6).
- Read https://pequalnp.com/papers/note-1 on 2026-11-25: its prior-work section explicitly says single-level bounds do not transfer to general monotone circuits, and multi-output Boolean sums with pairwise intersections≤1 need their naive monotone gate count. Therefore optimizing only the 13 neighborhood ORs cannot save a gate. External-paper exact figures UNVERIFIED independently: only the project’s secondary account was read.

## 2026-11-25T14:42:47.841736+00:00 — Baseline candidate ready

`L_meta_650.lean` now contains an explicit64-gate star circuit and a proposed Lean proof of the original statement with bound64, named helper `size64`. This is a partial checkpoint only; no claim of size63. Awaiting root cache setup before compiling. The candidate has39 neighborhood ORs,13 ANDs,12 final ORs; symbolic correctness avoids truth-table enumeration.

## Circuit-search 2026-11-25T14:43:59.117844+00:00
Implemented exact one-gate rewrites under downstream observability masks on all756 extremal assignments, with random topological reorder and perturbation restarts. Full63-gate searches still have best1 wrong assignment (52-edge graph minus one edge). Also searching arc4 subdivisionK4 core (10inputs12edges, target14g) and core plus4private lines (14inputs16edges,target18g); no exact witness yet. Shared deterministic seed64.json with SAT agent.

## 2026-11-25T14:46Z — root: prior search evidence

Read primary report https://github.com/brilliant-hq/pequalnp-proofs/discussions/12644 (redirects to open-goat same repo) on 2026-11-25. A previous 21-minute, 16-core annealing run also stopped at one failing extremal test. That report notes a failed 70-gate positive control, so its negative result is not evidence of impossibility. Our exact multi-gate window synthesis is a distinct route; requested positive controls for both solvers. No external unconfirmed numerical claim is being used as a theorem.
2026-11-25T14:46:31.362767+00:00
## Structural route — geometry and smaller search targets
- Computed all704 maximal independent sets on the exact posted incidence list. Type counts: (13,0)/(0,13)1 each; (9,1)/(1,9)13 each; (6,2)/(2,6)78 each; (4,3)/(3,4)234 each; (3,3)52. Only minimum covers13 are the full two sides; mixed covers have at least16 vertices.
- Important embedding correction: optimizing a bare induced subgraph can lose its saving when point stars are split between it and the residual. Full-row subsets embed cleanly: k selected point rows have4k edges and baseline5k−1 gates. A5k−2 circuit for them gives a full63-gate witness.
- Four-point arc representative(0,1,2,5):6pair-lines plus4private lines,16edges,14activevariables; target18gates vs19baseline. Bare subdivisionK4 withoutprivate edges is target14vs15 but not enough standalone forfull saving.
- Six-point representative(0,1,2,3,6,7):two3point lines plus9crosspair lines,24edges17activevariables, no private inputs; target28vs29. This gives3×3grid structure potentially richer thanarc4.
- Point-subset type representatives and counts saved to job scratch structural/point-subset-types.json. Circuit-search agent informed.

## 2026-11-25T14:47:24.146923+00:00 — SAT resynthesis

Built local Kissat-based CNF+CEGIS synthesizer. Pinned64gate star control passes all756cases. General14gate subdivisionK4 synthesis unresolved in first timed run; switching to63gate seed windows. Structural selector phase encoding improves planted control. Solver scripts and logs under pilot132/sat-resynthesis.

## Circuit-search 2026-11-25T14:47:44.437018+00:00 — controls and resource cap
70gate positive control recovered an exact solution from a63gate missing-edge seed plus7duplicate outputs in1.39seconds/6053iterations; independent Python check agreed on all756extremal cases.64gate control ongoing. Stopped redundant full-plane and arc4 searches to respect max2concurrent C++ jobs on3CPU environment. Only64control and theta5 active. Correct conditional-tap exact tests require4singleton special-line positives and197maximal false inputs of residual graph after deleting the4special lines; residual-output constraints add48positives+553maxfalse,802total includingduplicates. Prepared corrected two-output61gate search, not yet launched.
2026-11-25T14:48:54.751166+00:00
## Structural route — checked restrictions on any winning circuit
- Existing L_meta_2143 and L_meta_2145 forbid ≤63 circuits of syntactic degree≤1 in either bipartition side. L_meta_5254 establishes the64 lower bound under line-degree≤1 even on restricted tests.
- Qualitative constraint L_meta_8141: any correct≤63 circuit has some internal AND gate true on an input supported on a nonedge pair, allowing the two endpoints to coincide. Thus the gate may instead be true on a singleton; the theorem alone does not force a distinct spurious degree2 term. Search agents were informed of this clarification.
- L_meta_1961 rules out minimal candidates with≤1 pair ofnested AND gates. L_meta_3799 gives a shrinking step when every AND has≥2 readers. Therefore a minimal counterexample has a richer nestedAND pattern and some single-useAND. These are restrictions, not a global impossibility proof.
- A near-supergraph identity forθ4: OR_i((p∨q_i)∧(l∨k_i)) computes all12 edges ofthe4 length3 paths p–k_i–q_i–l plus the unwanted nonedge p·l in15gates, onebelowthe16gate bound forthe12edgegraph. Filtering p·l cheaply is unresolved. Bareθ4 doesnot embedwiththe1saving automatically due split-point-star costs.

## Circuit-search 2026-11-25T14:51:14.138255+00:00 — positive controls passed
64gate control passed45.781seconds/336105iterations;70gate control passed1.387seconds/6053iterations. Both independently verified on all756extremal inputs. No63gate witness. Preserved sources, cases and positive-control witnesses in results/orch/lemmas/circuit-search. Running only2jobs: exact conditional-tap61gate search and80-slot semantic-preserving search with≤67active gates. The latter alternates ordinary64star seeds and dirty67gate P4 seeds, using ab∨bc∨cd=(a∨c)∧(b∨d)∧(b∨c).
2026-11-25T14:52:20.015551+00:00
## Structural route — singleton dirty AND clarification
L_meta_8141 permits identical endpoints, so its dirtyAND may be true on a singleton; distinct nonedges are not mandatory. The archetype is (x∨A)∧(x∨B)=x∨(A∧B). Unshared ORparents make this removable withonegate saving; useful motifs needsharedparents. For two point-neighborhood ORs P_a,P_b, theAND has singleton lineab plus9products ofother lines througha/b. It safely substitutes the commonline only under endpointsa,b, notunder theother2points onthatline. Noncollinear borrowing needsanotherfilter. Fourcollinear fullpointrows areaforest(16edges17vertices), so cannotbeat19.

## 2026-11-25T14:54:25.424447+00:00 — SAT window results

- Unpinned8gate window in the64gate star solved in0.12s; decoded circuit independently matches all756extremal tests. Selector literal polarities preserve seed phase and greatly improve control.
- 63gate windows:8free and12free timed out after strengthened cases;12free reached no false positives but8missing edges. A24free window with all52positive tests and nonemptypositive-support constraints timed out120s. These are UNKNOWN, not UNSAT.
- DirtyAND16free window forced an ANDtrue on singletonline18 and finalfalse; CEGIS264wrong→28, then timed out120s at67cases. L_meta_8141 permits equal pair endpoints, so singleton dirtyAND cases must be included in any orbit analysis.
- Preparing incremental CaDiCaL to retain learning across added counterexamples. At most1solver active; future runs nice10 to prioritizeLean.

## Structural review — pruning refinement
Root identified, and structural reviewer independently verified, that an AND of two pure-side neighborhood ORs can be removed from a correct circuit: its values on every minimal positive edge agree with their unique common input literal, which is pointwise below the AND. Replacing all uses by that literal decreases outputs globally and preserves all positive edge inputs, hence preserves the monotone graph function. Thus shared OR parents alone do not rescue this pure-side singleton motif. Mixed parents with additional actual-edge support remain plausible; no blanket pruning theorem for those was proved.

## 2026-11-25T14:56:10.930345+00:00 — singleton-pruning helper compiled

`results/orch/lemmas/SingletonPruning.lean` compiles successfully (439 lines, Defs only). New lemma `erase_preserves_edge_function` proves: in a monotone ReadsBack circuit computing an edge function, a gate true on singleton p and agreeing with literal p on every minimal positive edge input may be erased and redirected to p. Monotonicity and ReadsBack persist, size drops by exactly one, and the full edge function is preserved. Erasure simulation helpers were adapted from checked L_meta_6142; no outside imports. Full compiler output is in SingletonPruning.validation.txt. This is a partial structural result, not the requested 63-gate witness.
2026-11-25T14:57:14.220428+00:00
## Structural route — mixed-support motifs and checkpoint review
- A plausible nonprunable singletonAND is (x∨u)∧(x∨v)=x∨uv whenuv is an actualgraph edge. It carries extra positiveedge support beyondliteralx. Search agent constructed andcomputationallyvalidated a66gate absorption seed usingx0∨x1y13 andmovingedge(1,13) into point0star. Direct x0∨(x1∧y13) gives a65gate version ifits twoORparents areunshared. Any saving must amortizeacross≥3noncollinear pointrows because twofullrowsformaforest.
- Small full-row target:3noncollinearpoints,12edges12activevariables,13gate target vs14baseline (C6core with2privateleaflines perpoint). No13gateconstruction found.
- Independent checkpoint artifact review: no credential-pattern hits in listed results/orch files, no network/process/credential access insearchsources. Recomputed exact52positive+704maxnegative cases frompostedstatement andmatchedcases.json. Validated seed64,slack-clean64,control64-run,control70-run: all756casespass, sizes64/64/64/70. README correctlylabels theseas computationalcontrols, notposted63gateproof. Timingfigures notindependently remeasured.

## Circuit-search 2026-11-25T14:58:33.604802+00:00 — independent audit and nonlinear seed
Read-only child search_audit independently regenerated all52positive+704maximal-negative cases and validated the802conditional-tap constraints. Known62gate residual+tap circuit scores0;61gate omitted-line seed scores exactly1. No semantic false-positive bug found. Raw slack-search solution JSON may still have80padded gates; active-cone pruning and independent verification are required before Lean. New66gate absorption seed t=(x0∨x1)∧(x0∨y13), used as point0 input while omitting edge(1,13) from point1 star, passes all756tests and survives singleton/duplicate pruning. Its obvious2gate t=x0∨(x1∧y13) normalization gives65, so this is a nonlinear starting point, not a new upper bound. Sources and witness are in results/orch/lemmas/circuit-search.

## 2026-11-25T14:59:31.031579+00:00 — minimality corollary compiled and axiom audit

SingletonPruning.lean now has 481 lines and proves `minimal_gate_has_offstar_edge`: in a minimum-size monotone circuit computing the edge relation E, every gate accepting singleton p must also accept an E-edge whose two endpoints both differ from p. The endpoints are not assumed or claimed distinct from each other. Derivation uses the checked erasure lemma and size minimality. Both final helper lemmas compiled and their axiom reports contain exactly propext, Classical.choice, Quot.sound. Complete logs are preserved in SingletonPruning.validation.txt and SingletonPruning.axioms.txt. Source SHA256 aa537d8a40363b1f344b99110e42ada90e9006a6399a96c085e929f43750f1fc. File frozen for checkpoint review.

## 2026-11-25T15:00:15.724031+00:00 — incremental solver ready

CaDiCaL3.1.0 built locally fromGitHub release source; singlethread,nice10. Unpinned64gate8window control solves0.08s andall756independent tests pass. Source-selector encoding now at-least-one only (as repo genmono.py); eachselected source agrees ontestedrows, so anyselector decodesvalidly onrows. Allwiresused andsourceordera≤b preserve identitypadding. Fullall-free circuits add adjacent-independent operator/first-source canonical ordering; windowproblems omitthatordering. Exact14gate subdivisionK4core synthesis nowrunningwithincrementalCEGIS. Greedynegativecovers:17maximalnegative rows coverall273nonedgepairs,28coverall1508independenttriples; available under job scratch. Scripts preserved inresults/orch/lemmas/sat_resynthesis.py andsat_incremental.py.

## 2026-11-25T15:03:22.994853+00:00 — Baseline64 checked

Named Lean module build passed (5149 jobs). `L_meta_650.lean` contains a checked64-gate baseline, 478lines, SHA256`f37b93c9e99fc12fa2eb9c99c0b4cdc8830539cfa2dd58595bc2668c0eee91cd`. No claim of posted63-gate theorem. Direct all-circuit simplification and broad propositional tauto were replaced by explicit wire equations and targeted simp normalization. Full build output preserved in `results/orch/lemmas/Star64.validation.txt`. Source frozen for independent review/checkpoint push.

## 2026-11-25T15:06:22.296574+00:00 — Extremal certificate wrapper checked

`results/orch/lemmas/ExtremalCertificate.lean` compiled with onlyDefs. It assembles checked geometry (6424) and monotonicity/test sufficiency (R713) into a generic candidate verifier with exactposted63-gate conclusion. This is conditional on a candidate passing tests; none claimed. Edge labeling independently recomputed from modularsum rule and matches all52posted edges. SourceSHA256`58476bfe97b70632b11031ed18703191228dee34917887ad810708824172e404`.

## 2026-11-25T15:07:37.461237+00:00 — structural exclusions and frozen baseline review

- Checked `L_meta_723.lean` proves the unconditional 15-gate lower bound for the 10-variable,12-edge subdivision of K4. Thus the 14-gate core SAT target is impossible. Setting four essential private leaf variables to0 removes at least four gates, so four full arc rows require at least19 gates; target18 is also impossible. Three noncollinear full rows similarly reduce by six private leaves to a C6 core requiring8, so target13 is impossible (baseline14). These deductions are mathematical, not newly Lean-checked in this job. First plausible full-row savings begin with five or six points.
- The six-point representative `(0,1,2,3,6,7)` has two triple lines and nine cross-pair lines: a subdivision of K3,3 plus two degree3 line hubs,24 edges and17 active inputs, with target28 versus29. A saving in this full-row graph embeds directly into the complete plane.
- Generic refutation route remains open: repository reduction `R_meta_1682_7` explicitly separates the missing lower bound of51 OR gates from the checked lower bound of13 AND gates. Existing OR-count lower bounds carry additional clean/top-form/line-degree hypotheses. No unrestricted theorem was found.
- Independently reviewed frozen baseline `L_meta_650.lean`: SHA256 `f37b93c9e99fc12fa2eb9c99c0b4cdc8830539cfa2dd58595bc2668c0eee91cd`,478 lines. New wire-evaluation helpers use append-only wire persistence and ReadsBack correctly. The size64 statement equals the posted statement after the sole63-to64 bound change. Exact52-edge list retained; only Defs import and permitted limit options; forbidden-pattern scan clean. Build log reports success. Checkpoint PASS as an honest partial, not a posted63-gate proof or proof PR.

## Circuit-search 2026-11-25T15:10:41.416086+00:00 — route retirement and next search
Conditional-tap stochastic search completed900seconds,2009restarts,6,025,471iterations, best1wrong test. Its exact61seed and802output-specific tests were handed to SAT as tap61-tests.json. Bare subdivisionK4 and full4arc searches are retired: structural agent found checked L_meta_723 proving core≥15;4privateleaf eliminations imply fullarc≥19. Adaptive full63 search is active; its best proper-dirty sample so far has9missing positive edges and no false positives after pruning, not useful progress. Prepared a positive-first superset variant with checked197/507false-positive starting seeds, independently audited. It starts when semantic-preserving slack hits its15minute cap.

## 2026-11-25T15:13:35.841667+00:00 — same-index AND-to-OR normalization compiled

OrReplacement.lean (286 lines, only Defs) proves `replace_preserves_edge_function`: when an AND gate accepts singletons p and q and equals literal OR(p,q) on every positive edge pair, replacing it in place by OR(p,q) preserves Monotone2, ReadsBack, total gate count, and the full edge function; the number of AND gates decreases exactly one. No assumption p≠q is required. Proof uses exact prefix/suffix simulation, pointwise decrease, and positive-edge monotonicity. Compiler and axiom audit both pass; only propext/Classical.choice/Quot.sound. Full logs saved beside source. SHA256 557e73aa13b1085b7be8c2ebc0c95373a2b5bc4055ef254486ece8712b3be90f. Source frozen; independent review requested from lean_semantics.

## 2026-11-25T15:17:58.630779+00:00 — SAT strategy replan

- SubdivisionK4target14 is already ruledout by checked L_meta_723, so stopped that route. It also rulesout18gatefourarc fullrows via4privateleaf eliminations.
- Conditional residual/tap target61:16gate and25gate windows both UNKNOWN at120s/180s strengthened rounds. New62gate twooutputcontrol solved0.29s, all802constraints pass.
- Full six-row block points[0,1,2,3,6,7] has17inputs,24edges,52maximalnegative tests. A28gate block lifts directlyto63fullplane by adding7remainingstars and7OR merges. Checkedpositivecontrol29 solved1.42s withall29gatesfree andall76cases, and itslift64passedall756fullplane cases. Target28initialrunUNKNOWN180s.
- Stronger normalizedtarget28 nowruns300s. Normalization: nonemptypositiveedge support pergate; singletonvacceptance requiresanacceptededgeavoidingv; exactlyonepositiveedge support forcesdirectAND ofthat edge. Structuralagent reviewedreplacementargument sound. Control29 withthese constraints solved1.72s (93rows, including17singletons).
- Independent artifact audit passed allsaved source/tool hashes, allcontrols, exact802taptest generation,6rowmetadata and64gatelift. Newnormalization variant isstillinscratch untilresults areknown.

## 2026-11-25T15:18:21.950454+00:00 — structural positive-superset seeds

- Generated exact-tested no-singleton supersets in job scratch `structural/superset-*.json`. Merging two point stars into `(a OR b) AND OR(N(a) UNION N(b))` costs8 rather than9, giving63 gates with all52 positive tests and290 maximal-negative failures. Noncollinear triple completion gives61 gates/435 failures; four collinear points61/506; six-grid points51/626; full bipartite product25/702. Each has zero singleton output errors; dual-side seeds agree on these counts. These are search seeds, not correct circuits.
- More targeted C6-sharing seed: rows0,1,2 with pair-lines13,14,25. Share the OR of those three lines across the three point rows, then add each row's two external line inputs. Neighborhood OR count falls9 to8, giving63 gates and only three extra nonedges `(0,25),(1,14),(2,13)`. Exact tests: all52 positives,210 maximal-negative failures, zero singleton outputs. Both side versions saved as `structural/superset-cycle6-share-side0-63g.json` and side1. General saving from sharing a completed rectangle R×S is `|E intersect (R×S)| - |R| - |S| + 1`.
- Do not infer an unrestricted quadratic-factor obstruction from connected nonincidence: unassigned nonedges invalidate that argument. A narrower mathematical obstruction applies to a completed cyclic rectangle when the second factor is itself bipartite quadratic; same-side terms evade it. Bare C6 plus both same-side triangles has a7-gate majority-of-three-mixed-ORs representation, versus8 for C6, but extending it to the three full point rows currently costs16 versus14. No under64 exact construction obtained.
- Independently reviewed frozen OrReplacement helper: SHA256 `557e73aa13b1085b7be8c2ebc0c95373a2b5bc4055ef254486ece8712b3be90f`,286 lines. Gate replacement by OR of two accepted singleton inputs preserves exact edge function under explicit positive-pair agreement; retains size and decreases AND count by1. Source/validation/axiom audit agree; checkpoint PASS as a conditional normalization helper only.

## 2026-11-25T15:20:13.110302+00:00 — positive-edge replacement compiled

PositiveEdgeReplacement.lean (312 lines, only Defs) proves two conditional normalization lemmas. General `replace_preserves_edge_function` replaces a gate by AND(p,q) when the old gate accepts pair(p,q) and agrees with that literal conjunction on every required edge pair. It preserves the full edge function, Monotone2, ReadsBack, and size; if the old gate was OR then OR count drops exactly one. Specialized `unique_positive_edge_replacement` uses explicit p≠q, E p q, and support exactly the unordered edge {p,q}. SAT agent confirmed the active pruning uses actual positive edges and excludes zero-positive-support gates. Both lemmas compiled and axiom audits list only propext/Classical.choice/Quot.sound. Full logs saved beside source. SHA256 b5d6c4a1a422855674a90040108c78896fe5d4b38e379262c5f0c947eab8bbfa. File frozen; independent review pending structural_math.
