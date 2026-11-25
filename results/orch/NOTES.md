# Pilot 73 orchestration notes

Task: L-meta-2089, leased 2026-11-25 06:35:43 UTC.
Exact desk statement is saved in /tmp/oec/pequalnp-pilot-73/desk-2.json.
Only root contacts the desk, renews, commits, pushes, and submits.
No Lean source changes outside the named proof file without coordinating with root; use task scratch for proof experiments.
Lean environment: ELAN_HOME=/tmp/oec/pequalnp-pilot-73/elan, prepend its bin directory to PATH.
Pinned Lean 4.36.0 and Mathlib cache ready; never lake update or build Mathlib from source.

## Current facts

- Posted target is an AND-output lower bound for order-3 projective-plane incidence.
- Prior circuit has at most 62 gates, two distinct selected wires, and their AND must match all incident pairs and all degenerate maximal false inputs.
- Goal is False.
- Only project import allowed: PEqualNP.Defs.
- Reductions enabled; three live reductions already reported.
- No open proof PRs reported by the desk.

## Strategy updates

Each agent should append a short timestamped result here using a separate append operation; avoid rewriting others' notes.


- 2026-11-25T06:37:58.921259+00:00 counterexample: enumerated all 8192 point subsets. There are 704 maximal false rectangles, 236 degenerate promised ones. All 117 nonincident pairs occur in promised negatives; all-point and all-line assignments are promised negatives. Hence every separator has the exact 52-edge degree-two shadow and no same-side/singleton minterms. Larger minterms remain unconstrained in 468 nondegenerate maximal rectangles. Data: scratch counterexample/promises.json.

## 2026-11-25 06:39:18 UTC — reduction review (status_review)

All three existing reductions of L-meta-2089 are open in the public desk snapshot (updated 2026-11-25T06:32:12.838Z). Join caps reductions at three per step; reductions_live=3 means a fourth is outside the stated allowance. No submission attempted.

| Reduction | Children / current status | Meaning |
|---|---|---|
| R_meta_2089_1 | L-meta-4239 CHECKED; L-meta-4241 open | Finite geometry classification; 63-gate AND-pair lower-bound core |
| R_meta_2089_2 | L-meta-4787 open; L-meta-4789 open | Single cold OR test on ≤60 gates; minimal family of at least two cold OR tests with C.size+2*K.card≤64 |
| R_meta_2089_826 | L-meta-5863 CHECKED; L-meta-5865 open; L-meta-5867 open | Gate replacement; false-OR quota; minimal circuit obstruction |
| R_meta_1684_1 | L-meta-2416 CHECKED; L-meta-2418 open; L-meta-2420 open | Correctness on one-line inputs; degree-one extraction; degree-one counting |
| R_meta_1684_2 | L-meta-2089 open; L-meta-2091 open | Final AND gate / final OR gate cases |
| R_meta_1684_3 | L-meta-2716 open; L-meta-2718 open | Degree-one lower bound; normal form up to point-line duality |

Checked files L_meta_4239.lean, L_meta_5863.lean, L_meta_2416.lean are present locally and can be copied into the target namespace when needed (only Defs+Mathlib are permitted project inputs). There is no fully solved reduction to apply directly. L2418 has public open PRs 8144/10913; L2420 PR4507; L2716 PR4938.

R2089_826's quota is conceptually an OR-gate sensitivity bound: a hot wire false at maximal false x must switch true when any zero input is enabled; its false OR dependency graph therefore needs at least count(false x)-1 OR gates. Even after proving this, the core L5867 retains the hard 63-gate lower bound. R2089_1's geometry proof L4239 is 144 lines and straightforward to inline if root chooses its direct core route.

Deeper cuts inspected: R4241_369 transfers from degenerate maximal rows to all nonincident degenerate rectangles; its geometry child L6824 remains open. R4241_644 abstracts circuits to trimmed families of false certificates but still assumes a 63-step cover-cost lower bound. R4787_1 normalizes fan-in/backward references; R4787_2 reduces negative tests to 20 cyclic-orbit representatives. R4789_407/418/521 give resource-count cuts but retain substantial obstruction hypotheses. None supplies a completed lower bound.

Correction: measured line counts are L4239=122, L5863=154, L2416=160 (the earlier 144 estimate for L4239 was incorrect).

## 2026-11-25 06:40:07 UTC — independent partial-preservation review (status_review)

Reviewed root maximal_pair_cover, structural weighted_cut, and geometry delta/incidence/separated_points/singleton_maximal/incidence_refl source. PASS for mathematical validity and namespace/forbidden-source rules; all helpers are isolated under PEqualNP.Outside.L_meta_2089, ordinary proof terms/tactics, no new axioms/sorry/native evaluation. Weighted descending-frontier induction charges each possible branching O gate once. Geometry uses ordinary decide on a finite proposition. The exact target theorem remains intentionally absent, so this is approval to preserve partial work only, not a full proof/checker/PR verdict. Structural build log predates cosmetic edits; rebuild the merged current source before asserting it compiles.

### 2026-11-25T06:41:34.278006+00:00 library_route

- Existing checked geometry L_meta_4239 and replacement L_meta_5863 can be copied into allowed module namespace. No direct circuit lower bounds available through Defs.
- Exhaustive Python geometry census: 704 maximal false rows; 236 degenerate rows, types (0,13):1,(1,9):13,(2,6):78,(3,3):52,(6,2):78,(9,1):13,(13,0):1. Remaining 468 generic rows are (3,4) or (4,3).
- Any independent input with at most 2 points or at most 2 lines extends to a degenerate row. Thus spurious minterms of a promised circuit need at least 3 points AND 3 lines.
- Building a new adaptation of L_meta_6206 plus copied L_meta_6208: AND rejection of only pair-generated degenerate rows already implies one operand accepts at most 12 nonincident point-line pairs. Scratch BadPairs.lean and complete build log under /tmp/oec/pequalnp-pilot-73/library-route/.

- 2026-11-25T06:41:52.346584+00:00 counterexample: Geometry.lean extended and Lean-checked (exit 0, empty log). Abstract monotone function satisfying promise rejects all nonincident pairs and all one-sided inputs; pair_truth_iff recovers exact incidence shadow. Scratch file /tmp/oec/pequalnp-pilot-73/counterexample/Geometry.lean, now 138 lines. Beginning bounded stochastic local optimization from a known 65-gate final-AND separator to test 63-gate candidates.

- 2026-11-25T06:42:19.696277+00:00: structural_proof compiled generic false_certificate in scratch structural/Structural.checked.lean. Every false wire has a raw-input false certificate B with |B| ≤ number of false OR gates in its prefix + 1. Handles forward/out-of-bounds references. Full build log structural-build-3.log is empty (exit 0). Geometry should force B to contain all zeros at closed independent-set inputs.

- 2026-11-25T06:43:29.217421+00:00 normal-form: compiled scratch normal-form/NormalForm.lean: nf_common_lines (kernel-checked unique common line), nf_rectangle (all-incident rectangle has a singleton side). Full lake env lean exit 0, build.log empty. A naive AND-birth biclique cover is invalid: P4 edge function xy OR yz OR zw = (x OR z) AND (y OR w) AND (y OR z); first AND creates bad xw, final AND deletes it, total 5 gates. Need global counting invariant.

## 2026-11-25 06:43:29 UTC — independent second partial review (status_review)

PASS for partial preservation, not full target completion. Reviewed structural false_certificate, geometry pair-truth/one-side rejection, and BadPairs.cross_bad/few_bad with copied combinatorial count proof. Gate semantics explicitly handle forward/missing references as false. Geometry keeps monotonicity/negative-row hypotheses explicit. Bad-pair cross incidence follows from pair-generated degenerate cuts, then ≤12 follows from finite projective-plane counting. Namespace isolation and forbidden-source scans passed; ordinary decide and decide +kernel are used, no new axioms or placeholders. Root must rebuild merged source.

- Structural.checked.lean: 294 lines, SHA256 c6c2690e88c64ae3bea58478f941bfa9f60950f7aec9de6f9c3a774bfbc2bd2c
- Geometry.lean: 131 lines, SHA256 b16dfed8f3ed6b286bb6aa018621cc977f8d9a1df5a0ab2823ff89c1eff34b38
- BadPairs.lean: 489 lines, SHA256 746e585969dd470927d0540769160a2d7ff8287a4cacc2bf0417192779d5b1f4

- 2026-11-25T06:44:26.098777+00:00 counterexample correction: final Geometry.lean line count is 131 (prior 138 was an estimate). Kernel check exit 0. Stochastic run still has only a near-witness: 63 gates, final AND, two missing positive edges, zero false positives. This is not a counterexample.

### 2026-11-25T06:45:47.331233+00:00 library_route checked component

BadPairsBridge.lean compiled with exit 0 and empty log (566 lines). Full source /tmp/oec/pequalnp-pilot-73/library-route/BadPairsBridge.lean. Namespace PEqualNP.Outside.L_meta_2089.BadPairs. few_bad_posted takes the desk-style negative mask, maximality, and only the collinear rejection branch; it concludes one selected wire accepts at most 12 nonincident point-line pairs. The combinatorial cardinality proof is copied from checked L6208; new cross_bad uses pair-generated degenerate negatives. pair_maximal and rel_iff are finite kernel checks. Parent and reviewer notified.
Caution: a single hot wire accepting at most 12 bad pairs need NOT cost 62 gates. Example p OR edgeFunction(G−p) uses 60 gates and accepts 9 bad pairs. The simultaneous two-hot-wire condition remains essential.

- 2026-11-25T06:46:34.504725+00:00 counterexample: bounded 240-second stochastic search finished without witness. DONE 9437433 143 8. Best 63-gate final-AND candidate misses two of 52 positive edges and rejects all 236 promised negatives. This is only a heuristic search, not a lower-bound certificate.

- 2026-11-25T06:46:48.978208+00:00: structural_proof compiled full OR quota: for a hot wire false on any closed incidence cut, count(false input bits) ≤ |I|+1 for some set I of false OR gates no later than the wire. Frozen scratch structural/Quota.checked.lean; full log quota-build-6.log empty, exit 0. Uses root maximal_pair_cover plus counterexample Geometry definitions. This proves the quota component of checked reduction R_meta_2089_826 (modulo the definition bridge), but not the remaining 63-gate core.

- 2026-11-25T06:47:48.901617+00:00 restriction-route: Checked generic exact_on_two_points: any monotone function satisfying the owned promise agrees with the incidence edge function on every assignment with at most two active points. Finite geometry proves each 0/1/2-point set is itself a degenerate closed row. Dual two-line exactness is compiling. Existing checked smallgraph gate-elimination engine in L_meta_8487 gives +1/+2 per input restriction; by itself it is too weak for 64 gates on 26 variables and requires exact semantics. Naive degree+1 deletion needs unproved exclusivity of shared neighbor-sum gates.

### 2026-11-25T06:48:12.434142+00:00 library_route literature check

Primary source read 2026-11-25: Jukna, Disproving the Single Level Conjecture (SIAM J Comput 2006), author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf. Section 3.5 establishes graph-cover lower bounds specifically for single-level circuits; its cited K2,2-free edge-count bound is not an unrestricted-circuit theorem. The published normalization counterexamples use saturated bipartite extensions, so they do not directly refute a normal form for this pure bipartite promise. No general unrestricted 64-gate theorem was verified.

- 2026-11-25T06:48:18.944028+00:00 normal-form correction: P4 masking formula has5gates, but y AND (x OR z) OR z AND w has4gates. Thus only naive per-gate birth classification is disproved; cost-preserving minimal-circuit normalization remains possible. For flag negatives F_(p,l), the6 true variables intersect another flag row in0 or2 positions; each variable occurs in12of52 rows. One final factor rejects≥26 flagrows, each requiring19 falseORs, but sharing prevents simply adding quotas.

## 2026-11-25 06:48:20 UTC — independent quota/bridge/restriction review (status_review)

Source/math review PASS for partial preservation. Quota correctly forces a false input certificate to contain every zero of a closed maximal negative row, then bounds its size by false OR gates before the selected wire plus one. The bad-pair bridge equates Singer-library rows with the posted mask and uses only the collinear negative branch. Restriction proves exact behavior whenever at most two points or at most two lines are active; any accepted input with no incident edge must therefore have at least three points and three lines. Namespace/forbidden-token scan passed; options are permitted declaration-local limits; ordinary decide/decide +kernel only. Quota and bridge frozen compiled snapshots were provided; restriction was reviewed while its owner completed build4, awaiting frozen compile confirmation. Full target remains unproved.

- structural/Quota.checked.lean: 577 lines, SHA256 e05e45693c5e1aaa7184d8bc5bf35edb1bd67bec36b707117b90bf7be40c8b7f
- library-route/BadPairsBridge.lean: 566 lines, SHA256 10f2d6c18cf5dde7eff63a97b7ad3850d8d87b8abd940dd6b0210fc3a349e5ad
- restriction-route/Restriction.lean: 270 lines, SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006

- 2026-11-25T06:50:19.717549+00:00 restriction-route: Frozen Restriction.checked.lean (270 lines; SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006) compiled exit0, build-5.log empty. Adds exact_on_two_points, exact_on_two_lines, and spurious_input_large (accepted independent input needs at least3points and3lines). Independent status_review checked this exact SHA. Root notified immediately.

- Restriction research read 2026-11-25: Jukna On Graph Complexity, https://eccc.weizmann.ac.il/report/2004/005/ and primary PDF /revision/1/download/, gives formula/depth bounds (Theorem7.3), not the needed unrestricted circuit-size bound. Amano–Maruoka 2006, https://doi.org/10.1007/s00453-006-0073-0, states a gap between general quadratic monotone circuits and single-level circuits; no generic single-level normalization theorem was found.

## 2026-11-25 06:52:04 UTC — independent singleton review (status_review)

PASS for partial preservation: singletonInput/forcedBad/badPairSet and small_bad_singleton_support. Two distinct input singletons force at least 17 nonincident pairs by the checked finite incidence calculation; monotonicity maps their forced sets into badPairSet, so a function with at most 12 bad pairs accepts at most one singleton. Bool order proof and local DecidableRel instances are valid; only permitted declaration-local limits, no prohibited source text. Full target still unproved.

Singletons.lean SHA256 7a1ccdbfe2fbe3adc608128f2d5471072129e0363fa76527c3abe13a90a8dad6. Restriction.checked.lean was confirmed compiled with empty build-5.log and matches previously reviewed SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006.

## Root replan 2026-11-25T06:55:14.722148+00:00

Compiled components now include a complete OR quota, exact behavior on inputs with at most two active points or lines, a <=12 bad-pair operand, and <=1 singleton support for that operand. None proves the required size bound.
Rejected shortcut: count each AND birth rectangle as a subgraph; later ANDs can suppress nonedges. The familiar 52+13-1=64 count requires an unproved normal form.
Next focus: structural minimality and sharing across two hot outputs; primary-source quadratic-circuit bounds; coupled restrictions; exact 10-input sunflower gadget search. Additional geometry will be added only when it supports a quantitative argument.

- 2026-11-25T06:55:21.917000+00:00 normal-form phase2 began06:52:37UTC. The best63gate stochastic candidate is algebraically the standard12-star remainder with (R OR p12) AND (R OR L12), deletingtwo neighbor-literal ORs. It is not yet a structurallynew near-witness. Singleton-factor branch: final singleton supports form a point-versus-incidentlines star, but extracting commonremainder from arbitrarycircuits remains unproved. Candidate transposition perspective: one-hot line restrictions give13linear OR4forms; obtaining39componentmerges plus25selector/connectivitycost is the missing weightedcharge.

### 2026-11-25T06:57:36.203364+00:00 library_route research update

Primary sources read via built-in web on 2026-11-25: Jukna, Disproving the Single Level Conjecture (SIAM2006), https://web.vu.lt/mif/s.jukna/ftp/single1.pdf ; Tarjan, Complexity of Monotone Networks for Computing Conjunctions (STAN-CS-76-553,1976), https://ftpmirror.your.org/pub/misc/bitsavers/pdf/stanford/Stanford_CS_TR_Collection_2025-12-12/OCR/CS-TR-76-553-ocr.pdf . Jukna labels the C4-free edge-count lower bound single-level. Section8 Problem8.2 asks for an explicit quadratic function with a superlinear arbitrary monotone circuit bound; this is historical evidence only, not a verified current-open claim. A uniform arbitrary-circuit C4-free m+vertex-cover−1 theorem would settle that historical problem on projective-plane families. Tarjan Theorems3/7/8 give 39 ORs for a multi-output network computing the 13 four-variable neighbor sums even when ANDs are allowed: transform into set union/subset computation, then pairwise intersection1 makes charged unions private. No cost-controlled extraction of these13 outputs from our single-output circuit is established.

- 2026-11-25T06:58:29.828924+00:00 counterexample structured phase: all15 partitions of4collinearpoints enumerated, yielding56 distinct partition pairs with disjoint added nonedges. Exact OR-sharing optimization within compressed block recipe gives minimum69 gates (range69–73), so this direct construction misses63. Four-collinear-point gadget reduced to an exact28-row frontier (12 positive,16 negative), each realized by posted tests. Z3 local11gate search has180s perrun limit; randomCEGIS priorrun timed out at72samples. No witness.

- 2026-11-25T07:00:44.345266+00:00: structural core investigation: local irredundancy from R2089_826 forces incomparable positive signatures at OR gates and incomparable negative signatures at AND gates; peeling the hot cone is already formalized by R2089_2. Per-row OR quotas alone do not combine to63 because false cones share. Naive star-count64 assumes a normal form not justified for arbitrary circuits with higher-degree junk. The repo public note explicitly limits its unrestricted exact graph bound to forests/cycles/long-thread graphs.
- The focused four-collinear-point gadget is theta_4 (four length-three paths between two hubs) under R implies OR Ai. Its28 canonical rows are indeed implied by posted promise; no additional freedom from ignored generic cuts within that gadget. No new fullproof or counterexample from structural route yet.

- 2026-11-25T07:01:30.964643+00:00 normal-form phase2: first-selected-output minimality can prohibit internaluses: OR(a,x) canredirecttoa (decrease, positivesunchanged becausea ishot); AND(a,x) canredirecttox (increase onlywhen a=false, masked byfinalAND). Directancestor outputcase collapses toonewire plusconstantTrue companion. This may organize pairminimality but doesnot supply63bound. OR-only39 counting alone isunsafe: ANDs canfilter supersets oflinearforms, trading manyAND gates for fewerOR gates; a valid argument mustcharge totalresources.

- 2026-11-25T07:02:08.431603+00:00 counterexample: exact collinear4point11gate synthesis returned UNKNOWN(timeout) at180s, no UNSAT claim. Found checked theta3 (three length3 paths,8vertices9edges) circuit≥12 in L_meta_516 and L_meta_7398, relevant sanity for gadget but not a solution of main64bound. Current distinct search freezes55gate prefix of best63 nearwitness and resynthesizes8gate suffix with60s cap againstall288tests.

- 2026-11-25T07:04:08.607595+00:00 restriction-route dedicated count attempt (started06:52:41UTC): exhaustive induced-subgraph DP (32,009,875 nontrivial states) gives31 for generic +1/+2 restrictions; adding first-gate reader multiplicity candidates raises this onlyto39 (deletepoint0:37, fixpoint0true:34). These are exploration outputs for exact graph functions, not Lean certificates or proofs under the weaker ownedpromise. Logs restriction-bound.log and restriction-bound-enhanced.log retained.

- 2026-11-25T07:04:56.584186+00:00 normal-form phase2: noquantitativebridge yet. First gate on two distinct rawinputs forcesbothinputsmultipleuses in a minimal separator (otherwise exact thin assignments lose an essentialvariable). This doesnot extend automatically tocomputed operands. Poolingneighbor sums ofkpointinputs saves a numberofORs equal to the cycle rank3k−|N(A)|+1 of their incidence subgraph; one mustcharge laterbadpair masks tothese savings, which is preciselythe unresolved globalnormalization.

- 2026-11-25T07:06:26.514498+00:00 normal-form phase2 aggregatequota deadend: the52flagrows give988requiredfalseOR certificates (19each), but an edgecomputingOR gate canbefalse onall52 rows, so per-row aggregation alone hascapacity52 andrecovers only19ORs. Rawpair gates arefalse on28/30/32flags dependingcrossincidence/same-side/nonincidence, but intermediateAND masks change rowpatterns; chargingthat extra capacityrequires anadditional invariant. No valid inequalityforces63totalgates yet.

- 2026-11-25T07:07:32.152858+00:00 normal-form phase2 singletonbranch: if a rawpointinput occurs onlyonce in OR(a,w), then w mustbe false on every pureline input; otherwise adding a neighboringline preservesw but makesa essential andmasked. On positives w can stillcarry alreadyaccepted edges, as in (R OR a) AND (R OR N(a)), so thisdoesnot eliminate singletonfactors. The canonicalcommonremainder factoring costs65; beating63 needs nonlinear sharing between R andneighbor-sum N(a), which ordinaryC4-free ORsharing forbids but arbitraryAND masks mayenable.

- 2026-11-25T07:08:17.674278+00:00 counterexample structured phase ended without witness: partition recipe minimum69; exactcollinear gadget11gate SMT UNKNOWN180s; exactsuffix8 SMT UNKNOWN60s. OR-only suffix repair algebraically cannotrestorethe6missingprefixedges: onlyfinalAND cancreate their quadraticterms, so theymustfitonebiclique/star, buttheyspan3points anddifferentlines. Extra internalANDsare necessary. Stable63gate nearcandidate and explicit NOT A WITNESS validation remain in scratch.

## Library-route research and exhaustive compatibility census (2026-11-25 07:09:16 UTC)

Completed all mutually closed cross-compatible bad-pair families, using a NextClosure enumeration on the 117 nonincidences. Cross compatibility is K((p,l),(q,m)) iff p~m or q~l; closure is N(N(A)). Started 07:05:03 UTC and completed 07:06:41.413200 UTC in 97.79 seconds, with 2,065,676 closed ordered pairs. This is executable evidence, NOT Lean checked. The largest min(|A|,|B|) is 12. Among closed pairs whose two sides both have cardinal at least 10, the only unordered size types are (11,18), (12,15), and (12,17), with ordered counts 1872,624,234 respectively. Therefore any compatible pair either has a side of size at most 9 or extends to one of these 2730 cases. Full script/log/summary and balanced records are under scratch library-route/badpair_concepts.py, badpair-concepts.log, badpair-concepts-summary.json, badpair-balanced.jsonl.

The balanced cases have five degree-shape types (the first two pairs are point/line duals): small side (11,18) has row/column degrees (9,1,1)/(3,1^8), or its dual; small side (12,15) has degrees (9,1,1,1)/(3,1^9), or its dual; (12,17) has degrees (3,3,3,3) on both sides. Every closed-family row has cardinal 0,1,3,9: for a fixed point p, its allowed lines must meet every point q appearing in a B-pair (q,m) with p not incident m. No such q gives 9, one q gives 3 (unless q=p gives 0), two distinct q give at most 1.

The (12,17) extremizer has a concise geometric description: choose a nonincident point p and line l. The 17-family is all nonincidences in row p or column l; its compatible 12-family is the nonincidence crown between the four points on l and four lines through p. Thus the existing bound 12 is tight.

Primary-source literature checked today: Jukna, Disproving the Single Level Conjecture (SIAM J Comput 36(1),2006), https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, constructs dense saturated graphs (each bipartition side becomes a clique) from Sylvester-type graphs or a perfect matching. These constructions do not apply to the bipartite projective-plane graph, and saturation contradicts the posted all-point/all-line negative inputs. Amano-Maruoka official abstract was read, but their original full construction is UNVERIFIED because accessible full text failed. Wegener, The Complexity of Boolean Functions, https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf, Exercise8.2 gives Bublitz's seven-edge graph x1x4+x1x6+x2x4+x2x6+x3x6+x4x5+x4x6; the gap there is formulas only (7 versus8), while circuit size is7 either way. It has a four-cycle and triangles, so does not provide a plane counterexample.

Tarjan's 1976 report The Complexity of Monotone Networks for Computing Conjunctions, Theorems3,7,8, and Wegener Ch6 Theorem6.2/Corollary6.1 independently imply all thirteen four-input line sums need 39 OR gates even in an unrestricted multioutput monotone circuit. The pairwise output-support intersections are at most one. This is stronger than an OR-only lower bound; the remaining issue is extracting these thirteen linear outputs from a single selector output without increasing total gate count. No primary-source bounded-degree singleoutput lower bound yielding64 has yet been found.

- 2026-11-25T07:10:32.636805+00:00 restriction-route: Explicit supporting counterexample to overstrong SINGLE-wire bound saved rectangularized-62.json. Merge pointpairs{0,1},{2,3} into two rectangles:62gates, all52positivepairs,12badpairs, zero singletonsupport. Not a witness for the ownedtwo-factor statement. Thus few_bad+singleton≤1 alone cannot force63gates.

- First-gate bound ceiling: even granting the59-gate optimum for every one-vertex-deleted plane graph, current firstAND/firstOR deletion bounds give62/61, below64total. Standard64-star circuit has initialOR inputs with4readers but privatecenter input whose deletion prunes1AND+1combinerOR+3privateORs=5gates. Private-ancestor pruning or degree-one extraction is necessary. For structured partition-form finalAND factors, N(P(p))∩N(Q(p))=N(p) lets one reconstruct all13lineforms using sharedlinearORs plusANDs, suggesting39linearOR count; arbitrarycircuits still lack this extraction.

- 2026-11-25T07:11:25.884853+00:00 normal-form correction to earlierOR-count worry: library-route verifiedTarjan/Wegener39OR lowerbound for the13exactlinearOR4outputs, evenwithANDs. Directcertificate explanation: remove anygate withsingletonsupport≤1 byits singleton/0 (preserveseverylinearoutput). Then eachOR infalsecertificate forlineℓ has≥2 singletonsupport insideℓ, socannot serveanotherline. Eachline needs3ORs. Theunproved bridge is extractingthis multioutputproblem fromthe single bilinear selector circuit withatleast25gates accountedelsewhere. No fullcore proof or counterexample afterphase2.

- 2026-11-25T07:11:49.197286+00:00 restriction-route conditional count bridge (mathematical, notLean): for two factors explicitly in point-partition rectangle form with k,l blocks and t common singletonblocks, paircorrectness gives eachcrossblockintersection≤1 and N(P(p))∩N(Q(p))=N(p). Consequently pointORs≥26−k−l and extracted13lineforms requirelineORs≥39. SelectorANDs≥k+l−t, combiningORs≥k+l−t−1 ift>0 (≥k+l−2 otherwise), andfinalAND1. Total≥65 for t>0, ≥64+k+l ift0. Stillrequirespartition-selector form; arbitrarycircuit extraction unresolved.

- 2026-11-25T07:12:40.104310+00:00 restriction-route sharper partition obstruction: any mergedpointblock containingp,q creates3badlines in rows p andq. Cross-bad compatibility forces the otherfactor to have no badpairs in those rows and≤1badline in everyotherrow r (all its badlines must lie in N(p)∩N(q)). Anymergedblock in the otherpartition wouldcreate≥3badlines in itsrows, impossible. Thus at leastoneof two point-partition rectangle factors mustbe theexactsingleton-star factor. No unconditionalnormalization/count theorem obtained. Dedicatedattempt began06:52:41UTC.

Library-route final source check: Jukna2006 Theorem2.3 gives unrestricted unbounded-fanin lower bound induced-matching-size+1, hence no useful64 bound here; its degree-sensitive bounds are only depth3. Jukna2025 Notes on Boolean Read-k and Multilinear Circuits, https://web.vu.lt/mif/s.jukna/ftp/readk-submit.pdf, Theorem1 proves the lower-envelope arithmetic transfer for read1 circuits. This identifies an additional hypothesis rather than resolving unrestricted Boolean idempotence. Do not silently apply it to the posted Monotone2 circuit.

- 2026-11-25T07:14:54.383214+00:00 restriction-route compiled MergedPair.checked.lean,107lines, namespaceMergedPair, SHA256 c9c877a6814f9581a06296fe6db5850f7a38905494a99747e9256c0d67e10f21. Empty merged-pair-build-1.log, exit0. bad_family_forced_common_line proves both pointindicesp,q incidentwith everyB-pairline and B-pointdistinctfromp,q wheneverAcontainsbothcross-neighborhooddifferencesofp,q. bad_family_column_and_card proves B liesin theiruniquecommonline column and B.card≤9. OnlyMathlib+Defs; finite geometryusesordinarykerneldecision. Rootnotifiedimmediately.

- MergedPair.checked.lean measuredlinecount correction:99lines (not107). Compiletimestamp07:14:54UTC; SHAunchanged.

## 2026-11-25 07:16:17 UTC — independent merged-pair review (status_review)

PASS for partial preservation. MergedPair.checked.lean uses finite projective-plane separation to force the line coordinate of every compatible bad pair through two distinct points, hence into their unique common line; nine nonincident points bound the second family by 9. Reviewed SHA256 c9c877a6814f9581a06296fe6db5850f7a38905494a99747e9256c0d67e10f21. Namespace/import/forbidden-source checks pass.

Axiom audit reports only propext, Classical.choice, Quot.sound for or_quota, few_bad_posted, spurious_input_large, and small_bad_singleton_support. Format checkpoint correctly refuses the absent main theorem. Checker checkpoint currently ends at verifier reading and has no final verdict yet. Full target unproved.

Refreshed public desk JSON at 07:14:59.216Z still lists core L-meta-5867 open with no PRs or reductions; no checked-descendant route is available.

## 2026-11-25 07:32:22 UTC — compiled single-factor limitation witness

restriction-route/OperandWitness.checked.lean passed Lean with ordinary `decide +kernel` (148 lines; SHA256 9d762b2bde2f3c30fc74ef44c204e82824d760830f80af4f810dc28d969af13a). Full log operand-witness-build-2.log is empty, exit 0. The existing Circuit is Monotone2, has 62 gates and valid output, accepts all incident pairs, accepts exactly 12 nonincident pairs, and rejects all 26 singleton inputs. It refutes ONLY the overstrong single-operand ≥63 shortcut, NOT the owned L-meta-2089 statement, which requires two jointly constrained factors.

Kernel checking caught that the earlier exploratory rectangularized-62.json used the transposed incidence orientation. The JSON has now been regenerated against the posted p = l + d, d ∈ {0,1,3,9}; SHA256 e89505eba67be6338e829ae992f5a19a541c279e83807b4f937620d5fec8bbd7. Correct bad pairs are (0,1),(0,5),(0,11),(1,4),(1,10),(1,12),(2,0),(2,3),(2,7),(3,1),(3,6),(3,12). Earlier concrete bad-pair lists in these notes are superseded. Generic graph-isomorphism invariant cost/count conclusions are unchanged.

Optional uniqueness of the only hot wire is being checked separately; preserve the already compiled snapshot immediately.

- 2026-11-25T07:32:56.817271+00:00 counterexample:20minute broad evolutionary phase completed07:12:28–07:32:28UTC. 181506495 mutations in3populations withRELAXED finalwireinequality, 15140404 inSTRICTpopulation. No computationalwitness. Beststrictcandidate misses2positiveedges andrejectsall236promisednegativecuts. Earlierrelaxedstatusisexplicitinconfigs; independentvalidatorchecks62priorgates,AND/ORbinarybasis,sequentialdefault-falsereads,distinct/in-rangefinaloperands,andall288tests. Canonicalorientationp=l+d independentlyregeneratedandmatchedallrows. Fullsummary,scripts,hashes,RNGseeds,logs,validatedcandidatesunder scratchcounterexample/.

## 2026-11-25 07:39:33 UTC — independent final-audit review

PASS for partial preservation only. The 164-line OperandWitness.unique.checked.lean snapshot independently compiled with the pinned toolchain via lake env lean, exit 0; the complete operand-witness-independent-review.log is empty. SHA256: 03e637580f9ee70686f999eef19a690696899d1befbae28d9f59442997b902df.

The added diagonal_hot_unique finite proof checks every wire below 88 against all 13 diagonal incident inputs. The general hot_unique follows because delta contains zero. Thus wire 87 is the only wire accepting every positive pair. This explicitly rules out using this particular 62-gate circuit as a witness for the target's two distinct operands. Independent Python evaluation exactly matched all 62 gates of the corrected JSON, all 52 incident pairs, the 12 listed nonincident pairs, and empty singleton support; both diagonal-hot and fully hot wire sets are [87]. Data saved in operand-witness-independent-data.json.

Imports, namespace, options, UTF-8, regular/nonexecutable file, and forbidden-source checks pass. Main helper file remains 1444 lines / 63424 bytes, SHA256 f302b961cb0cdde7b28aab9437b45798aa1559890878d2c78797133078a96b9d, and has no theorem PEqualNP.Outside.L_meta_2089. Therefore checker REJECTED (no-theorem) remains the correct final-state verdict; this is not a completed proof or refutation.

## 2026-11-25 07:43:07 UTC — independent private-quota audit

PASS for supporting-artifact preservation. Frozen LinearBound.checked.lean / PrivateQuota.checked.lean: 125 lines, 5469 bytes, SHA256 5ab93e646c7501d75703153252e258df603adbfdc3f6d1e5209e6fe04bc88af7. Independent lake env lean completed exit 0; private-quota-independent-build.log is empty. Independent axiom audit lists only propext, Classical.choice, Quot.sound for private_quota.

The proof does not normalize the full circuit: it changes predecessor certificates only in a query model containing the fixed false input and every singleton input. For a gate with at most one singleton support, the explicit hmono hypothesis ensures its support input is false on the chosen false row. For larger supports, existing gate_false_step supplies strict predecessor certificates and correctly handles forward/missing reads as false. The weighted cut then bounds support size by the number of false OR gates with support size at least two, plus one. No malformed-wire or empty-gate assumption is omitted.

The standalone artifact imports the previously compiled L_meta_2089 helper module. This is appropriate under results/orch/lemmas, but would need to be removed if the helper were merged into the final named PR file. This lemma does not extract thirteen linear outputs from the target's two factors, and does not finish the posted theorem.

## 2026-11-25T07:44:11.443999+00:00 — checked unrestricted multioutput linear bound

The linear_bound agent proved a stronger private false-certificate quota. Restrict the query space to the chosen negative assignment and all singleton inputs. A gate whose accepted-singleton support has cardinal at most one can then be bypassed by its unique input, or by an empty certificate; this is valid on that restricted query space and needs no circuit normalization. The certificate charges only false OR gates with singleton support of cardinal at least two.

For thirteen linear outputs supported on the four lines through each plane point, each output complement is false, so every charged gate has singleton support contained in that point support. Pairwise support intersections have cardinal one, making all charged OR-gate sets disjoint. Each output needs three OR gates, giving39 OR gates even when arbitrary AND gates are allowed. More generally, m supports of cardinal at least4 with pairwise intersections at most1 require3m OR gates. The proof derives wire monotonicity from Monotone2 and handles forward references/default-false semantics.

Frozen LinearOutputs.checked.lean:300lines,SHA256 d50e613fba1ddfb1353ea870c6811268395dc29f8996fdb3e985f51b5265d796. Build6 completed07:43:46UTC,exit0,emptylog. Scratch directory /tmp/oec/pequalnp-pilot-73/linear-bound/. The original L-meta-2089 statement remains unproved: extracting these thirteen outputs from its two joint separator wires with a valid cost accounting is still missing.

Root status refresh: public desk feed updated 2026-11-25T07:40:28.291Z still has L-meta-2089 and its hard core L-meta-5867 open, no proof PRs, and all three permitted reduction slots occupied. Latest upstream main was fetched and related new proofs inspected; no completed core dependency was found.

Primary-source follow-up read 2026-11-25: Alon and Boppana, The Monotone Circuit Complexity of Boolean Functions (1987), Section2 Theorem2.1 gives a legitimate-lattice distance lower bound through accumulated gate-error sets: https://web.math.princeton.edu/~nalon/PDFS/Publications/The%20monotone%20circuit%20complexity%20of%20Boolean%20functions.pdf . No finite lattice giving the needed63 bound was constructed. The full Amano–Maruoka paper remains UNVERIFIED because the DOI redirected to an inaccessible page.

## 2026-11-25 07:45:09 UTC — independent linear-output count audit

PASS for supporting-proof preservation and integration. Frozen LinearOutputs.checked.lean: 300 lines / 12411 bytes, SHA256 d50e613fba1ddfb1353ea870c6811268395dc29f8996fdb3e985f51b5265d796. Independent lake env lean exited 0; linear-outputs-independent-build.log is empty. A separate full-file axiom audit reports only propext, Classical.choice, Quot.sound for wire_monotone, linear_outputs_bound, and plane_linear_outputs_bound.

wire_monotone handles arbitrary sequential wire indices through List.getD defaults, without assuming all gate reads are backward. AND/OR evaluation is monotone even with zero or one inputs. The generic count explicitly assumes m sets of cardinal at least four with pairwise intersection at most one, accepted singleton inputs in each set, and rejection of its complement input at the corresponding output wire. Each private certificate has at least three OR gates. Every counted gate has singleton support of size at least two contained in that output set, so certificates for distinct sets are disjoint. All counted gates belong to the existing-gate OR filter.

planeSupport uses the posted p = l + d modulo 13 with d in {0,1,3,9}. The ordinary kernel decision verifies cardinal four and pairwise intersection one. Thus the resulting 39-OR bound is correct for the stated thirteen-output problem, even allowing AND gates. No extraction of these outputs from the target's two factors is asserted or proved. Remove only the standalone own-module import when merging these helper declarations into the named file. Forbidden-source checks pass.
