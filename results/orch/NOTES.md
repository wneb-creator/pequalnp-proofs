Job pequalnp-pilot-92
Gap L-meta-2592

Exact statement and desk response are in /tmp/oec/pequalnp-pilot-92/desk-001.json.
Only root holds and renews the lease.
Strategies: counterexample search; structural lower bound; reduction design; definition and existing lemma audit.
Append findings with strategy name and UTC time.

2026-11-25T13:46:05.264635+00:00 [definition audit]
FanInTwo restricts every gate to AND/OR/NOT and at most two operands. Gate evaluation defaults invalid or forward reads to false; empty AND and NOT produce true; NOT uses only its first operand. No semantic loophole found.
Three live reductions already exist for2592 (cap reached): R_meta_2592_408 normalizes wiring/output; _271 separates15 binary gates floor and1..4 NOTs; _318 splits after last NOT. Parent651 reductions are first-gate symmetry (_1), last-gate classification (_2), and monotone-vs-NOT (_7).
Checked L_meta_4725 proves exactly15+notCount C<=C.size for every FanInTwo Petersen circuit; its self-contained helpers use142188 bytes. L_meta_6194 proves15 non-NOT gates directly (144705 bytes). L_meta_1755 gives explicit20-gate monotone circuit. Many9-variable induced-Petersen lower bounds exist but no checked full19-bound found. Candidate file census and complete statements are in scratch audit-petersen-files.txt and audit-petersen-statements.txt.

2026-11-25T13:46:53.038368+00:00 [audit partial]
Prepared results/orch/lemmas/audit.lean: self-contained inline15 binary-gate floor from checked4725 plus new five_not_exclusion lemma. Uses namespace PEqualNP.Outside.L_meta_2592_aux, no Outside imports,145162 bytes/3227lines. Not yet compiled. This excludes all >=5 NOTs;1..4 remain.

Reduction-design audit at 2026-11-25T13:47:22.267122+00:00
- L-meta-2592 already has three accepted reductions (_271,_318,_408); desk reductions_live=3 is at documented cap. A fourth reduction is not appropriate even though reductions_open=true.
- _271 splits into binaryFloor and fewNot. binaryFloor is already checked in L_meta_4725 (3224 lines): 15 + NotBracket.notCount C <= C.size for Petersen edge function. FewNot is L-meta-4727, still decomposed further by R_meta_4727_1,_17,_53. _1 includes a vacuous no-NOT case proved as L_meta_8021, leaving the real case unchanged.
- _318 splits at last NOT. Exact generic compiler is already checked as L_meta_8295 (67 lines), so separator is the substantive open part.
- _408 splits normalization from normalized residual lower bound.
- L_meta_8367 internal graphLower proves unconditional HasCircuitSize(9, Petersen minus vertex9,15) is false. Final theorem has extra assumptions but internal bound does not. It reuses L_meta_2446 certificates (about6860 lines), so a restriction deleting >=4 gates from any <=19-gate Petersen circuit would finish.

2026-11-25T13:47:36.282343+00:00 [descendant audit]
L_meta_4727 (1..4 NOT case) is still conjecture in current public map; reductions _1 (tautological no-NOT split), _17 (semantic straight-line normalization), _53 (signed binary normalization) exist. L_meta_8021 only proves its impossible no-NOT branch. L_meta_5236 is useful: with nonedge OR x0||x2 supplied freely, Petersen still requires16 further non-NOT gates; its final theorem rules out18 remaining gates and3..4NOTs. L_meta_8033 proves Petersen with vertex9 removed requires15 total gates and13+NOT-count. No full1..4NOT result located.

[2026-11-25T13:48:29.332244+00:00] structural_bound: FanInTwo has only and/or/not and length<=2; forward or invalid wire reads false, NOT uses first input. No semantic loophole found. Generic same-size elimination of one NOT from a monotone single-output circuit is NOT established; literature bracket decomposition alone is insufficient. Existing L_meta_1433 only proves it for ten specified five-variable functions. Useful stronger route: L_meta_8367 graphLower proves no15gate arbitrary FanInTwo circuit for Petersen minus vertex9; proof uses monotone15 and signed/free-complement14 certificates. For full Petersen, a signed18 lower bound would settle L-meta-2592.

2026-11-25T13:48:34.949594+00:00 [petersen_search] Installed libz3.so.4 found; Python ctypes C API avoids downloads. Running19gate1..4NOT CEGIS search firstgate AND(edge0,1). Initial91patterns = all76 independent sets plus15 graph edges; every candidate will be checked on all1024inputs. Canonical commutative ordering and allgates-used normalization narrow witness search (UNSAT is not a checked theorem). Full log /tmp/oec/pequalnp-pilot-92/search-z3-shard0.log.

2026-11-25T13:50:52.043945+00:00 [audit stronger partial]
Prepared audit16.lean (285204bytes/4603lines) from5236 signed-circuit certificate. Added Extended.realizePins for original10inputs, yielding16+notCount<=size and four_not_exclusion. Namespace is PEqualNP.Outside.L_meta_2592_aux.Stronger; all helper declarations lemmas. Not compiled yet. Source5236 computes with long hex masks; checker source search found no numeral restriction, so constants retained.

Independent red-team review 2026-11-25T13:51:04.824543+00:00
- audit.lean: source L_meta_4725 preserved modulo helper namespace and theorem/lemma spelling; ≥5NOT exclusion is valid partial; no full2592 theorem.
- audit16.lean supersedes it: source L_meta_5236 prefix4539 lines preserved modulo namespace and theorem/lemma spelling. New realizePins uses ten raw pins (subset of original initial bank), obtains Live computation, and reuses atLeastSixteen. The count identity implies16+NOT≤size, hence≥4NOT exclusion atsize≤19.
- Independent Python checked all1024 truth-table rows: pins enumerate all ten-variable assignments bijectively and target equals exact posted Petersen expression.
- audit16 bytes285204/lines4603; no forbidden token, quote, attribute, own type/instance; allowed scoped limits only. Pending actual Lean build. It remains a partial artifact and must not be submitted as a full proof.
- Normalization child of R_meta_2592_408 already checked as L_meta_7389 (about320lines).

Root integration: named L_meta_2592.lean currently holds ONLY checked-candidate helpers, sixteen_binary_floor and four_not_exclusion. It does not yet declare the exact posted theorem. Independently reviewed by reduction_design; compilation pending. No proof PR is warranted until full target is proved.

2026-11-25T13:51:21.541020+00:00 [local optimization]
C++ full1024truth-table search running from all390 single-gate deletion/rewire variants of explicit20gate witness. Best starting19gate variant differs on6rows, missing edge(0,5); top20 variants saved scratch local-seeds.json and shared with SAT agent. Current best weighted error61/raw9 includes1unused NOT, so is not a counterexample. Exhaustive two-gate editing code prepared for a complementary finite neighborhood search.

2026-11-25T13:51:41.155193+00:00 [audit structural handoff]
Structural agent is pursuing retained first-gate operand projection: source5236 projected_bound lines583-590 gives L+constant-mass<=remaining gates; nineFloor is15. Restricting an annihilating retained input can leave two constant live wires after one paid gate and potentially force18binary gates. Audit agent limits work to16binary global lower bound and checked-source survey to avoid duplication.

2026-11-25T13:53:02.867431+00:00 [lean_setup] Installed pinned Lean4.36.0 in /tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux; source /tmp/oec/pequalnp-pilot-92/lean-env.sh for PATH/cache paths. All9 pinned dependencies fetched; targeted cache get decompressed3233 files. lake build PEqualNP.Defs passed with no Mathlib source compilation. Full logs task scratch cache-get.* and defs-build.*. Disk remaining roughly351MiB; avoid Mathlib umbrella imports.

2026-11-25T13:56:08.532590+00:00 [petersen_search] Encoder validated against fixed known20gate circuit: SAT and all1024assignments correct. LocalSAT around first19gate deletion seed with≤4gatechanges and1..4NOT found a30critical-pattern model, rejected on54full-table counterexamples, which were added. Global OR-nonedge firstgate shard remains unknown. Added sound cofactor-essentiality pruning to new script search-z3-pruned.py: a binary gate with two originalinputs cannot be sole use of either (otherwise absorption destroys essentiality under a cofactor). Known20gate witness still passespruning. Next: improved18used-gate seed with4falsepositive K4startriples supplied by local_optimize.

2026-11-25T13:56:20.672052+00:00 [local optimization improved seed]
Found 18 used monotone gates plus one unused NOT computing the target except four false-positive maximal independent triples: {0,2,6}, {3,5,6}, {0,3,9}, {2,5,9}. The four stars centered at vertices 4,1,8,7 cover12 edges. Remaining six variables are K4 edges; product of its four vertex-star ORs accepts all three perfect matchings (05,23,69) plus four unwanted star triples. Shared factorization S4*(x7 OR S1*S2*S3) gives the18gate near-witness. Exact circuit saved scratch local-improved-seed.json; SAT agent testing bounded edits. No witness yet.

[2026-11-25T13:57:26.864486+00:00] structural_bound: results/orch/lemmas/structural.lean compiled,223lines,8656bytes. normalize_pair gives a Petersen automorphism taking0 to arbitrary a and1(edge) or2(nonedge) to arbitrary distinct b. remains_essential gives two assignments differing only in b after any distinct a is fixed, with target values false/true. Both independently reviewed by reduction_design. Complete build log /tmp/oec/pequalnp-pilot-92/structural-build.txt is empty, exit0.

2026-11-25T13:59:44.253116+00:00 [local batch complete]
Full 600second stochastic run exhausted 1,667,631,432 candidate evaluations across66,703 restarts without a witness. This is heuristic evidence only, not a lower-bound proof. Best is the four-error K4 near-witness. Prepared uncompiled Defs-only local_near.lean with explicit18gate circuit and exact cubic-completion semantics; deterministic two-edit search and neutral-network CGP source are ready but paused for Lean CPU.

Canonical-bank strategy 2026-11-25T14:04:19.477369+00:00
- bank16.lean drafts a16binary residual lower bound for all8canonicalfirst signedgates (4operations, adjacent/nonadjacent pair), plus17residual lower bound forconjunctioncases ifnewgateused.
- bankfinite.lean compiled successfully: concrete1024row finite witnesses target_diff/other_stable for all8cases. Build log /tmp/oec/pequalnp-pilot-92/bankfinite-build.txt is empty(exit0).
- live_map.fragment.lean drafts injective Sig homomorphism transport of Live preservingcost, forpaircanonicalization.
- Genericduplicate-input charge is false evenformonotone targets; conjunction strengthening uses onlytwo constants, whileORcase needsPetersen-specific argument.

2026-11-25T14:05:56.439495+00:00 [audit16 build passed]
lake build PEqualNP.Outside.L_meta_2592 exited0. New kernel-checked16+notCount<=size and>=4NOTexclusion proven. Full stdout/stderr in scratchpartial-build.*. Root notified immediately forpush. NoLeanerrors or edits needed.

2026-11-25T14:06:28.330671+00:00 [K4 template symmetry]
The81 choices of binary OR pairings for four triple sums reduce to15 orbits under the K4 automorphism subgroup fixing the fourth center (S3). Canonical 11gate prefixes are in scratch local-prefix-orbits.json; SAT agent has them. Added a tiny uncompiled six-Boolean k4_cover_identity lemma to local_near.lean: product of four K4 vertex-star ORs equals three matching terms OR four star terms.

2026-11-25T14:07:26.136445+00:00 canonical-bank component COMPILED
- results/orch/lemmas/bank16.lean passes pinnedLean with emptylog bank16-build.txt.
- CanonicalBank.lower: foranyd:Fin4,j:Fin2, a Livecomputation using pinsplus bin(d,pin0,pin(j+1)) needs16binarygates.
- CanonicalBank.conjunction_lower: ifd=0or2 andextra isused, residualneeds17binarygates, becausebothpin0andextra projecttoconstants whilethenine-inputtargetneeds15.
- Readyintegrationafterarbitrary-paircanonicalization andfirstbinaryextraction; rawordinarytargetnotyetproved.

2026-11-25T14:08:09.166746+00:00 [independent local_near review by petersen_search] PASS for compiled56line2324bytecomponent: parsed18topologicalpositivefanin2gates, independentlychecked1024rows against exactPetersen function OR fourcubic terms; onlyextraaccepts69,104,521,548. K4coveridentitychecked64rows. LatestFanInTwo simpfix reviewed; allformatrulespass. It is apartial overapproximation, notacounterexample and notthepostedtheorem. Detailedreport scratchsearch-review-local-near.json.

2026-11-25T14:08:10.983519+00:00 [checked local component]
local_near.lean compiles under pinned Lean with no diagnostics. Independent SAT agent review verified18 legal positive gates, output27, full1024row cubic-completion identity, and64row K4 identity. Exact target differs only at69,104,521,548. This is a checked partial, not a counterexample. Root notified immediately for push.

[2026-11-25T14:08:12.869668+00:00] one-NOT investigation:
- Let the unique NOT negate a monotone prefix value g(x), and let the monotone suffix be H(x,b). Put A(x)=H(x,false), B(x)=H(x,true), so A<=B and f=A OR (B AND NOT g). If g<=f pointwise, B=f (replace the NOT output by true). If f<=g pointwise, A=f (replace it by false). This is a conditional semantic simplification only; translating it into gate savings needs a circuit constant-propagation lemma. Full Petersen monotone 20 minimum is NOT checked: L-meta-2590 is still conjecture, and1755 gives only the20-gate upper bound.
- For the18-gate K4 near-witness, simply masking the four false-positive maximal independent triples by a monotone guard cannot work: their strict supersets contain Petersen edges and must remain accepted. A suffix using the guard must restore those supersets through another positive path.
- Concrete finite obstruction: use the free bank of six raw inputs0,2,3,5,6,9; pair-ORs(2,5),(9,3),(6,0),(3,6); four triple-ORs(2,5,9),(9,3,0),(6,0,2),(3,6,5); and false. The target residual is x0*x5 OR x2*x3 OR x6*x9. Exhaustive64-row formula DP found no expression with<=3 binary gates and<=1 NOT. At3 binary gates it enumerated3767 monotone and49660 one-NOT truth functions.
- Sharing cannot rescue that4-gate residual: an all-used circuit with3 binary gates and1 NOT has7 total input slots. Any internal fanout raises internal edge count to>=4, leaving<=3 external bank occurrences. Exhaustive testing of all575 bank subsets of size<=3 found none whose values determine the target. With no internal sharing the circuit is a formula, already covered. This yields a computed obstruction for the fixed free bank, NOT a Lean-checked proof and NOT a lower bound for arbitrary Petersen circuits. Scripts/results: /tmp/oec/pequalnp-pilot-92/one-not-residual.py, one-not-residual-result.json, one-not-three-bank-result.json.

### 2026-11-25T14:10:02.466402+00:00 — structural agent: canonical transport checked
`results/orch/lemmas/structural_transport.lean` compiled successfully (exit 0; empty complete log `/tmp/oec/pequalnp-pilot-92/structural-transport-build.txt`). Finite row encoding inverses are kernel checked. `canonicalize_first` maps any distinct first input pair to `(0,1)` or `(0,2)`, preserving Petersen target and every signed-binary Live derivation. Canonical bank is exactly `pins ++ [bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero)]`. Final splice body: `/tmp/oec/pequalnp-pilot-92/structural_transport_body.txt`; scratch imports are harness only. Independent audit requested from reduction_design.

2026-11-25T14:11:37.243155+00:00 [deterministic local neighborhood]
Exhausted every one-gate deletion/rewire of the explicit20gate witness (390 seeds), then one mandatory NOT replacement and one arbitrary AND/OR/NOT gate replacement at a different position. Complete run made1,078,288,780 score evaluations (including initialization) and found no witness. This finite neighborhood result is not a global lower bound. Full log local-twoedit-all.log; source local-twoedit.cpp.

### 2026-11-25T14:11:42.435120+00:00 — structural transport membership extension checked
`transport_used.lean` compiled successfully, exit0 with empty complete log `/tmp/oec/pequalnp-pilot-92/transport-used-build.txt`; object `/tmp/oec/pequalnp-pilot-92/transport_used.olean`. `canonicalize_first_used` retains canonical extra membership, enabling the conjunction bank 17-tail bound. Original `structural_transport.lean` is frozen unchanged and independently reviewed PASS by reduction_design. New extension independent review requested.

## 2026-11-25T14:14:15.490600+00:00 — reduction_design exact residual bank
- `bank_all_pins.lean` compiled (empty complete log `bank-all-pins-build.txt`). Its 80 kernel-checked row witnesses prove every raw pin is required in all eight canonical first-gate banks. `exact_bank` forces residual S exactly equal to the eleven-word bank when the new gate is used. Structural agent independently rechecked all witnesses in Python and reviewed the proof: PASS.
- Independently reviewed plain live extraction, row transport, used-extra transport, and seventeen-floor integration: all PASS; scratch meta harness excluded from final source.
- Remaining hard case: first proper gate OR, one or two NOT gates. Generic duplicate projection charge is false.

2026-11-25T14:14:32.366869+00:00 audit: Cached 17-binary floor and >=3-NOT exclusion compiled; strict raw-pins realization and floor axioms exactly propext, Classical.choice, Quot.sound. Independent reduction_design review PASS. Plain fragments integrated into named source; awaiting full build.

2026-11-25T14:15:46.461236+00:00 [petersen_search completed templatecensus] All15OR-pairingorbits UNSAT for11fixedprefixgates +<=7additionalANDORgates (18total). ComputedZ3only, notLeanchecked andnotageneral lowerbound. Completecode,data,stdout/stderrlogs archived results/orch/lemmas/search_archive/. AIGcofactorencoderpreparedandvalidated20gatefixedcircuit onall512rows; next targetsx0=notx1andx0=notx2with<=15signedbinarygates.

### 2026-11-25T14:16:03.934649+00:00 — structural agent: next conjunction bound and dead projection route
Drafted `conjunction_tail_lower` and `first_binary_or_eighteen` in `results/orch/lemmas/conjunction_bound.lean`: every first signed-AND direction has residual binary cost≥17, including d3 by swapping inputs to d2. Compilation awaits completion of named17 rebuild, which removed prior named .olean. This draft is UNCHECKED.
The proposed nonedge-OR projection x0=¬x2 does not yield a16 signed-binary floor: local_optimize found and exhaustively verified a14-binary+1NOT realization. Do not pursue that lower-bound claim.

## 2026-11-25T14:18:22.463815+00:00 — reduction_design second-gate exploration
- Python-only exploration (not Lean certified), complete script/log `/tmp/oec/pequalnp-pilot-92/second-gate-classify.py` and `.txt`: for either canonical first OR there are 852 fresh/proper second-gate plus operand-retirement candidates. Row collisions eliminate 591 adjacent-pair / 587 nonadjacent-pair cases. The existing single-coordinate cofactor lower bound leaves 180 / 182 candidates at total binary budget17.
- Remaining raw-input non-OR second gates are disjoint from the first OR and preserve both operands, suggesting a commutation argument; hard cases consume the first OR output or add another OR. This is not a full residual proof.
- `first_or.fragment.lean` is an UNCOMPILED optional draft of non-OR residual17 and first-OR classification, stopped to avoid duplication with structural agent. Its only attempted test failed because named olean was intentionally absent during rebuild, not because proof terms were checked.
- Independently reviewed integrated17 source: five inserted bodies match compiled components; no forbidden syntax or scratch elaborators; exact full target theorem remains absent. Review PASS as partial checkpoint.

2026-11-25T14:19:35.933229+00:00 [nonedge projection route refuted]
Analytical identity after x0=not x2: target = x1 OR mux(x2,x3 OR x7,x4 OR x5) OR x8*(x3 OR x5 OR x6) OR x9*(x4 OR x7 OR x6). The mux absorbs original edges34 and57; edges01+12 become x1. This gives14 binary gates plus1 NOT (15 total), disproving the proposed nonedge projected15gate exclusion. Exact512row verification and independent reviews passed. Formal helper local_projection.lean proves size15,notCount1,FanInTwo,and exact projected semantics; pinned Lean passes with no diagnostics after cleanup. This does not refute the original held gap.

2026-11-25T14:20:55.675161+00:00 [independent archive audit]
Both search_archive and one_not_archive PASS. All50files UTF-8 text;38872bytes total;largest11567; recorded hashes match; no credential/environment dump patterns or binaries. Fifteen explicit solver runs all round0 UNSAT on30 critical rows, exits0; independent enumeration confirms81 pairings reduce to15 K4/S3 orbits and prefix semantics. Independently evaluated known21-gate seed and logged SAT model on1024rows:zero errors. Re-ran formula DP (3767 monotone/49660 one-NOT at3binary) and575 bank-subset tests:exact archived results, no witness. The sharing argument is sound for this fixed bank and gate budget. README explicitly excludes a general lower-bound or Lean-checked claim. Full audit report/script in job scratch archive-audit/.

2026-11-25T14:23:40.066122+00:00 [C6 audit]
Existing checked L_meta_4354 has base_C6 at1361 proving arbitrary FanInTwo HasCircuitSize6(C6)s implies8<=s, and final theorem1393 excludes7 gates. Its six-cycle edges01,02,13,24,35,45; adapted from L_meta_927 base_C6 at2281. Notified local_optimize and petersen_search that standalone7-gate C6 synthesis cannot yield a result; shared-bank variants remain distinct.

2026-11-25T14:26:19.344145+00:00 [one-NOT continuation] Archived fixed-bank scripts/full logs/results and exact-scope README at results/orch/lemmas/one_not_archive/. THEORY.md records endpoint mixed-AND/OR path constraint, two-gate suffix forms with a16-gate monotone prefix, raw-input NOT reduction to a16-gate nine-vertex circuit with positive OR/negative AND toggles, and a conditional adjacent-pair-AND negation exclusion using global17 plus first-AND18 bounds. These gate-count routes still need formal normalization/constant propagation; dead NOTs remain a separate monotone<=18 case. No full target proof.

### 2026-11-25T14:26:25.576957+00:00 — structural agent: restricted NOT-source elimination idea (unproved)
If the unique NOT negates a first AND on distinct original inputs a,b, then setting one input0 deletes the AND, NOT, and first effective NOT-use gate. Robust cofactor essentiality requires another effective use of each of a,b outside the initial AND; because the first NOT-use gate has fanin2, at least one of those extra uses is a different gate. Choosing that input should delete at least4 gates, contradicting the9-variable floor16 for a≤19gate circuit. This needs a strict/reduced normalization and a formal gate-elimination proof.
Caution: the18/nonOR result is about normalized signed-binary runs; actual AND of two negated original inputs normalizes to OR and remains in the2NOT case. Do not prune it from a complete search.

2026-11-25T14:28:06.166089+00:00 [neutral-network run complete]
900second CGP run made1,996,365,633 score evaluations, preserving exact truth while seeking lower active gate count. No improvement over20gate monotone baseline. Independent Python validation of final circuit is exact on1024rows, size20,noNOT, hence not a held-gap refutation. Next planned target is C6 with3 free opposite-vertex ORs plus7 unknown gates. Shared prefix with three external Petersen stars would turn any such NOT-containing completion into19 total gates.

2026-11-25T14:28:29.459709+00:00 [refutation route audit]
Public metadata confirms L-meta-2593 is exactly the negation of2592 (string equality verified); status conjecture. Current public gaps.json updated14:24:09Z posts2592 as check but omits2593 and parent651. L652 is unrelated. Therefore current outside-guard would reject an unposted2593 PR or refute-kind2592. Expected twin file/module L_meta_2593.lean / PEqualNP.Outside.L_meta_2593 follow repo format but are not authorized by a current posted row. Full exact statement and metadata URLs saved job scratch audit-refutation-route.json. No desk API calls or lease changes were made.

2026-11-25T14:29:10.255576+00:00 [search replan] Edgeprojection15AIG endedUNKNOWN: two sampledmodels rejectedon30and34of512rows, then3uninterrupted180secondtimeouts. Nonedgeprojectionhas independentlyvalidated14AIG witness fromlocal_optimize, closingthatlower-boundroute. IsolatedC6<=7routealreadyexcludedbycheckedL_meta_4354. Active smallertarget: C6getsfree3oppositeORs(0∨3),(2∨5),(1∨4), seek<=7newgateswithNOT; liftinguses3Petersenexternalstars+3ORs, total19. Encodercontrolandgenericlifterverifiedonknown20gatePetersencircuit/all1024rows. Exactsmallsearchstarted14:28:55,64constraints,600seconduninterruptedcheck.

2026-11-25T14:30:21.161886+00:00 [full17 named build PASS]
Full lake build PEqualNP.Outside.L_meta_2592 exited0, target805seconds,5149jobs. Named source5246lines/312347bytes is kernel checked, proving17+notCount<=size and>=3NOT exclusion. Complete logs partial17-build.stdout/stderr (stderr empty); root notified immediately forpush. Still no exact full2592 theorem.

### 2026-11-25T14:30:51.266396+00:00 — structural agent: conjunction18 and constant sweep checked
`results/orch/lemmas/conjunction_bound.lean` compiled exit0, empty complete log `/tmp/oec/pequalnp-pilot-92/conjunction-bound-build.txt`, emitted object `conjunction_bound.olean` in scratch. `conjunction_tail_lower` proves17 residual signed-binary gates for any first non-OR normalized binary operation, including d3 via swapping. `first_binary_or_eighteen` gives total≥18binary or an explicit firstOR residual.
`results/orch/lemmas/constant_sweep.lean` compiled exit0, empty complete log `/tmp/oec/pequalnp-pilot-92/constant-sweep-build.txt`, emitted object `constant_sweep.olean`. It generalizes L_meta_7073 constant propagation to arbitrary finite marked original wire indices, each anyBooleanconstant. Output gate count saves every gate with an effective read from a marked index. Semantics relation and valid references are preserved.
Both independently reviewed PASS by reduction_design; source frozen and root notified for immediate preservation.

2026-11-25T14:33:39.482584+00:00 [two-NOT structure compiled]
Frozen two_not_structure.lean compiles with empty logs (exit0); plain body two_not_structure.fragment.lean. For an actual FanInTwo circuit with<=19gates,exactly2NOTs,correct Petersen output: size=19,non-NOTcount=17, an extracted raw-pins signed Live run has17steps, and its first normalized gate is OR with16-step tail. After graph automorphism the tail is exactly the canonical11-word bank (all10pins+OR of0 with1or2). No claim both NOTs are live or actualfirstGateOp=OR. Independent review requested.

2026-11-25T14:34:57.337594+00:00 [C6/free-bank search]
First300second heuristic batch made2,865,736,646 evaluations, no exact C6 completion. Best monotone candidate misses rows12 and13 (edge23 alone and with vertex0). Replacing one AND input yields a two-false-positive completion at rows5 and21 (nonedge02 alone and with4). Stable candidates local-c6-twoerrors.txt and local-c6-overapprox.txt. A bounded second pass now requires exactly1or2 NOT gates to avoid monotone plateau and respect checked17+NOT bound. No further repeats planned without a new idea.

### 2026-11-25T14:36:09.441896+00:00 — structural agent: syntactic firstAND18 checked
`first_and_circuit.lean` compiled exit0, empty complete log `/tmp/oec/pequalnp-pilot-92/first-and-circuit-build.txt`; object `/tmp/oec/pequalnp-pilot-92/first_and_circuit.olean`. Independent review PASS by reduction_design. Public `Extended.realizeBank` handles arbitrary all-plain banks. `first_and_tail_binary_lower` gives17binary for tail supplied anAND of distinct originalinputs, whether the extra isused or not. `first_and_size_lower` proves actual circuit size≥18 whenever its firstgate is AND of two distinct valid originalinputs and it computesPetersen. No liveness or strict-read assumption is needed.
Final splice body saved as `results/orch/lemmas/first_and_circuit.fragment.lean`; scratch harness Batteries import/export-private aliases are omitted from thatbody. Official API documentation read2026-11-25: https://leanprover.github.io/hex/docs/Batteries/Tactic/OpenPrivate.html ; module-based export-private exposes alreadychecked constants without newaxioms.

### 2026-11-25T14:39:01.305682+00:00 — structural second-gate route assessment (paused after lease410)
No new code or builds started after parent pause. Feasible next lemma: in a≤17binary Live program, any independent signed-AND gate on two raw pins can be commuted to the beginning, contradicting checked first-nonOR≥18. For just the secondgate, let firstOR valueu and second raw-pin signedAND valuev be distinct/proper; tail S⊆pins∪{u,v} containsv. Ifu∈S, prepend the firstOR to thattail, yielding a run oftailcost+1 from pins∪{v} retainingv; conjunction_tail_lower gives≥17 residual, hence≥18 total. Ifu∉S, apply conjunction_tail_lower directly for an evenstronger bound. This uses Live.binary and erasingu, so should be a concise checked component.
Finite next-bank projection assessment: secondgate involving a firstOR operand often permits its0restriction to collapse both extra wires; when that originalpin remains semantically necessary, nineFloor15+oneconstant gives16tail and18total. But necessity can fail for the comparator bank OR(a,b),AND(a,b), so reorder the independentAND instead. For two ORs (a∨b),(a∨c), the sharedpin a is hidden only whenb=c=true; ifb,c adjacent, target is alreadytrue there and a neednot be necessary. These geometries are genuine residual cases. Disjoint rawORs or OR ofa thirdpin withfirstOR require one constructiongate after any coordinateprojection, givingonly17total by currentmass method.
One future broad form: every root binary gate (both operands rawpins) in a≤17 normalizedbinary circuit must be OR. This is stronger SATpruning than firstORonly, but requires formal commutation or genericReach translation before claiming checked.

## 2026-11-25 14:39:28 UTC — checked one-NOT subclass

lean_setup compiled four frozen components one_not_semantics, one_not_compile, one_not_eliminate, one_not_petersen. Full empty build logs and scope: results/orch/lemmas/one_not_build/README.md. The restricted first adjacent input AND + later consumed NOT of that AND requires >=20 gates. First three reviewed PASS; final review requested. Parent notified; paused on lease410.

2026-11-25T14:39:30.059088+00:00 [shared-C6 search complete] Z3 returned UNSAT in390.147s for three free opposite ORs plus at most seven new gates with1..3NOT, all64rows. This closes the restricted19-gate Petersen lifting family computationally, without a Lean certificate. Full source, log, known control and verified20-gate lift archived in results/orch/lemmas/search_shared_c6/. Upon root lease410 report, remaining NOT-prefix driver PID10384 and child PID12841 were paused with SIGSTOP; no search remains running.

## 2026-11-25 14:41:26 UTC — L-meta-1886 map rigidity checked

map_rigidity.lean compiles exit0, empty full logs in lemmas/map_rigidity_build/. Arbitrary successful pinmap must be bijective, proved by20 explicit finite witness pairs. No circuit legality or size assumptions required. Independent review requested. Root informed for preservation.

2026-11-25T14:42:24.127695+00:00 [petersen_search] New owned gap L-meta-1886: started exact CaDiCaL shard with identity mapping, free OR(0,1), first counted gate NOT x0, then 17 arbitrary AND/OR gates. Cofactor monotonicity reduces complete constraints to 38 minimal-true/maximal-false rows; any SAT is independently checked on all 1024 rows. Positive control with 21 counted gates validated. Search timeout 600 seconds; log search-1886-or-not0.log. Old 2592 NOT-prefix driver 10384 and child 12841 were first paused at withdrawal, then killed; their full logs remain in scratch.

## 2026-11-25T14:42:44.731791+00:00 — reduction_design L1886 consumed supplied-AND NOT
- `supplied_and_not.lean` / `.fragment.lean` compiled with exit0, empty complete log `supplied-and-not-build.txt`. Identity-order pins, supplied x0∧x1, explicit NOT[10], monotone suffix, and explicit direct consumer imply seeded size≥19; hence exact counterexample at size≤18. Proof prepends the physical AND and invokes checked20-gate theorem. Lean_setup independently reviewed PASS.
- Independently reviewed new `map_rigidity.lean`, one-NOT elimination/Petersen components, and shared-C6 archive: PASS within each stated restricted scope. C6 is computed-only Z3 UNSAT; independent positive-control checks gave zero errors on64/1024rows.
- L1886 has three existing live reductions (_17,_74,_317), so no new reduction slot. Arbitrary pin maps reduce by surjectivity to permutations; ANDseed binaryfloor17 leaves≤1NOT and ORseed binaryfloor16 leaves≤2NOT at budget18.

## 2026-11-25 14:45:29 UTC — arbitrary-map consumed supplied NOT checked

InputRelabel and ArbitraryMapSeedNot compile exit0; all full logs archived in lemmas/input_relabel_build/. The latter extends SuppliedAnd≥19 to any ten-pin map, with explicit consumed NOT[10] and monotone suffix. Parent/integration agent notified, structural reviewer requested. InputRelabel independently reviewed PASS.

2026-11-25T14:46:00.151931+00:00 [1886 integration frozen]
New named lean/PEqualNP/Outside/L_meta_1886.lean:6436lines/363579bytes. Renamed checked2592base namespaces, added checked conjunction/second-nonOR-root/firstAND, constant-sweep and one-NOT semantic/compiler/elimination/Petersen, two-NOT structure, MapRigidity, InputRelabel, suppliedAND-NOT and arbitrarymap extension. All scratch imports/export bridges omitted; renamed second_root_nonOr_lower to second_rt_nonOr_lower to obey forbidden-token rule. Imports only three specific Mathlib modules plusDefs. Exact full1886 theorem remains absent. Manifest job scratch integration1886-manifest.json; independent final concatenation review requested from structural_bound. Root handles preservation and fullbuild. Old2592source unchanged.

## 2026-11-25 14:46:54 UTC — ignored NOT operand covered

seed_not_operands.lean compiled exit0; source frozen and structural review requested. Extends arbitrary-map suppliedAND lower/exclusion to NOT(10 :: rest), preserving count and semantics. Full empty logs archived in lemmas/input_relabel_build/.

2026-11-25T14:47:26.476515+00:00 [local_optimize independent 1886 search review]
PASS: search-1886-firstnot.py and search-1886-decode.py. Exhaustively checked AND/OR CNF truth cases and selector polarity, commutative operand ordering, fixed-NOT bank semantics, and decoder wire indices. Independently checked critical-row coverage on every input for every NOT source: 30 monotone, 38 raw-input-NOT, 46 supplied-edge-NOT rows; the final-OR free-AND template uses 29 rows and covers all 768 care inputs. All SAT candidates still require full1024 decoder validation. This reviews restricted templates, not arbitrary-circuit completeness. Report and file hashes: scratch local1886-review-search.json. Lightweight preprocessing of all120 automorphisms of the known20gate witness plus every valid greedy gate removal under the freeAND care domain reached19 gates, not the desired17; seeds/report in local1886-and-care-seeds.json and local1886-and-care-analysis.json. No new heuristic process launched.

2026-11-25T14:50:56.553164+00:00 [local_optimize ordered SAT symmetry review]
PASS for optional lexicographic ordering by (maximum parent, minimum parent, operation). Exhaustive normalization of all4608 three-gate/two-input circuits preserved truth and produced sorted keys;600 finite selector/order cases matched the emitted CNF. Proof: remove unused gates; choose minimum ready key; newly ready gates reference the newest output index and thus have larger maximum-parent keys than all previously ready gates. Output remains last because all retained gates are its ancestors. Identity-output padding preserves order. Standalone control canonicalizer asserts output-last and assumes unused-gate removal separately. Report/hashes: scratch local1886-review-ordering.json. Suggested sound all-used unknown-gate clauses to SAT agent. Distinct17gate freeAND care-domain heuristic prepared in local1886-care-search.cpp but not compiled/launched while named build and exact shards occupy CPUs.

2026-11-25T14:51:16.490394+00:00 [petersen_search] New L-meta-1886 CNF encoder independently reviewed by local_optimize (reports local1886-review-search.json and local1886-review-ordering.json in scratch). Identity-map cases: 18 monotone gates over free edge OR have 30 critical rows; fixed first NOT of a raw pin plus 17 monotone gates has 38; first NOT of the free edge signal has 46. A separate free-AND final-OR template has 17 unknown monotone gates and 29 critical rows. All critical-row dominance checks exhaust all 1024 assignments. Optional sound symmetry orders unknown gates by (max parent, min parent, operator), and liveness removes disconnected unknown gates; identity gates permit padding. Oversized known controls for ordinary, first-NOT, final-OR, ordered and live modes all passed full truth-table validation. Current two 600-second searches remain unresolved; no counterexample or lower-bound certificate claimed.

2026-11-25T14:52:30.568711+00:00 [local_optimize NOT-source pair orbits]
For a first unknown two-input guard followed by NOT and a monotone suffix, the unordered edge{0,1} stabilizer has8 automorphisms and10 raw-pair orbits. Six nonedge AND reps: (0,2),(0,3),(2,4),(2,6),(2,8),(3,7), each49 complete critical rows after fixing both source bits. Four additional OR reps: (0,1),(0,4),(2,3),(3,8), each46 rows. OR(0,1) already supplied in the OR-bank branch, so its NOT is a one-gate direct bank-NOT template. Equal inputs reduce to raw-NOT templates. All1024 dominance cases independently verified for each representative. Full orbit members and stabilizer are in scratch local1886-pair-orbits.json; shared with petersen_search.

## 2026-11-25 14:53:00 UTC — arbitrary dominated source checked

dominated_source and dominated_source_witness compiled exit0 and independently reviewed PASS. Any source index and arbitrary pinmap covered. If consumedNOT source implies target and suffix is monotone, suppliedAND needs>=19 gates. Contrapositive: exact<=18 circuit must have source true on an independent input. Logs/scope in lemmas/dominated_source_build/. Parent and integration agent notified.

### 2026-11-25T14:53:14.156887+00:00 — structural suppliedOR conjunction projection checked
`results/orch/lemmas/or_seed_conjunction.lean` compiledPASS exit0, empty complete log `/tmp/oec/pequalnp-pilot-92/or-seed-conjunction-build.txt`. Object in scratch. Body `/tmp/oec/pequalnp-pilot-92/or_seed_conjunction_body.txt`. For freeOR01 seedu and firstcomputed v=u∧pinp oru∧¬pinp withp outside0,1, bothendpointpins are necessary and distinctfromv. Restrict0=1=0: target maps to checkedgraphGoal383 floor13; allthree wires becomeconstant, so residualbinary≥16 andsuppliedtailbinary≥17. No duplicatewire charging. Independentreviewrequested; sourcefrozen.
Python independently enumerated all1024-row functions toconfirm211distinct freshnormalized firstcomputedfunctions afterfreeOR01:135raw-pin nonORs,44rawORs,32seed-only functions (fourfamilies×8outsidepins). RootnonOR135 excludedbycheckedsecond_rt lemma; thisnewcomponent excludes16 seedpositiveconjunctions. Pending:8negatedseed∧pin,8seedORpin,44rawORs;12overlappingrawORs have a simpleronecoordinateprojection route assignedseparately.

## 2026-11-25 14:55:31 UTC — actual source15-row guard checked

prefix_monotone and source_guard compiled exit0; prefix independently PASS, source_guard review requested. Under monotone prefix+suffix and direct consumption, any exact<=18 suppliedAND circuit has source true on one of15 maximal independent rows. Arbitrary pinmap/source index and ignored NOT operands covered. Full logs and Python-only five-orbit computation archived in lemmas/dominated_source_build/.

## 2026-11-25T14:58:41+00:00 — reduction_design: guard classification and obstruction

`independent_guard.lean` compiled with kernel finite checks and was independently reviewed by lean_setup. For a monotone guard, domination by Petersen is equivalent to being false on the 15 listed maximal independent rows; any failure has a witness among those rows. The object is exported in the job scratch directory. The list uses ordinary vertex bit positions, not Extended truth-table pin encoding.

A proposed universal negation-elimination theorem for a quadratic target with arbitrary supplied positive roots is false. Conceptual obstruction: given any monotone H with at least five essential variables, supply the two positive functions A=z AND H and B=z OR H for free. Then H=A OR (B AND NOT z), using three additional gates. A positive completion must read every essential original variable in its output cone: for an essential-coordinate flip x<y, compare z=1 at x against z=0 at y. A and B are respectively 0 and 1 on both, all other original coordinates agree, and z decreases. Omitting the flipped variable would force the wrong monotone order. A connected fan-in-two three-gate circuit has at most four distinct source leaves, so cannot read five essential variables. This is an obstruction to a general relative-bank theorem only; the cost of producing A and B is excluded, and this is not a gate-counted Petersen counterexample or a Lean certificate.

Independent review PASS for structural_bound's `or_seed_conjunction_used.lean`: both endpoint pins, the used supplied OR, and used conjunction output are four distinct roots that all become constants under the adjacent-two-vertex deletion slice. The existing 13-gate signed floor therefore yields a 17-gate residual bound. All liveness assumptions are explicit.

## 2026-11-25 15:01:38 UTC — dual source dominance checked

dominating_source and dominating_source_witness compiled exit0 and independently PASS. F<=source allowsNOTfalse deletion and implies>=19 gates; cheap exact consumedNOT candidates need sourcefalse on some positive input. All pinmaps/source indices/ignored operands covered. Logs/scope in lemmas/dominating_source_build/. EdgeGuard generic15edge characterization independently reviewed PASS; actualsource composition awaiting imported object.

## 2026-11-25T15:03:55+00:00 — reduction_design: overlapping OR and edge guards checked

`overlapping_or.lean` compiled with exit0 and an empty full log. With free OR01 and a second raw OR0p where 1 is nonadjacent to p, any signed Live residual requires at least16 gates; symmetrically for OR1p with 0 nonadjacent to p. No use assumption on either supplied OR is required. The proof forces the shared endpoint raw pin by two rows, restricts it false, and charges one constant against the checked nine-variable floor15. The symmetric case uses the explicit edge-swap automorphism. This covers the twelve nontrivial overlapping OR cases, plus harmless redundant cases.

`edge_guard.lean` compiled with exit0 and an empty full log, and its scratch object is exported. A monotone guard is above Petersen iff it is true on the15 edge rows; otherwise some listed edge row has false guard and true target. Coverage uses the15 disjuncts of the exact edge function and tiny10-index kernel support certificates. This complements `independent_guard`. lean_setup independently reviewed the final symbolic coverage proof.

Computed only: under the eight-element supplied-edge stabilizer, edge-row orbits are [3], [6,17,33,66], [12,24,132,160,288,320,528,576], [264,640]. These orbit reductions are not Lean-certified and are not needed by either proof.

## 2026-11-25 15:04:11 UTC — actual source15-edge witness checked

source_edge_guard compiled exit 0 before the v2 deadline. Under monotone prefix and suffix, direct consumption, arbitrary map/source and ignored operands, an exact circuit of at most 18 gates with supplied AND forces the source false on one of 15 edge masks. Combined with SourceGuard this gives finite incomparability witnesses. Complete empty logs are in lemmas/dominating_source_build/. Final symbolic EdgeGuard coverage and SourceEdgeGuard composition independently reviewed PASS.

### Structural continuation 2026-11-25T15:08:10.052034+00:00
- Negative-seed transport now compiled and independently reviewed: every fresh pin_p AND NOT(OR01) first computed gate leaves residual signedbinary cost at least16; forced pin liveness is proved via10 finite witnesses. Combined with positive-seed conjunction, raw nonOR and overlappingOR cases, remaining second-gate fresh values are40 positiveOR shapes (28 disjoint raw pairs,4 exceptional overlaps,8 triples).
- V2 exact splice/hash review passed; partial scope explicit, target theorem absent.
- mode_extract_transport compiled/reviewed: Live mode preserved, allowed u d retained. mode_realize compiled: actual Monotone2 circuit realizes Live false with cost≤size; scratch private exports excluded from final fragment. MonoNine floor remains pending full compilation, so ModeFloor compositions take external floor as an explicit premise.

### 2026-11-25T15:12:57.837946+00:00 — status agent: monotone certificate and v2 integration

- Frozen named1886 v2 has421238bytes7652lines; all15 post-v1 appendices compiled individually and independently reviewed, exact splice review PASS. Root owns full build/push. Exact gap theorem remains absent. Manifest is scratch/integration1886-v2-manifest.json.
- MonoNine standalone extracts the8367 monotone certificate into479128bytes with1336 declarations. First compile exposed10 omitted field accessors; all10 were restored exactly, re-reviewed, and the full build restarted. Current build has no errors; MonoNine.lower16 is pending compilation.
- Generic MonoBank lower/cofactor helper compiled and reviewed PASS: arbitrary mode u and floor L give canonical bank L+1, and used conjunction bank L+2. Structural agent's mode-preserving extraction/transport and floor composition combine this into monotone raw/AND18 and OR17 once floor16 is available.
- NineActual split/conditional lower compiled and reviewed PASS: any actual9-variable circuit of size≤15 yields monotone Live≤15 or signed Live≤14. Existing signed certificate plus the pending monotone root will establish actual9-variable lower16 without duplicating8367's signed certificate.
- Fresh upstream audit from aa08d391 to f7f0ee83:379new Outside paths, only6098 Petersen-labelled proof;18new8/9 graph candidates checked. No new induced Petersen subgraph bound found. L10832 gives15 total gates for Petersen-minus-one-vertex-minus-one-edge,445914bytes; full census and metadata in scratch/audit-new-*.
- Independent local1886-search and local1886-repair archive reviews PASS, plus mixed240-template heuristic preparation. All data claims are restricted finite computations, not general or Lean lower bounds.

2026-11-25T15:14:59.951256+00:00 [petersen_search] All first-wave L-meta-1886 searches ended UNKNOWN at 600 seconds: raw-NOT-x0/free-OR, monotone/free-OR, ordered monotone/free-OR, ordered free-AND final-OR, and broad 18-gate free-OR CEGIS with 0..2 NOTs. Broad CEGIS found an initial 30-row model after24.6s, rejected it on870 full-table rows, then timed out on94 constrained rows. No counterexample or UNSAT result for1886. Full final CNF, metadata, model and logs archived in search_1886_broad; first-wave source/control archive search_1886_initial independently passed. A warm CEGIS variant uses temporary assumptions for the canonical18-gate near-circuit, reproduces exactly four errors69,104,521,548, restores them and clears assumptions; this control and its API behavior passed independent review. Warm search is queued pending root CPU/renewal approval. All my heavy processes ended, and the slot was transferred to local_optimize.

### Exhaustive suppliedOR first-step 2026-11-25T15:15:15.368578+00:00
- or_first_nonor.fragment.lean compiled and independently reviewed. For any two distinct operands from pins+[OR01], every normalized nonOR first computed gate leaves residualbinary≥16. Endpoint signed cases reduced explicitly to raw signedAND, positive idempotent endpoints to originalORbank.
- first_or_of_sixteen therefore forces exact16 binary and another positiveOR as first computed gate, with residual15. This is normalized Live statement; physical gate pruning additionally requires budget equality/all nonNOT gates contribute. Exact2NOT under18tail ensures that equality, but the physical translation is not formalized here.

## 2026-11-25 15:15:33 UTC — monotone circuit realization and conditional floors checked

monotone_circuit_banks and monotone_circuit_floor compiled exit 0 and independently reviewed PASS. Arbitrary pinmaps and raw/canonical supplied banks yield Live false with exact support and size bound. Conditional false-mode floor L gives raw/AND size L+2 and OR size L+1. Full logs and scope archived in lemmas/monotone_circuit_build/. Parent/status informed.

2026-11-25T15:17:00.990186+00:00 [local_optimize1886 repair archives and mixed heuristic]
New scoped archives results/orch/local1886-search (12files) and local1886-repair (13files) independently reviewed PASS by pilot92_status. Repair computations:540 direct edge-bank gate substitutions, none preserving the18gate near function, best21errors; residual two-gateK search with fixed pair prefixes:1762560 candidates/no solution; granting all12 within-star pairORs free:8611200 candidates/no solution, minimum4errors in all24 residual-bank/factored-star cases. These exclude only specified architectures and are not Lean results. Root received reports and source/log locations.
Prepared and reviewed local1886-near-canonical.json:18monotone gates over11inputs, output28, freebankunused, exact failures69,104,521,548 for either bankop. Used to independently validate warmCEGIS control (28rowsSAT,32rowsUNKNOWN); assumption reset independently rerun. Reviews PASS for search_1886_initial and search_1886_broad archives, with full1024 replay of oversized/rejected controls, complete hashes and CNF validation. No witness or generalUNSAT claimed.
At about15:13UTC, after root renewal15:12:59(expiry15:32:59.022Z) and broadCEGIS exit, launched oneCPU600second mixed17gate freeAND-care heuristic, seed92. Uses120 exact-care templates plus120automorphic18gate near seeds; all240 independently validated. Full log scratch local1886-care-mixed-run1.log; source local1886-care-search-mixed.cpp; independent all1024 lifted-circuit validator local1886-care-validate.py. Initial weighted best49; run currently ongoing, nozero-score.

## 2026-11-25T15:18:10+00:00 — reduction_design: endpoint-NOT distinct consumer checked

`endpoint_order.lean` and `endpoint_consumers.lean` both compiled with exit0 and empty complete logs. The first proves reverse order of all wires except a distinguished raw input through a monotone suffix when every consumer of that raw input also reads its complementary NOT wire; gates reading both are constant. It preserves default-false behavior at invalid indices and requires no fan-in bound. Structural independently reviewed it PASS.

The second proves an actual seeded Petersen circuit with exactly one explicit endpoint NOT and monotone prefix/suffix must have either an earlier raw-endpoint consumer in the prefix, or a later raw-endpoint consumer that does not read the NOT output. Both endpoints0,1 are covered. Singleton inputs rule out returning the raw endpoint directly. Inputs {4}/ {0,4} or {2}/ {1,2} force target output to increase while the paired-wire invariant would make it decrease. No NOT-liveness assumption is smuggled in: a separate consumed-NOT hypothesis is still required for the desired three-gate deletion count. The compiler/counting bridge belongs to lean_setup.

### Forty remaining values 2026-11-25T15:20:26.070839+00:00
- or_first_census.fragment.lean compiled/reviewedPASS: suppliedOR normalizedLive≤16 has exact16 gates, firstcomputedvalue among40 distinctORwords, residual15. List consists28 disjoint rawpairs outside0/1, four exceptionaloverlaps(0,2),(0,6),(1,4),(1,5), and8 triples OR01∨pin_p. Kernelchecked121operandpairs plus independentlycheckedPython truth tables. RecomputingthefreeOR itself excluded by originalbankfloor16.
- negative_seed_absent and its arbitrary-p transport compiled/reviewedPASS. A tight16 residual afterpin_p∧¬OR01 mustretainOR01; positive-seedconjunction tight16 mustretireOR01. All cases explicit, no duplicatecharging.
- Perparent, no deeperprojectionsearch untilendpointNOT andMonoNine/v2buildstatus evaluated. Structural agent available for independentreviews.

## 2026-11-25T15:22:57+00:00 — reduction_design: dead single-NOT semantics checked

`endpoint_unused.lean` and `unused_not_general.lean` compiled with exit0 and empty full logs; objects are exported. The first shows that a suffix reading no appended NOT wire has the same other output for either replacement constant. An all-zero input excludes choosing the NOT of a raw input as the final output. The second covers any NOT source index: monotonicity of the prefix between all-zero and all-one inputs contradicts choosing the complemented source as Petersen output. Thus with a monotone prefix and suffix, an unused single-NOT wire may be replaced by either constant while preserving the exact target. Ignored NOT operands are included. These are semantic replacement statements; gate deletion and the final size bound are still supplied separately by lean_setup's compiler.

## 2026-11-25 15:26:11 UTC — endpoint0 NOT restriction checked and frozen

constant_sweep_mono, constant_not_cut, endpoint_restrict, endpoint_lower0 all compiled exit0 and independently PASS. Explicit consumed NOT[0], monotone prefix/suffix and suppliedAND imply>=19 gates from the checked nine-variable>=16 bound. Identity pins, endpoint0 and consumer/floor premises remain explicit. Full logs and scope in lemmas/endpoint_compile_build/. Parent410 pause respected after completing this existing pipeline; no new builds started afterward. DeadNotCompile separately reviewed PASS for preservation.

2026-11-25T15:26:22.909027+00:00 [local_optimize1886 mixed heuristic complete]
600secondcap completed1536141680 evaluations and61439restarts; weightedbest49 unchanged; normal non-witness exit1. Independent full1024 lifted-circuit validation confirms ninefalse negatives640,641,642,648,649,650,896,897,898. Raw17gate monotone circuit computes Petersen minus exactly edges01and79. The freeAND01/finalOR lift restores01 only; testing all15suppliededgeAND choices leaves at least9errors. No counterexample. Frozen results/orch/local1886-care-run (14files53063bytes) contains source,240templates, complete logs, finalcircuit, validation outputs and reproduction instructions; pilot92_status independently reviewing. Root reported1886lease410 and requestedpreservation; no newsearches launched and CPUisfree.

## 2026-11-25T15:43:33.241752+00:00 — final ownership stop and preservation

Our own1886 lease returned410; no new proof searches were started afterward. Recovery requests3–5 returned null with checker backlog521. Requests6–7 returned the same pre-existing4970 lease issued15:22:04.914Z, before our requests, and the exact five-gap handle-limit message. The required retry did not assign a new lease, so polling stopped. No work, renewal, or release was performed on4970. All six subagents are stopped or performing final read-only preservation review. The named1886 v2 partial build passed; the exact theorem remains absent. Official checker startup failed because authentic full Mathlib cache is unavailable. No proof PR was opened. The final archives, scope notes, integration fragments, complete desk answers and reproduction guide are preserved in this branch.
