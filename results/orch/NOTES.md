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
