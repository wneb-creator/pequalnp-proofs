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
