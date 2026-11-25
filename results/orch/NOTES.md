# L-meta-2592 orchestration notes

Lease holder: root only. No agent calls the desk.

Goal: Petersen graph 10-input edge function has no fan-in-two circuit of size <=19 containing any NOT gate.

Allowed project module: PEqualNP.Defs. Three reductions already live. Seek full proof or checked components.

Each agent appends findings under a uniquely named section; use separate files in lemmas/. Do not alter final target without coordination.

## submission_rules audit after upstream update

Updated audit against upstream commit 0686a851 (2026-11-25); earlier stale-checkout audit is superseded.

- Checker v4 and authoritative workflow now support `check`, `refute`, and `reduce`. A refutation run still requires the public desk row to have `kind: refute`; selecting refute does not convert a prove row.
- For the full proof use `node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-131/statement.txt check` with complete stdout/stderr saved, and separately `node .github/scripts/outside-guard.mjs imports lean/PEqualNP/Outside/L_meta_2592.lean /tmp/oec/pequalnp-pilot-131/imports.json lean/PEqualNP/Outside/L_meta_2592.lean check`.
- New own-namespace rule: helpers belong within `namespace PEqualNP.Outside.L_meta_2592` or `_aux`; each namespace/end is unindented and each end names its scope. Main theorem is fully qualified, outside the helper namespace, and last. Top level otherwise allows imports/open/four scoped limit options/comments. Avoid helper instances and simp attributes because they affect importing files.
- The three live reductions reported by the desk are present on main: R_meta_2592_271 (15 binary gates floor plus no computation with 1..4 NOT gates); R_meta_2592_408 (normalization plus lower bound for legal trimmed circuits); R_meta_2592_318 (cut after last NOT plus a separator bound). The published cap of three live reductions leaves no available reduction slot for another submission now.
- A reduction must have only one theorem and no extra declarations or namespace. Checker requires 2..4 closed independent proposition hypotheses, exact structural equality of the conclusion, no duplicate/False/decidably-false hypothesis, no hypothesis containing the conclusion, no text/meta data, and at most 2000 printed characters per child. Generic local validation uses kind `reduce`; format validation also requires explicit `reduce`.
- One-file final PR still required: only the target Lean file may differ from upstream main. Notes/results may be preserved in branch history but cannot remain in final PR diff.

L-meta-1035 status audit (saved data/repo only): exact target filename and R_meta_1035_* are absent at 0686a851; exact boundary-matched git log titles return no entry; no match appears in the saved complete 931-open-PR census. Saved head.json was generated 2026-11-25T14:27:26.728Z. Saved search files are an inverted token index, not lemma status rows. Thus current open/taken/refuted/withdrawn status is UNVERIFIED from these local artifacts; absence of a proof file is not evidence that it remains open.

## submission_rules independent pre-push partial audit

Reviewed 2026-11-25, before any compilation by this reviewer.

- Structural.lean SHA256 7bb33dde12ce912a559a9247fdda0e1c3d8b651ea5da169dafe5eaeada643471 (90 lines): sound list split at the last NOT; prefix output selects the first NOT input, using an invalid index for an empty input list so its value is false; appending its complement therefore exactly reproduces the NOT gate. Suffix has no NOT and retains fan-in-two, and sizes sum correctly. No mathematical counterexample or hidden hypothesis found.
- Counterexample.lean SHA256 a0b7224666e38e43d7642747acecabc34c5570dbbd625c124b8f48e29e6c9b32 (57 lines): independent Python evaluation confirmed all 1024 assignments match the fifteen Petersen edges. Exactly 20 gates, every gate binary AND/OR with legal earlier indices, output wire 29. This is an upper-bound witness, not a refutation of L-meta-2592.
- Source scan found no sorry, native_decide, axiom, forbidden root qualifier, quotes, or attributes. Kernel decision tactic is permitted. Compilation is pending root cache completion.
- PASS for push-early preservation once Lean compiles. These results-folder files and theorem names are archival partial components only and must not remain in a final proof PR diff.

## Counterexample strategy 2026-11-25T14:33:32.188987+00:00

Semantics audit found no loophole: invalid reads give false, NOT ignores extra operands, output fixed. FanInTwo excludes all extra GateOp cases. Verified 76 independent sets, five maximum independent sets of size four (so vertex covers size six). Standard star-cover circuit has exactly 20 gates. Explicit 20-gate witness is in lemmas/Counterexample.lean, Python all-1024-input verification passed; Lean waiting for cache.

Custom C++ stochastic 19-gate AND/OR/NOT synthesis started; best error 9/1024 from a monotone circuit omitting one edge, no witness. Cadical available from toolchain. Started one-NOT SAT synthesis with 92 initial rows (all 76 independent sets, 15 edges, all-true), then CEGIS; a heuristic search for clean minimal witnesses, not a proof of global UNSAT. Files /tmp/oec/pequalnp-pilot-131/synth.py and circuit_search.cpp.

## structural_proof: 2026-11-25T14:33:40.456705+00:00

Prepared `lemmas/Structural.lean` with an exact last-NOT factorization: split gate list at its last NOT, retain fan-in-two prefix P, obtain monotone suffix Q, and prove exact size and evaluation identity. Empty NOT operands are handled by choosing a missing prefix wire as P.output. This proves the first hypothesis of R_meta_2592_318. Awaiting Mathlib cache for compilation.

Analytical route: Petersen has 15 edges and vertex cover number 6, suggesting monotone size 15+6-1=20. The needed extension to circuits with arbitrary NOTs remains unresolved; arbitrary NOT gates cannot simply be dropped. Existing L_meta_1507 proves a depth-4 exclusion with edge/independent-set signatures, not the needed size bound.

Structural compile PASS 2026-11-25T14:35:55.670033+00:00: `lake env lean ../results/orch/lemmas/Structural.lean` exited 0. Full saved logs: structural-002.stdout and structural-002.stderr (both empty). The theorem is a checked partial component, not the posted Petersen bound.

## restriction_route findings

- L_meta_1938.signedPetersen gives a 15-total-gate lower bound for Petersen minus one vertex, even with a free complemented input.
- Generic fixed-input elimination costs one gate; best-side elimination costs two. These cannot alone prove the desired 20 bound: each zero cofactor has a 15-gate monotone construction, and each one cofactor has an 11-gate construction (three singleton neighbors OR a 6-cycle edge function). Therefore even exact cofactor bounds yield at most16 from these rules.
- A universal claim that a zero restriction removes five gates is too strong: star-cover20-gate formulas can be arranged so each zero restriction removes only3–4 gates under ordinary simplification. Any successful elimination proof must exploit the assumed19 budget or analyze richer prefixes.
- Checked partial component results/orch/lemmas/Restriction.lean: monotonicity except a globally ignored coordinate, and an obstruction to computing Petersen with a monotone suffix that has free !x0 but never reads positive x0 (assuming output !=0). The proof handles default/future reads. This is not a proof of the posted statement.
- Lean compilation exit0 on2026-11-25; only deprecation warnings. Complete logs: /tmp/oec/pequalnp-pilot-131/restriction-build.stdout and .stderr.

## Library route: checked binary lower bound

2026-11-25T14:37:19.338571+00:00 — `lemmas/Library.lean` compiled with pinned Lean; exit 0, no warnings. `Full.binary_floor` proves every fan-in-two circuit computing the full 10-input Petersen edge function has at least 15 non-NOT gates. It adapts the general circuit branch argument of L_meta_8039: earliest branch labels give an injective vertex-cover set, minimum cover size 6, and circuit branching budget >= cover+9. The finite common-neighbor samples are checked with `decide +kernel`. File is 2735 lines, about 123 KB. This is a partial, not the posted theorem.

The fullgraph maximum independent sets ofsize4 are {0,2,8,9}, {0,3,6,7}, {1,3,5,9}, {1,4,7,8}, {2,4,5,6}. At exactly15binarygates, the existing budget argument forces four terminal variables to be read at most once in the unfolded formula. certificate_search is testing an upgraded ledger bound.

## submission_rules updated partial audits

- Structural final reviewed SHA256 772870ce2c2f869524a02d6e3d16fb48bda597c8e90fccff4b50dc09210f05ef (92 lines). Only elaboration/simplification fixes since earlier review; no logical changes. Root reports compilation exit 0; structural-002 stdout/stderr are empty. PASS for archival push.
- Library reviewed SHA256 ea4a085368acddd6ea934082a5f06562ad28173ee0e38f27bd85b8a19bf6d63f (2735 lines). Generic prefix is identical to merged L_meta_3831 after namespace substitution. Full.es matches the exact posted fifteen-edge list. Independent Python checks validate pair_samples on all 60 ordered common-neighbor triples, alternate-neighbor witnesses, and vertex-cover minimum 6 over all 1024 subsets. Read new tie exclusion, injectivity, least selection, and arithmetic bound: all sound. Count lemma proves at least 15 non-NOT gates, not the full size-20 lower bound. PASS pending compilation; no forbidden-token hits.

restriction_route strengthening: `positive_input_required` is now checked and removes the output-index hypothesis. Any monotone circuit computing Petersen from the ten inputs plus a free !x0 must have some gate that reads positive input0. This excludes only one narrow shape of a first-NOT circuit; arbitrary internal NOTs, multiple NOTs, and the 19-gate bound remain open. Compilation exit0; complete logs copied to results/orch/restriction-build.stdout and .stderr.

## Counterexample strategy stop 2026-11-25T14:40:00.664462+00:00

Root reported HTTP410; all seven active search processes were interrupted (exit130), and no further gap work is running. No19-gate witness found. Every SAT case remained at initial92-row instance without SAT/UNSAT verdict; these interrupted searches establish no lower bound. Stochastic unconstrained best6 weighted errors; NOT-required best15 weighted errors. Known20-gate witness passed Lean and was pushed byroot. Complete scripts/stdout/stderr and SHA256 manifest preserved under /tmp/oec/pequalnp-pilot-131/counterexample-search-manifest.json. SAT encoder sanity test with frozen20-gate witness returned SAT and passed full1024-row verification.

## certificate_search finite ledger experiment

2026-11-25T14:40:04.989729+00:00 Stopped after root reported desk HTTP 410.

Generic Readers restriction recurrence cannot reach the needed 20: Petersen-minus-vertex has a 15-gate witness, and the true cofactor has an 11-gate witness. My initial 16 estimate for the false cofactor was only the star-cover construction cost, not a lower bound; it was corrected.

A stronger ledger at binary count 15 is promising. Canonical independent terminal set T=[0,2,8,9], complement S=[1,3,4,5,6,7]. Regular sample masks [0,2,8,16,32,64,128,10] give profiles [154,198,180,104] and canonical seeds [8,16,32,64,123,125]. Exact finite cover/build search returns no ledger at pure-build+filter-block cost <=11: 223641 cover states, 41917 build states, 2.64 seconds. This is a Python computation, not yet a Lean-checked circuit lower bound.

The first seven rows alone are insufficient: there is a ledger at cost 11. The eighth sample {1,3} removes that loophole. Base sample 138 (vertices1,3,7) is independent and meets every terminal neighborhood; special sample 66 (vertices1,6) contains an edge, supplying the extra baseline cost.

Certificate.lean adapts the standalone CoverCheck module of L_meta_8039 to eight bits, seventeen cover cells, and budget eleven. Lean checking was started; no result yet at stop. Probes and terminal-class integration are not yet implemented. A successful integration would yield binary gates >=16, excluding circuits with at least4 NOTs under total19, while leaving1–3 NOTs. Scripts and exhaustive output are preserved in results/orch/search.

## submission_rules final preservation audit after desk 410

No new proof work or compilation performed by reviewer.

- Strengthened Restriction.lean reviewed SHA256 add9870f833f7f8e8b75546c0122be1b054fb070860d957238a7680601e9a265 (148 lines). Original 112-line prefix matches prior reviewed hash. New preservation of input wires and singleton-input contradiction correctly remove the old output-not-zero hypothesis. PASS for archival as checked partial, per agent compile exit 0. Build logs only show deprecation warnings.
- NotStructure.lean reviewed SHA256 8f1a01e62568383e041828e95008b67529bce62570032ae98a1718e8c15a2c7b (256 lines). Generic alias-deletion helper code matches an unchanged subsequence of merged L_meta_522. New minimal_no_alias uses valid earlier alias deletion; not_gate_value requires a valid earlier first operand; minimal_no_double_not correctly excludes a direct chain of two NOT gates in a minimal circuit under these explicit hypotheses. PASS for archival as checked partial, per agent compile exit 0.
- LibraryNext.lean SHA256 05e498f6c4e4293cd2d0dd35f37f41ffe9d5f257c63c06c112ac59e2371472de (2899 lines): safety scan clean, archive as UNVALIDATED because compilation has reported failures.
- Certificate.lean SHA256 49f914d27f27d158197310c44fb0dfce738e49aeec51a131d1fa173163b5051f (705 lines): safety scan clean, archive as UNVALIDATED while compilation pending. Finite ledger alone is not the full gap theorem.
- gen_certificate.py and ledger_probe.py inspected in full: task-local source reads/writes, deterministic finite computations, no credentials, no network, no shell/subprocess execution. Safe to preserve as research artifacts; their numerical results do not substitute for the Lean checker.

## New assigned gap L-meta-2583

Previous gap2592 lease returned410; workstopped andpartials pushed17967427. Recovery request assigned2583, reductions_open:false. Rootonlyholdsthislease. Statement in scratch statement-2583.txt. Newhelpers use2583namespace andnewfilename, avoidoverwriting2592artifacts.

2026-11-25T14:42:25.144949+00:00 Certificate.lean pending validation exited137 with empty stdout/stderr; resource termination. This component is not Lean-checked. No edits were made after desk410.

## submission_rules L-meta-2583 model and duplicate audit

New lease only; no further old-gap proof work.

- Current definitions: IsAO2 means AND/OR only, reads earlier wires, exactly two operands (repetitions allowed). IsReadK is joint proof-tree multiplicity for every prime implicant; it is not fan-out and not separate per-variable minima. For this incidence function prime implicants are point-line pairs. The lower hypotheses imply N>=7, nonempty incidence, and the usual regular projective-plane design; no immediate vacuity or model loophole found.
- Saved complete 931-open-PR census contains PR13723, titled L_meta_2583, same author handle, created 2026-11-25T11:49:40Z. Read-only API request made using brilliant-hq path redirects to the same renamed open-goat project. One added file at correct path, 7090 lines/333774 bytes; no main theorem named PEqualNP.Outside.L_meta_2583 occurs.
- Authoritative comment at https://github.com/open-goat/pequalnp-proofs/pull/13723#issuecomment-7161809767: REFUSED before any build because the theorem must be top-level, last, fully qualified. Run https://github.com/open-goat/pequalnp-proofs/actions/runs/45608830837. Current local format guard reproduces refusal. There are no check-runs for its head SHA in the API. Thus no checked full competitor; do not treat this partial as a completed proof.
- Public partial source saved to /tmp/oec/pequalnp-pilot-131/pr13723-L_meta_2583.lean. Useful declarations: plane_read_one_upper line1216 (size<=N*(q+2)-1); read_one_plane_lower line3395; read_one_replacement_iff_size line3416; normalization line4300; unrestricted_plane_size_lower line7075 only gives3*N-1. Source has no obvious sorry/native_decide/axiom tokens, but has not been Lean-validated in this job. Its equivalence isolates the missing general lower bound (Fano27 vs currently20).
- Desk pr_open=0 contradicts saved open PR census, likely because this is refused/partial; authoritative refusal and lack of target declaration are directly verified. No current negated twin identified in saved artifacts. Reductions explicitly disabled for new2583 lease even though sketch proposes cuts; old2592 reduction authorization does not apply.
- Old Certificate validation finished exit137 (resource termination), empty logs, not Lean-checked. Agent preserved result in results/orch/search/certificate-status.txt. Keep UNVALIDATED label.

## restriction_route: L-meta-2583

Checked component `lemmas/IncidenceRestriction.lean`: for any circuit computing a bipartite incidence function, prime implicants are exactly the incident point-line pairs. Consequently `IsReadK k` is equivalent to the per-edge `readsAtMost` checks on the pair's setList, for any k. This needs no AO2 or projective-plane geometry and does not establish a size-preserving circuit normalization. `pair_prime` follows the existing L_meta_2581 argument; the converse and read equivalence are added here. Compilation exit0, no warnings; complete logs `incidence-restriction.stdout/.stderr`.

## Incidence counterexample route 2026-11-25T14:44:38.641797+00:00

New leased step L-meta-2583 asks no-size-increase READ1 normalization of monotone projectiveplane incidence circuits. Audited IsAO2 and ReadK definitions: exactbinary legalAND/OR, joint per-primeimplicant proof-tree counts; no obvious semantic loophole. Fano q2 has21 edges,458 independentsets and37 maximal independentsets (21ofsize4,14ofsize5,2ofsize7). Thus58 criticalrows completely determine a monotone computingcircuit. Libraryagent found READ1 lowerbound27 (L_meta_7639); any26-gate AND/OR witness would be promisingrefutation.

Started20-minute26-gate stochastic bitsetsearch and Cadical search over58 criticalrows. Candidateverification will use all16384 assignments. Searchdata/scripts/fullstdoutstderr under /tmp/oec/pequalnp-pilot-131/fano-*. Noresult yet.

## submission_rules IncidenceRestriction pre-push review

PASS for archival checked partial. Reviewed SHA256 e8b19569ddfa5439d1b553b7ce1382c3e516865ee949682f139bc353fef7f2c7, 89 lines. Agent reports Lean exit0; saved stdout/stderr are empty. The castAdd/natAdd inputs are provably disjoint. Every incident pair is prime because a proper subset cannot retain both endpoints; every prime accepting set contains such a pair and minimality forces equality. The ReadK equivalence follows by this classification for arbitrary k. No plane axioms or IsAO2 assumption are needed because these are semantic claims under exact function equality. No forbidden proof shortcuts, extra axioms, or format hazards found. Correct own helper namespace; file contains helpers only, so remains an archival component and not the final2583 theorem or submission-ready PR file.

## submission_rules IncidenceLibrary pre-push review

PASS for archival checked partial, SHA256 9a3c903705cbdadcee5ea16d26a0c7d4488f33d16d720760896ef1c800c12d72, 1175 lines. First1126 lines match merged L_meta_7684 exactly after namespace substitution and final theorem-to-canonical-lemma rename. Added incidence count N*(q+1), point-star construction size<=N*(q+2)-1, and conditional replacement via explicit size hypothesis are correct. Reported Lean exit0, saved logs only contain unused/deprecated tactic warnings. No forbidden tokens or new axioms. This does not prove2583 because required original-circuit lower bound remains a hypothesis. Before eventual final PR, move fully qualified canonical helper at1123 into an own namespace block; top-level helper declaration is allowed for this archival partial but fails final proof-file format.

## L-meta-2583 construction component (library_route)

`results/orch/lemmas/IncidenceLibrary.lean` compiles with only `Mathlib` and `PEqualNP.Defs` imports. Namespace `PEqualNP.Outside.L_meta_2583_aux.CanonicalConstruction`. It copies the checked L-meta-7684 generic bipartite cover construction and specializes to the all-points cover. The incidence cardinality and specialization match archived PR13723. `plane_read_one_upper` assumes only every line has q+1 points and constructs AO2/read1 D with size <= N*(q+2)-1. `plane_read_one_replacement_of_size` additionally assumes this threshold <= C.size and gives the target replacement witness. This is a checked partial, not a solution of L-meta-2583.

Build exit 0, full logs `/tmp/oec/pequalnp-pilot-131/incidence-library.stdout` and `.stderr`; warnings are inherited unreachable/deprecated tactics. SHA256 `9a3c903705cbdadcee5ea16d26a0c7d4488f33d16d720760896ef1c800c12d72`, 1175 lines. Independent submission_rules archival review PASS.

No unconditional exact N*(q+2)-1 lower bound found. Existing generic exact bounds L-meta-4897/7639 require read1, L-meta-8569 requires leastAO+TopForm+junk empty, and L-meta-7241 assumes every AND gate false on every nonedge pair (including diagonal pairs). The archived PR already proves read1 replacement iff this exact size threshold. L-meta-3376 supplies the weaker general 3N-1 bound.

## submission_rules read-only research on q>=3

Read 2026-11-25: https://github.com/open-goat/pequalnp-proofs/discussions/12644 (primary search report, not a Lean proof). It reports PG(2,3)63-gate annealing against52edge inputs and704maximal independent sets; best still failed one test. The same method failed at70gates, so no lower bound follows. Reduced SAT with fixed top structure/symmetry is suggested there. Its tiny C4-free core-cover exhaustive search reports230415755circuits over19graphs with no violation, but explicitly says the C definitions were not independently audited. These are reported figures confirmed on the page, not independently reproduced here. No q>=3counterexample was found in allowed-domain research.

Read-only public snapshot https://data.pequalnp.com/data/desk/gaps.json, updated2026-11-25T14:46:07.445Z, saved /tmp/oec/pequalnp-pilot-131/public-gaps-review.json. It has1630postedrows and keeps2583, genericC4-free read1 replacement2585, and core-cover2962 open. No explicitly titled negated twin of2583 found. Core-cover2962 sketch identifies overlapping core cones as the remaining difficulty. Order3lowerbound972 (>=64) and existential650 (<=63) both remainopen. No new lease or desk mutation was made. ExactL-meta-1035 absent from posted/checked/withdrawn records and hashed graveyard snapshot; status remains UNVERIFIED, absence is not proof of refutation.

## submission_rules IncidenceStructural pre-push review

PASS for archival checked partial. SHA256 8673204201208fda2f1c2c1717a34ec360562911d76ef417da6f0b641c001c08, 92 lines. Agent reports Lean exit0 and saved logs are empty. point_degree partitions all points except p into q-sized disjoint sets on lines through p, deriving degree q+1 from N=q^2+q+1. pencil_cover_card is a valid union-cardinality argument: each point other than p meets at most one line of the pencil. independent_pencil_replacement uses independence of X,Y to force every newly accepted incidence to involve the newly added line, then invokes that bound. The p-not-in-X hypothesis is necessary and explicit. No full circuit-normalization or cost claim is made. No forbidden tokens, new axioms, or namespace issues found.

## L-meta-2583 certified synthesis pruning (library_route)

`results/orch/lemmas/IncidencePruning.lean` (321 lines) is Lean-checked, namespace `PEqualNP.Outside.L_meta_2583_aux.Pruning`. It copies L-meta-8385 wire evaluation and gate deletion infrastructure. `DeterminesOn n S f` says agreement on S by any AO2 circuit determines full output f. Assuming C is least among AO2 circuits for its output, `no_earlier_signature` excludes any gate signature matching an earlier wire on S; `operand_separators` gives witnesses on S with operand values (true,false) and (false,true). These justify finite complete-row pruning without assuming read1 normalization. Restriction agent is formalizing incidence critical-row completeness.

Build exit 0; logs `/tmp/oec/pequalnp-pilot-131/incidence-pruning-2.stdout` and `.stderr`. SHA256 `d1e0d8fb385472aa7d1114afc8125dc720e4c5a928876ddf0e8bff2cf0426933`. The only warning is deprecated push_neg. No forbidden token matches. Submitted to independent reviewer.

Minimality caveat for synthesis: constraints apply to globally least circuits; near-seed searches freezing most gates may not contain a normalized candidate after bypass. Therefore they are sound for exhaustive search over the least size, but a local search returning UNSAT under these constraints is not a global lower bound.

Dirty gate counterexamples: merged L-meta-4849 has 8 inputs, 8 edges, 11 gates and dirty AND in a minimal monotone circuit, but graph contains a 5-cycle and is not bipartite. Merged L-meta-3679 refutes AND-antichain normalization in a 39-vertex bipartite graph, but graph has 4-cycles. Neither refutes bipartite+C4-free cleanup specifically.

## restriction_route: generic critical-row completeness

`lemmas/IncidenceCriticalRows.lean` compiled exit0 with no diagnostics. For any m-point/n-line incidence relation and any semantic monotone Boolean function f, exact incidence computation is equivalent to f being true on every incident singleton pair and false on all completions X together with every line avoiding X. This is independent of the original normalization claim and supplies the determining-row bridge for signature pruning.

AND-count search found existing L_meta_1898: arbitrary Monotone2 circuits for cyclic q3 incidence require at least13 AND gates (no ReadK/bilinearity assumption). L634/L910 give Fano's7 bound. General C4-free full-computation bound found only up to cover5 in L2399. L1006 refutes a weaker boundary-only statement, not full computation: Python checked all2048 inputs of its11-variable witness and found39 false negatives, including edge{6,7}.

Python independently enumerated closed point sets for cyclic q3 offsets0,1,3,9:704, matching the maximal-independent-row count. Full list /tmp/oec/pequalnp-pilot-131/q3-closed-pointsets.txt. Lean closure reduction is being added separately.

## Counterexample strategy replan 2026-11-25T14:52:24.587377+00:00

Stopped Fano26 search after certificateagent found checked arbitrarymonotone≥27 result in L_meta_7997. Its FanoE atline9403 exactlymatchesour cyclicoffsets0,1,3, ao27at9428 doesnotassumeReadK. Fano searches unresolvedandinterrupted; noFALSEclaim.

q3 incidence offsets0,1,3,9 has52edges,704maxfalse assignments,756completecriticalrows. Full63gatebaselinefoundone missingprimeedge; rereadbiasedvariantfoundtwo missingedges but its badproof was onlyAND(4,4), spottedbycertificateagent. Bothbaselines stopped. Newvariantpenalizescomparableoperand signatures, duplicateinputs, andfewerthan13ANDgates (checkedlower L_meta_1898), plusREAD1lack. Runningtwo nearseedSATvariants: removeoneORfrom64seed, freeze50gates, synthesize13gates aroundthreepointstars andfinaljoins, CEGIS112initialrows, seed25831noncollinearpoints0,1,2 and25832collinear0,1,3. Alsofast23gateGPfor5-lineblock0,1,2,3,9 with50criticalrows, independentlypairedwithcertificateagentSAT. Noexactcounterexample yet.


## Independent archival audits: Pruning, CriticalRows, OrSplice

Reviewed by submission_rules at 2026-11-25T14:53:02.362851+00:00.

- IncidencePruning.lean: PASS, SHA256 d1e0d8fb385472aa7d1114afc8125dc720e4c5a928876ddf0e8bff2cf0426933, 321 lines. Rowwise alias deletion plus explicit determining-row completeness contradicts least AO2 size. Operand implication would make the AND/OR gate an alias, yielding two separating rows. Reported Lean exit 0; full log has only a deprecated tactic warning. This is a generic partial, not the posted theorem.
- IncidenceCriticalRows.lean: PASS, SHA256 aa08b651c434cd0ff306c8c9f43e6ec798ccd785b4173d7950485285612c59cd, 84 lines. Any incidence-positive row contains an incident pair. Any incidence-negative row lies below the completion of its active point set. Therefore semantic monotonicity, pair positives, and completion negatives imply exact incidence semantics; reverse implication is direct. Reported Lean exit 0; both complete logs empty.
- IncidenceOrSplice.lean: PASS, SHA256 06cc88a097759dde86b335568b3ec82198d184ace4fc314c1630066aef4ec727, 134 lines. Prefix and suffix avoid primary v; all other wires preserve true values under the input change. The distinguished OR is true at the target via its other operand. Explicit v<input length and output != v discharge exceptional-wire cases. Reported Lean exit 0; complete log only deprecated-name warnings.

The latter two source scans found no forbidden root escape, strings, sorry/admit, axioms, native_decide, options, or attributes (rg exit 1, no matches). They remain checked partial components, with no final normalization/size theorem or local-checker acceptance claimed. Parent notified before archival push.

### 2026-11-25 14:55:04 UTC — restriction route: closed critical rows checked
`IncidenceClosedRows.lean` is a self-contained extension of the frozen `IncidenceCriticalRows.lean` snapshot; both snapshots deliberately retain the same helper declarations and should not be imported together. The extension proves that point closure is extensive and idempotent and preserves the set of lines avoiding a point set. Every negative completion is below its closed completion. Thus only incident-pair positives and closed-completion negatives determine any semantically monotone function (`criticalRows_determine`); no incidence geometry, AO2 normalization, or assumed circuit lower bound is needed. Lean exit 0; complete stdout/stderr archived as `incidence-closed-rows.stdout` and `.stderr` (both empty). The finite q3 count of 704 closed point sets remains a Python observation, not yet a checked Lean enumeration.

## Structural route: sole-OR pencil obstruction (2026-11-25T14:55:30.338484+00:00)

Checked `IncidenceSoleOr.lean` with exit 0 (`incidence-sole-or-002.stdout/.stderr`). The new theorem `sole_or_independent_witness_large` proves: if the only read of point p in an AO circuit computing the plane incidence function is at OR(p,a), then every independent input witness (X,Y) for operand a, with p outside X, contains at least q+1 points. It assumes a is not the wire p and output is not p (both routine normalized-circuit necessities). Proof: replace p in each incident edge witness by the independent witness for a; monotone transfer forces X to hit each of q+1 lines through p, and unique joining lines force distinct points. This provides a plane-specific obstruction to cheap dirty OR helpers but does not yet yield a global gate lower bound. File frozen for independent audit and push.

### 2026-11-25 14:57:58 UTC — restriction route: maximal rows checked
Frozen `IncidenceMaximalRows.lean` extends the previous self-contained closed-row snapshot. It proves `closed_iff_omitted_neighbor`: a point set is closed exactly when every omitted point has a neighbor among lines avoiding the set, the condition used in the q3 Python/C++ generator. It also proves `closed_iff_completion_maximal`: closed completions are exactly the maximal false incidence inputs under coordinatewise Boolean inclusion. Lean exit 0, no warnings; complete logs `incidence-maximal-rows.stdout/.stderr` are empty. These successive snapshots duplicate helper names and are not intended to be imported together.

## Structural route: singleton support restricts literal filters (2026-11-25T14:58:05.097979+00:00)

Checked `IncidenceDirtyFilters.lean`, exit 0 with empty complete logs `incidence-dirty-filters-002.stdout/.stderr`. Generic monotonicity helpers adapted from merged `L_meta_4063` (dimension generalized from 11 to n). New checked lemmas: (1) every singleton-support vertex of an AND/OR gate is adjacent to every vertex of its `wmax`; (2) with NoFourCycle, singleton support of size at least 2 forces `wmax.card ≤ 1`; (3) with any proper Boolean bipartition, singleton support meeting both color classes forces `wmax = ∅`. These handle arbitrary gates, not just dirty ANDs, and require no least-circuit/TopForm assumption. Proposed by certificate_search, formalized here. Indirect cleanup using further dirty gates remains the main unbounded case. File frozen for independent audit/push.


## Independent archival audit batch: closure, sole OR, filters, AND choice ledger

Reviewed by submission_rules at 2026-11-25T14:59:17.838885+00:00.

- IncidenceClosedRows.lean: PASS; SHA256 e8c69f812cc26f4d3fc4aa210f8190eb1da2b7f4cc88017e8c2343797c8b675c; 169 lines. Point closure preserves avoided lines and is idempotent; closed completions dominate arbitrary completion negatives, proving row completeness. Empty build logs.
- IncidenceSoleOr.lean: PASS; SHA256 5d2a042b373bee68ce84b8be54ef4703208ae4228740e10dc191a14353f9c72a; 327 lines. Exact incidence semantics composes with the sole-OR transfer: each point-pencil pair transfers to X with its line inserted. Independence and omitted point yield the q+1 pencil bound. Build log only deprecated names.
- IncidenceAndEquality.lean: PASS; SHA256 cb61e6a0794e9f446d3234dea351b4d5a63b9c7ed6d9e734297c685db37ee485; 277 lines. Maximal false rows inject into canonical false-choice codes; cardinal saturation gives surjectivity. A true gate permits a flipped valid choice with the same complement row, contradicting distinct codes. Empty build logs.
- IncidenceDirtyFilters.lean: PASS; SHA256 0aa1094deceb8415563410018cc087f4ac40c97157a3d94bcda4f6dcff440539; 115 lines. Singleton gate truth implies adjacency to each wmax filter vertex. Two distinct singleton witnesses and C4-freeness bound the filter by one; opposite bipartition sides force an empty filter. Empty build logs.
- IncidenceMaximalRows.lean: PASS; SHA256 991e31019a07280167352b6ffdfc041fb3942d4004559e31b8a0441cadc3cdb7; 239 lines. Reviewed ClosedRows prefix unchanged. Closed point sets are exactly those where every omitted point has an incident avoided line; this is equivalent to completion maximality among negative rows. Empty build logs.
- IncidenceAndLedger.lean: PASS; SHA256 ce23bae1ccd8bef74986c7116adb42d57cd3370752126afda95d49231489b0fb; 343 lines. Reviewed AndEquality prefix unchanged through line 276. Choice sets of distinct maximal false rows are disjoint, and t true gates give at least 2^t valid choices. The disjoint-union count proves the weighted sum bound by 2^ANDsize. Build log only two deprecated names.

All six agents reported Lean exit 0; reviewer read complete sources or verified the unchanged reviewed prefix and read the full extension, plus complete logs. Forbidden-token scans had no matches (rg exit 1). All are partial components, not the posted theorem and not checker-accepted final submissions. Self-contained snapshots intentionally duplicate earlier declarations and must not be imported together. Extra Mathlib imports in the relevant snapshots must be removed when integrating a final Defs-only submission. Parent received frozen hashes and PASS verdicts before archival push.

## AND-count equality and false-choice ledger (library_route)

Bare ANDcount=vertex-cover number does not force read1: P4 has ab∨bc∨cd = (a∨c)∧(b∨d)∧(b∨c), using 2 ANDs but repeated reads; its total 5 gates exceeds canonical 4. Uniform line degree does not suffice either: replace OR(A1, AND(x2,N2)) by AND(OR(A1,x2), OR(A1,N2)), preserving ANDcount but adding one total gate. Thus least total size or a size-preserving normalization remains essential.

A stronger valid equality route is now proved. `IncidenceAndEquality.lean` (277 lines, SHA256 cb61e6a0794e9f446d3234dea351b4d5a63b9c7ed6d9e734297c685db37ee485) proves that an AND-count circuit with exactly 2^size maximal-false rows has every gate false on every such row. The proof copies the generic false-choice clause infrastructure from L-meta-2399 and uses cardinal saturation. Lean exit 0 with empty logs incidence-and-equality-2. Reviewer PASS.

`IncidenceAndLedger.lean` (343 lines, SHA256 ce23bae1ccd8bef74986c7116adb42d57cd3370752126afda95d49231489b0fb) extends that snapshot with the weighted bound: sum over maximal-false rows I of 2^(number of gates true on I) <= 2^C.size. Valid false-choice sets are disjoint for distinct maximal rows, and each true gate contributes one unconstrained choice bit. Lean exit 0; only two deprecated dite tactic warnings in incidence-and-ledger.stdout, stderr empty. Reviewer PASS. Use Ledger instead of Equality when merging because it contains the full prefix.

Consequences for q3 line-blocks: 3-line and general-position 4-line blocks have exactly 8/16 maximal-false rows; the 5-line types have 30,31,32. At ANDcount=k, saturation applies to the 8/16/32 cases. For A=5 with 30 maximal-false rows, dirty gates can occur on at most two rows and never two on one row. For 31 rows, at most one row can have one true gate. Formal transfer from AO2 original gates requires a gate-value-preserving AO2-to-AND-count bridge; current checked ledger does not claim this transfer or solve gap2583.

## Root replan near15:00UTC

Dropped fullFano26search (checked27lower alreadymain), generic TopForm-implies-read1 (insufficient), and ANDcount=cover-implies-read1 (absorption counterexamples). Continue order3 fixed-windowSAT and5/6-lineblocks, weightedfalse-row ledger withAO2 bridge, and plane-specific soleOR/dirty-filter arguments. No full theorem, no PR; reductions_open=false. Reviewer scanspostedsteps readonly for exact matches to alreadycheckedcomponents; root retains only2583lease.

### 2026-11-25 15:01:16 UTC — restriction route: AO2 determining-row instance checked
`IncidenceAO2Rows.lean` is the latest self-contained critical-row snapshot. It adds a short fold-level semantic monotonicity proof for every AndOrOnly circuit (no readback or fan-in assumptions required) and `ao2_criticalRows_determine`, immediately instantiating library_route's `Pruning.DeterminesOn` for the critical row set. Lean exit 0, no warnings; complete logs `incidence-ao2-rows.stdout/.stderr` empty. The fold proof duplicates the independently checked structural agent's approach, with true-preservation phrasing.


## Review correction, new components, and posted-step census

Time: 2026-11-25T15:02:43.536834+00:00. Reviewer: submission_rules.

Import-rule correction: CONTRIBUTING.md lines 18–22 explicitly allow Mathlib and its modules in ordinary proof submissions, in addition to the project modules listed for the step. Earlier notes saying Mathlib must be removed from a final ordinary proof were too strict; that caution is withdrawn. Reduction-specific rules remain separate.

- IncidenceBlockCounts.lean PASS, SHA256 6ca0077b660100a8c538f5989a268626623a7112236f89aea6f71150dfb1458a. It proves exactly 30 and 52 closed-left-subset counts for two explicit transposed finite relations with decide +kernel. Independent Python enumeration over all 32/64 subsets reproduced the counts; each listed line has four points. It does not prove an embedding into the full q3 plane or a circuit lower bound. Reported Lean exit 0, complete logs empty. Only permitted maxRecDepth/maxHeartbeats options occur; no forbidden tokens.
- IncidenceAO2Rows.lean PASS, SHA256 44ec07e52a55862deb28fc1a519b54d39335e6b02fd11fe365a7921a66415886, 301 lines. Its first 239 lines exactly match reviewed MaximalRows. The extension proves AND/OR circuit monotonicity by listwise induction, then uses it to specialize row completeness to AO2 circuits. No output-validity assumption is needed for this semantic result. Reported Lean exit 0, empty complete logs and no forbidden tokens.

Read-only complete census of all 1,630 open rows in public-gaps-review.json (snapshot 2026-11-25T14:46:07.445Z) found no exact open posted statement already proved by the new weighted-choice ledger, saturated maximal-false lemma, critical-row completeness, or pencil-cover partials. Every AndCountCircuit candidate still asks for a concrete lower bound or a circuit construction; the plane candidates still require size or normalization bounds. No new-gap work or desk call was made.

The old 2592 child matches are already checked: L-meta-4725 is exactly the 15+notCount floor hypothesis of R_meta_2592_271, and L-meta-8295 is exactly the last-NOT factorization hypothesis of R_meta_2592_318. Their local SHA256 values match the checked feed: 1f9ecfd77d1ca6167a432c28243b294bb92df7242e37de34678357516ca2b3e2 and 3c4298fea2b9cb541d262b293745fd06cafd48ad0317a33fcc2b3bc2a827dc5d, respectively. They were merged in commits 6cfaa263 (PR9152) and c268955f (PR12508). The open siblings are L-meta-4727 (1–4 NOT exclusion) and L-meta-8297 (separator bound), neither proved by our archived partials.

### 2026-11-25 15:02:43 UTC — restriction route: row-count bridge checked
`IncidenceRowCounts.lean` extends the latest self-contained snapshot with injectivity of completionInput, a full characterization of maximal false inputs as closed completions, and a finite row set `maximalNegativeInputs`. `mem_maximalNegativeInputs` characterizes its members exactly, and `card_maximalNegativeInputs` proves its cardinality equals the number of closed point sets. Lean exit 0, no warnings; complete logs `incidence-row-counts.stdout/.stderr` empty. This supplies a generic bridge from the separately checked 5/6-line closed-set counts30/52 to exact maximal-negative row counts.
Optional direct full-q3 closure-count proof by kernel decide was stopped after about6min at9GB RSS to avoid starving parallel proof/search tasks; exit130, full logs preserved as `incidence-q3-count-attempt.stdout/.stderr`. The numerical count704 is still Python-verified only, not a Lean theorem. No failed enumeration theorem was added to a preserved Lean snapshot.


## Independent archival audit: AND state bridge and maximal-row counts

Reviewed by submission_rules at 2026-11-25T15:03:39.879200+00:00.

- IncidenceAndBridgeState.lean PASS, SHA256 9b5f94ed6e763925ece13a0ab26aad70937f507acbb7b9587025b78eddcc2be8, 551 lines. The copied first 393 lines match merged L_meta_7541 except the own-namespace rename. New exact-arity/noTop invariants ensure the state adds one AND record per original AND gate, preserves earlier wire forms, and maps AND gate k to the singleton marker indexed by the number of AND gates before k. This is the state-index component, not yet a full value-preserving bijection. Reported Lean exit 0; complete log has only unused simp/tactic warnings.
- IncidenceRowCounts.lean PASS, SHA256 6695cc79c59d58007dfdd9ae214668b0a273a6a18f583d11d19457d07e3af843, 373 lines. Exact reviewed AO2Rows prefix unchanged. CompletionInput is injective, maximal negative rows are exactly closed completions, and the finite-image count equals the number of closed point subsets. Reported Lean exit 0; both complete logs empty.

Forbidden source scans found no matches in either snapshot. Parent received frozen hashes and scope before archival push. No final-gap theorem or checker acceptance is claimed.

## Exact AO2 to AND-count compression (2026-11-25T15:04:23.402849+00:00)

`IncidenceAndBridge.lean` compiled exit 0 (`incidence-and-bridge-004.stdout/.stderr`, only inherited unused-simp warnings). Namespace `PEqualNP.Outside.L_meta_2583_aux.AndBridge`. `compress_exact` constructs, for every AO2 circuit C, a well-formed AndCountCircuit D with exactly Nat.card(AndIndex C) gates, identical output on every set of true inputs, and an equivalence from original AND indices to compressed gates preserving EACH gate value on EVERY input set. `AndIndex C := {j : Fin C.gates.length // C.gates[j].op = .and}`. Construction adapted from merged L_meta_7541; exact fan-in 2 excludes its constant-true/no-record branches. Newly checked `and_marker` maps gate k to record (take k).countP isAnd; this rank is bijective. This supplies the missing semantic bridge for transferring AndEquality.false_choice_ledger into the AO2 search. Frozen full file and earlier state-only snapshot are with the independent reviewer.

## 2026-11-25 15:04 UTC — certificate_search, L-meta-2583 local blocks

Checked component: `lemmas/IncidenceBlockCounts.lean` (Lean exit0, no diagnostics) counts30 and52 closed subsets for the transposed5/6-line block incidences. Independent reviewer reproduced these counts. This is finite combinatorics, not a circuit lower bound or a proof of the posted theorem.

The q3 Singer incidence uses differences {0,1,3,9} mod13. Complete orbit census of5 chosen lines has3 types: representatives {0,1,2,3,9}, {0,1,2,3,4}, {0,1,2,3,7}, with maximal-negative counts30,32,31. Four6-line types have representatives {0,1,2,3,9,10}, {0,1,2,3,4,6}, {0,1,2,3,4,7}, {0,1,2,3,4,5}, counts52,55,59,64. The densest6-line type is two3-line pencils plus nine cross-intersection points,17inputs,24edges; replacing canonical29 gates with28 would give a global63-gate counterexample. Counterexample agent owns its GP search.

Exact monotone SAT searches on3-line/13-gate and4-line/18-gate targets each returned UNKNOWN at600s, not UNSAT. Full logs are preserved in search/. A fixed14-gate3-line star encoding passed SAT and independently all4096 truth-table rows. Unrestricted5-line/23-gate SAT and5-AND weighted-ledger SAT remain running at this timestamp. The latter imposes at most2 true (AND, maximal-negative-row) events, a necessary consequence of library_route's checked weighted ledger. Its fixed14-gate sanity also passed.

Computational dirty-capacity classification (C++, not Lean): any AND of two ORs of singleton inputs in the30-negative block, if true on at most2 negatives, accepts at most4 positive edges. Four maximal dirty patterns achieve4: N(line1) AND (line1 OR point3); (N(line1) OR point3) AND line1; and the corresponding two line9 patterns. Each accepts exactly2 negatives. An A=5 circuit must birth all20 edges at fiveANDs, so each must birth4. This suggests a transport obstruction for a dirty star, but a complete generic proof and all6+-AND cases are unresolved.

The two nonread1 globalGP near-misses inspected so far had avoidable repeated-filter gates: first AND(x,x), then x AND ((x AND a) OR b). The latter simplifies by one gate to x AND (a OR b). Both were reported promptly to the search agent.


## Lease-ownership audit (read-only; inconclusive)

Time: 2026-11-25T15:06:06.546855+00:00. Reviewer: submission_rules. No desk calls or mutations were made, and no lease identifier was printed.

The saved first response for 2592 contains lease.terms.issued_at 2026-11-25T13:44:05.796Z and expires_at 2026-11-25T14:49:29.130Z; the saved first response for 2583 contains terms.issued_at 2026-11-25T13:59:02.364Z and expires_at 2026-11-25T15:00:37.581Z. Both responses report holding=5 and say the handle has reached its maximum held gaps. The terms timestamp remains unchanged across later 2583 renewals.

join.txt lines68–70 say points are computed by the desk and frozen into lease.terms when the step is taken, but do not define issued_at separately. tools/pnp.sh does not inspect issued_at or explain its meaning. The public profile at https://pequalnp.com/a/wneb-creator and its agent.js client display checked proof/contributor history, not lease ownership or issuance timestamps. Thus exclusive ownership and the interpretation of issued_at as lease creation rather than cached terms time remain UNVERIFIED. Older timestamps plus the maximum-hold note suggest pre-existing handle-level lease records, but this is inference rather than proof. Current evidence does not justify releasing either lease. Join lines107–113 also say HTTP410 can mean the step was settled or withdrawn, so an early410 alone cannot establish expiry or another pilot action.

15:06 UTC: Unrestricted5-line23-gate SAT also reached its900s bound with solver_exit0 (UNKNOWN), no witness or UNSAT certificate. Full logs preserved. Weighted-ledger5-AND run remains active.


## Independent archival audit: exact AND compression and small-side tests

Reviewed existing frozen work by submission_rules at 2026-11-25T15:06:59.344485+00:00.

- IncidenceAndBridge.lean PASS, SHA256 bb9c5b3a08734207c42ba3495fe6b99923c1f938b84fe82014338494b5ee8a0d, 667 lines. Reviewed State prefix unchanged. The new rank map is strictly ordered on original AND indices; finite equal cardinalities make it bijective. compress_exact constructs a well-formed AndCount circuit of exactly the original AND count, identical output function, and an equivalence of AND gates preserving every gate value on every input set. No hidden row restriction or weakened count. Reported Lean exit 0; full log has only the same unused simp/tactic warnings.
- IncidenceSmallRows.lean PASS, SHA256 e9e50ccd4fb41ef22849c04a3e4786cce4fc0a95c81d286250c08c3a237082cd, 416 lines. Exact RowCounts prefix unchanged. A point completion lies below the dual completion of its avoiding-line set. The explicit smallSide hypothesis ensures either the point side or that avoiding-line side has size at most k; supplied negative tests on both sides therefore suffice. No geometric smallSide result is claimed here. Reported Lean exit 0; full logs empty.

Forbidden scans have no matches. These are preservation audits of existing checked partials, not new proof work or a final gap result; parent received hashes and scopes.

## Direct AO2 false-row ledger (library_route integration)

`IncidenceAO2Ledger.lean` is the self-contained combination of frozen `IncidenceAndBridge.lean` and `IncidenceAndLedger.lean`, with duplicate imports removed. New namespace `PEqualNP.Outside.L_meta_2583_aux.AO2Ledger` transfers gate-value counts through the exact equivalence of original AND gates and compressed AND-count gates. `ao2_false_choice_ledger` therefore applies directly to original AO2 circuits. `dirty_incidence_budget` gives M.card + sum_I trueAndCount(I) <= 2^andCount. `five_and_thirty_rows` gives sum_I trueAndCount(I) <= 2 when andCount=5 and M has at least30 maximal-false rows.

Frozen source 1081 lines, SHA256 `cb6ad252e308915f3b2582470c58f68661cc2a1adb6fd5e8629852e43470367a`; Lean exit0. Logs `/tmp/oec/pequalnp-pilot-131/incidence-ao2-ledger-2.stdout` (46 inherited warning lines) and `.stderr` (empty). Only Mathlib and PEqualNP.Defs imported; forbidden scan returned no matches. Independent review requested. This removes the earlier AO2 transfer caveat but remains a partial toward gap2583.


## Independent archival audit: direct AO2 false-choice ledger

Reviewed by submission_rules at 2026-11-25T15:07:27.814968+00:00. IncidenceAO2Ledger.lean PASS, SHA256 cb6ad252e308915f3b2582470c58f68661cc2a1adb6fd5e8629852e43470367a, 1081 lines. The helper body exactly concatenates the previously reviewed Bridge and AndLedger bodies after removing duplicate imports. The new namespace transfers true-AND cardinalities through the value-preserving gate equivalence, proving the weighted choice ledger directly for original AO2 circuits. It then derives M.card plus total true-AND incidences at most 2^ANDcount, and the five-AND/at-least30-maximal-rows corollary bounds the total by2. Maximal false rows are explicitly hypotheses about the actual circuit. Reported Lean exit 0; full log has only inherited warnings; forbidden scan has no matches. Parent received the frozen hash before preservation; no full gap theorem or checker acceptance is claimed.

15:07 UTC: Parent paused all work because lease ownership is uncertain. The remaining weighted-ledger SAT process was stopped with SIGTERM after505s; solver_exit−15, no result. Full outputs and source preserved, certificate-search-status.json records no active child processes. No new proofwork or desk calls made.

### 2026-11-25 15:07:44 UTC — restriction route frozen for lease pause
Latest fully compiled, independently reviewed snapshot is `IncidenceSmallRows.lean`,416 lines,SHA256 e9e50ccd4fb41ef22849c04a3e4786cce4fc0a95c81d286250c08c3a237082cd; full build logs `incidence-small-rows.stdout/.stderr` empty. It includes all prior row lemmas and proves small_rows_suffice from the explicit hypothesis |X|>k ⇒ |avoidingLines X|≤k.
At the parent pause, one already-launched compilation finished with exit1: `IncidenceBonferroni.lean.incomplete` (source preserved without fixes) contains a generic four-set Bonferroni bound and the intended13-line small-side theorem. Only errors reported are unknown constant Finset.eq_empty_iff_forall_not_mem.mpr at line462 and resulting no-goals error at463. The source is NOT a compiled result; complete logs are `incidence-bonferroni.stdout/.stderr`. No fixes or new builds were made after the pause.
A superseded715-case finite four-point check was stopped before the pause in favor of the algebraic Bonferroni route; exit130 and complete logs preserved as `incidence-q3-small-attempt.stdout/.stderr`. No finite q3 count or four-point certificate was certified.

## Counterexample searches paused — 2026-11-25T15:07:57.475876+00:00

Root reported uncertain lease ownership. Every active search was stopped; the five remaining processes exited 130. No fresh desk request or release was made by this agent. Full sources, data, stdout, stderr, and a SHA256 manifest are now archived in `results/orch/search/counterexample/`. No target counterexample was found. SAT cases remain unknown, not proved impossible. The archive README records the exact limitations and the redundant structure found in approximate candidates.


## Final pre-retry preservation audit

At 2026-11-25T15:09:54.653209+00:00, submission_rules completed independent read-only archival review. PASS for the authorized archival push, with the following scope.

The counterexample manifest contains113 entries:103 archived source/data/log artifacts and10 intentionally omitted CNF inputs. All103 archived sizes and SHA256 hashes match. The only additional files are README.md and manifest.json. Both older36-artifact manifests also match. Reviewed access behavior of22 distinct Python/C++ sources: finite computation, task-local reads/writes, and argv-based calls to the local cadical solver; no environment/credential access, network client, shell execution, or unexpected deletion was found. A scan of all276 then-present results/orch files found no credential-shaped GitHub tokens, private keys, authorization values, or lease URL parameters. No symlinks were present. No environment variables or credential values were read or printed by the audit.

IncidenceBonferroni.lean.incomplete is explicitly UNVALIDATED, SHA256 b633327768bdaa8acdc3ef1f1b3c0200f3a5e8338779d8392c56f10dfa28134c. Its complete logs preserve exit1 errors at lines462/463; NOTES already states it is not compiled. It has no forbidden proof escape or code-execution tokens. It is safe to preserve as an incomplete artifact, never as a checked result. Search README/status files accurately distinguish UNKNOWN/interrupted solver runs, computational checks, checked finite counts, and the old certificate exit137. They assert no unsupported UNSAT result or target counterexample.

Manifest SHA256:06214a358590a70c1e6965d59a3b42f06a910d86b635e2cb7b3843a78cbd41ef. Certificate-search status SHA256:621cd26e28f8ab9387781e569d6769f0caa9665ec9c6a1eb2c919548b88ea8fe. All checked frozen components named in the parent request had already passed independent review. No lease was released or acquired by this reviewer.
