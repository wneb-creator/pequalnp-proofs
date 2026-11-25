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
