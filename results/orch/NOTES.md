# Pilot 110 shared notes

Gap: L-meta-2592. Root holds the only team lease. No sub-agent may call desk or change git.

## Problem
Petersen edge function cannot be computed with <=19 AND/OR/NOT gates of fan-in <=2 if circuit contains a NOT. Imports: PEqualNP.Defs. Exact statement in /tmp/oec/pequalnp-pilot-110/statement.txt. Reductions allowed but desk reports 3 live reductions already. Need investigate eligibility.

## Instructions
Agents own separate scratch files under results/orch/lemmas or /tmp/oec/pequalnp-pilot-110. Append findings under your task name here; never overwrite others. Read CONTRIBUTING.md and README.md. Never print credentials. Root alone commits/pushes/submits/renews.

## reduction_strategy (14:07 UTC)
All three permitted reductions already exist on latest main: R_meta_2592_271 (15 binary gates plus few-NOT cases), _408 (normalization and finite normalized lower bound), _318 (split at last NOT, then prefix/suffix separator). A fourth reduction is not eligible under current cap. Preparing an elementary proof of the cutLast component from _318; prefix output chooses the first NOT operand or an out-of-bounds false sentinel.

## counterexample — initial combinatorial checks

Verified exhaustively in Python: Petersen graph has 15 edges, independence number 4, five maximum independent sets, minimum vertex-cover size 6, no triangles, and each vertex pair has at most one common neighbor (so no 4-cycles). Ordinary star factoring gives 15+6−1=20 gates. No circuit semantic loophole identified: each gate contributes exactly one sequential wire; fan-in condition really excludes mod/majority. Running a C++ bit-parallel stochastic 19-gate AND/OR/NOT synthesis search over all 1024 inputs, seeded from random 20-gate star decompositions. This search is heuristic, never proof of a lower bound.

## status_review — reduction history and guard audit (2026-11-25)

Three reductions are already checked and merged, matching `reductions_live=3` and exhausting the stated cap:

- `R_meta_2592_271.lean`, PR https://github.com/open-goat/pequalnp-proofs/pull/7606 (merged 2026-11-24 19:12 UTC): first premise is `15 + notCount C <= C.size` for Petersen; second excludes 1–4 NOTs at <=19 total gates. The first premise is now exactly proved by `lean/PEqualNP/Outside/L_meta_4725.lean`, 3225 lines, with `petersen_binary_lower` near line 3179. Remaining hard premise still needed.
- `R_meta_2592_408.lean`, PR https://github.com/open-goat/pequalnp-proofs/pull/9069 (merged 2026-11-25 03:27 UTC): normalization to legal earlier-wire reads, unary NOTs, output last; either retains NOT or strictly reduces size. Second premise excludes those normalized circuits at <=19 with NOT, or <19 without NOT.
- `R_meta_2592_318.lean`, PR https://github.com/open-goat/pequalnp-proofs/pull/11694 (merged 2026-11-25 05:14 UTC): split at last NOT into fan-in-two prefix P and monotone suffix Q, total cost P.size+Q.size+1; second premise excludes Petersen when P.size+Q.size<=18. The PR body includes an explicitly checked, reusable proof of the general last-NOT split (~70 lines). Source API response saved in /tmp/oec/pequalnp-pilot-110/status-review/pr-2592.json.

The currently allowed `PEqualNP.Defs` closure has no Petersen theorem or reduction imports. Reusing Outside results requires copying/adapting their relevant proofs into the assigned file, under its own namespace; these modules cannot be added as imports.

Other checked components useful for a vertex-restriction strategy:
- `L_meta_8035.lean`: Petersen minus vertex (9 inputs), size=15 and zero NOT impossible.
- `L_meta_8037.lean`: same, size=15 and one NOT impossible.
- `L_meta_8039.lean`: same, size=15 and two NOT impossible, via a 14 non-NOT gate floor.
- `L_meta_8367.lean`: strict legal normalized nine-input circuits with <=15 gates and <=2 NOT cannot compute the deletion function.
- `L_meta_7493.lean`: the nine-input deletion function requires >=14 non-NOT gates (4140 lines).
These are not available from Defs alone, but several accepted source proofs already share the same circuit elimination machinery.

Updated format/independent-review checklist:
- PR diff against upstream main adds exactly one UTF-8 ordinary 100644 file <=512 KiB: `lean/PEqualNP/Outside/L_meta_2592.lean`. Results artifacts must not enter the PR diff.
- Plain allowed initial imports are Mathlib and PEqualNP.Defs only; import word forbidden after header.
- Helpers inside exactly `namespace PEqualNP.Outside.L_meta_2592` or `_aux` (or descendants); matching named `end`, all scope commands column 0. Final theorem top-level with full exact name and last in file. No declarations, namespaces, or command words after it.
- Raw text is scanned, including comments: no `_root_`, quotes, quoted identifiers, `sorry`, `axiom`, `native`, `bv_decide`, `Lean`/`IO`/`Meta` namespace tokens, metaprogramming commands. Avoid comments containing forbidden words.
- Only `@[simp]` or `@[local simp]`; avoid persistent simp helpers and instances per CONTRIBUTING. Only four limit options, each `set_option ... <digits> in` above one declaration.
- Run `.github/scripts/outside-guard.mjs imports <file> <imports.json> <repo-relative-file> check` (imports JSON is an array, e.g. ["PEqualNP.Defs"]). This validates import, plain-text, and namespace restrictions together. `tools/check-lean.mjs` alone does not perform these text guards.
- Run `lake build PEqualNP.Outside.L_meta_2592` and `node tools/check-lean.mjs <file> <statement.txt> check`; checker pins build config, rebuilds project dependencies, rechecks kernel and axioms, and compares exact statement in a clean definitions environment. Preserve full stdout/stderr.
- Desk must still post step on submission; lease renewal immediately before long build/check and before push. Three reduction slots full means no fourth reduction.

### Last-NOT reference
PR https://github.com/open-goat/pequalnp-proofs/pull/11694 (merged) includes a separately checked 70-line proof of the first cutLast child in its body. Saved as CutLastReference.lean in the reduction_strategy lemma directory, with only namespace/name adaptation. Independent draft CutLast.lean is 85 lines. Both await local cached Defs build. This does not resolve the Petersen-specific separator.

## counterexample — verified upper bound

Prepared `results/orch/lemmas/counterexample/UpperBound.lean`: 20-gate monotone witness, FanInTwo and size lemmas, finite eval proof pending Lean cache. Independent Python evaluation checked all 1024 inputs and all backwards-wire conditions. Heuristic search reached a 19-gate monotone circuit for Petersen plus edge (1,9), only five false positives (masks 514,522,546,554,770); sent structure to SAT agent. No counterexample.

## toolchain_setup — 2026-11-25 14:08:07 UTC

Prepared Lean v4.36.0 in `/tmp/oec/pequalnp-pilot-110/toolchain/lean-4.36.0-linux`. Use `source /tmp/oec/pequalnp-pilot-110/toolchain/toolchain-env.sh` before commands; it sets PATH, PEQUALNP_REAL_LAKE, PEQUALNP_HOME and MATHLIB_CACHE_DIR to nonsecret job paths.

`lake exe cache get` succeeded for 67 direct Mathlib roots and their 2480 dependencies. Genuine Mathlib root archive 79da901f0eeeaa4a.ltar was fetched separately from official cache; its comment identified pinned Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. This meets checker root-artifact requirement without installing unused Mathlib dependencies. Do not import Mathlib root in proof files: full cache exceeds disk.

`lake build PEqualNP.Defs` passed with 5147 jobs; zero Mathlib source module builds. Project toolchain/config/manifest remained unchanged. Complete diagnostics under `/tmp/oec/pequalnp-pilot-110/toolchain/`. Downloaded archives cleaned; approximately 1.2 GB free.

### Checked partials (2026-11-25T14:08:58.802824+00:00)
CutLast.lean (85 lines) and TrimNot.lean (71 lines) both pass lake env lean, exit 0, no stdout/stderr. CutLast proves the full universal last-NOT factorization from R_meta_2592_318. TrimNot preserves FanInTwo, circuit size, every wire value/evaluation and existence of a NOT while restricting NOT operands to length <=1. Neither proves the final Petersen-specific bound. Logs are in /tmp/oec/pequalnp-pilot-110/reduction_strategy/{cutlast,trimnot}.{stdout,stderr}.

### status_review — first partial push review
Reviewed TrimNot.lean, UpperBound.lean, CutLast.lean, and CutLastReference.lean source. PASS for preservation of checked partials, conditional on compilation logs: no forbidden proof escapes, literals, attributes, options, or imports. TrimNot preserves NOT semantics because GateOp.not reads only headD; all size/op/eval/hasNot claims are meaningful. UpperBound proves a 20-gate monotone construction only, and does not settle <=19 circuits containing NOT. Its Pilot110Partial namespace must be changed to L_meta_2592_aux on merge. These scratch files do not carry the posted final theorem and must not be described as a completed proof or submitted as a proof PR. Root alone performs git operations.

## sat_strategy (2026-11-25 14:09 UTC)
CaDiCaL 3.1.0 built in scratch. Existing LinkN/LinkN2 encodes normal-form arbitrary AND/OR/NOT circuits (padding allowed); direct use needs forbidden-import helper proofs inlined and local macros expanded. Boundary-only CNF (15 minimal true +15 maximal false inputs), <=4 NOT and one-hot selectors, is SAT in 17.39 wall seconds: decoded 19-gate model uses2NOT but is wrong on250 of1024 assignments. Thus boundary rows alone are far too weak with negation. No lower-bound certificate obtained. Testing82rows next: all support<=2, maximal false, all-one and single-zero rows, plus <=4NOT and NOT-or-leading-padding constraint. Added count/padding constraints still require proof that normalization preserves these conditions; all SAT candidates are checked on full truth table. Complete scripts/CNFs/solver logs in /tmp/oec/pequalnp-pilot-110/sat_strategy.

## counterexample — Lean-checked partial

2026-11-25T14:09:59.685731+00:00: `UpperBound.lean` compiled successfully via `lake env lean`, exit 0, empty stdout/stderr. This checks the explicit 20-gate monotone construction, its FanInTwo condition and size, and all inputs using kernel decision. It does not prove the assigned 19-gate lower bound. Parent notified for immediate preservation.

### status_review — last-NOT child IDs and staged review
Public node JSON confirms R_meta_2592_318 child 1 is L-meta-8295, CHECKED at 2026-11-25 06:23:49 UTC; child 2 is L-meta-8297, still CONJECTURE. Their exact statements are saved under /tmp/oec/pequalnp-pilot-110/status-review/L-meta-8295.json and L-meta-8297.json. Public node URLs are data.pequalnp.com/data/lemma/<id>.<node hash>.json, with hashes from public map nodes. CutLast therefore reconstructs an already checked component; the separator remains unresolved.

Independently reviewed initial staged 9-file partial-preservation diff, including source, validation, timeline, and full build logs. git diff --cached --check passed. Source forbidden-token scan and staged credential-shape scan were clear. Verdict: PASS FOR PARTIAL BRANCH PUSH only; not a proof PR, and validation accurately says posted theorem unproved and exact checker not run.

## sat_strategy (2026-11-25 14:14 UTC)
82-row base+<=4NOT+NOT-or-pad run reached300s limit with unknown. Full1024-row instance now running1200s:1,527,347clauses,249,912numberedvariables. Additional search-only normal-form restrictions: binary source functions incomparable across sampled rows; NOT input nonconstant; firstactive gate representative(0,0)NOT,(0,1)edgebinary,or(0,2)nonedgebinary under Petersen automorphisms. These need additional Lean normalization/count/aut proofs before UNSAT could establish target. All inputs remain fully checked for any SAT witness. Default bv_decide is NOT admissible: official Lean docs confirm native checking introduces a dedicated axiom, so use only repo kernel LRAT reflection if a certificate route succeeds.

## counterexample — search summary at 2026-11-25T14:14:36.158091+00:00

First unrestricted 19-gate heuristic: 1,173,839,213 candidate evaluations across 2,246,487 restarts in 300 seconds; closest has 5 false-positive rows and no NOT. Second heuristic requiring at least one NOT: 1,143,012,558 candidates, 1,879,556 restarts in 300 seconds; closest has 10 wrong rows and an unused NOT. Third run requires a NOT on the output dependency cone; running, currently 18 wrong rows. Exact local perturbation of the first near-solution checked all 2,641,950 choices of one NOT replacement plus one arbitrary binary gate replacement; closest has 11 wrong rows. These are search statistics only, with no global lower-bound claim. Complete sources and finished logs copied beside UpperBound.lean for preservation.

The tempting seven-gate six-cycle replacement is ruled out by the already checked L-meta-106 cycle theorem, which counts NOT gates. Parent and SAT agent notified; that subroute is dead.

Third heuristic complete (live NOT required): DONE restarts=1214970 evaluations=728956053 best=17. No counterexample. Source and complete log preserved beside the checked UpperBound.lean partial. All counterexample search processes have ended.

## Root status, first replan

- Baseline mathematical components now Lean-checked and pushed in c93f2f11. Posted theorem remains open; no PR.
- All three parent reduction slots already occupied; do not submit duplicate reduction.
- Full-row exact SAT search started/starting after renewal14:14:35UTC; sparse sampled rows yielded spurious models. Any finite search restriction must have separate soundness proof before a theorem claim.
- C6 standalone7gate shortcut is already excluded by checked L106; only cross-component sharing can help near19.
- New small target: remove sole terminal/penultimateNOT from endpoint-correct monotone output using prefix monotonicity; proof_strategy owns it.
- Guard rule: bv_decide may add a forbidden axiom in current Lean; use explicit kernelchecking/decide+kernel only.
- Do not delete any active cache artifacts; .c files are part of Lake artifact-validity checks. Restore cached modules before resuming builds.

## sat_strategy (2026-11-25T14:17:55.499756+00:00)
Checked partial: results/orch/lemmas/SatCofactor.lean compiles with pinnedLean/Defs usingkernel decide, exit0. It proves every variable ofPetersen remains essential after fixinganyother variable tofalseortrue, viaexplicit≤2vertex witnesses. Rootnotifiedforimmediatepush. Genericcircuitreaderbridge beingprovedbyproof_strategy.
New82rowsearch adds firstbinarygate-inputs-read-again condition, firstOR(nonedge)NOT-count≤2−padding fromL5236, firstNOT combinedreader-count≤3−padding fromL5367, andNOT-count+padding≤4fromL4725. Thesearederivedproofideas, implementationnotyetLean-linked; onlysearchresults, notproof. Full1024row20minruncontinueswithouttheseextraconstraints.

### status_review — second partial source review 2026-11-25T14:18:21.695677+00:00

Reviewed current 190-line named file (6985 bytes) and 20-line SatCofactor source (707 bytes). PASS for partial preservation, conditional on successful named-file build. No forbidden tokens, unsupported imports/attributes/options, or namespace problems. New vertex-cover lower bound and dependency witness are meaningful finite lemmas; neither asserts the circuit lower bound. Independently enumerated all 1024 vertex subsets: minimum Petersen vertex cover is 6. Independently checked all 180 (u,v,b) dependency-witness cases: each has a valid w. git diff --check clean. Exact posted theorem remains absent; no proof PR approval.

### status_review — Endpoint partial 2026-11-25T14:19:51.069616+00:00

PASS for checked partial preservation of Endpoint.lean. Final NOT cannot realize a function with false/true endpoint values after a monotone prefix. A penultimate unary NOT feeding final AND/OR can be deleted, dropping only its final-gate occurrences, and the resulting monotone circuit has exactly one fewer gate. The proof handles out-of-range wire references through the existing false default; no hidden legal-wiring assumption is needed. Exact monotone-prefix and endpoint hypotheses prevent overclaiming general internal-NOT elimination. File source scan clear, only Defs import and no attrs/options/escapes. Scratch Pilot110Endpoint namespace needs own-file namespace adaptation before final submission. Full190-line named build review remains conditional after root stopped memory-heavy run.

## proof_strategy: endpoint deletion and first-gate readers

- `results/orch/lemmas/proof_strategy/Endpoint.lean` (250 lines) compiles with only `PEqualNP.Defs`. New `final_not_impossible`, `remove_terminal_not`, `penultimate_not_smaller` lemmas show a monotone prefix followed by a unary NOT and at most one final AND/OR gate cannot be an essential use of NOT for an output taking false/true at the cube endpoints. The penultimate case explicitly removes the NOT and removes its neutral reads, producing a monotone circuit one gate smaller. Invalid source indices and constant prefix wires are handled. Generic monotone-wire infrastructure was adapted from checked L_meta_610. Build log: `/tmp/oec/pequalnp-pilot-110/endpoint-build.log`, empty, exit0.
- `results/orch/lemmas/proof_strategy/ReaderBridge.lean` (89 lines) compiles. `first_gate_must_read_again` proves a first AND/OR gate cannot be the only reader of an input when the target retains dependence on that input after the other source is fixed to the controlling value. Arbitrary suffix gate operations and invalid reads are allowed. Pair with SatCofactor.sat_dependency_witness. Build log: `/tmp/oec/pequalnp-pilot-110/reader-bridge-build.log`, empty, exit0.
- Both files scanned: no forbidden `_root_`, quotes, attributes, sorry or native_decide. No claimed proof of the full gap.
- Reviewed `counterexample/local_synth.py`: CNF encoding and full1024-row CEGAR decoding consistent. Local UNSAT covers selected fixed-backbone windows only; require_not assumes monotone BASE; constanttrue must export as AND[].
- Mathematical search observation: two near-solution rectangles17,22 form C6 plus extraneous edge(1,9) in7gates. Rewriting just them seeks a7gate C6 realization; include common-neighbor6 star for a broader theta gadget.

### status_review — ReaderBridge source review 2026-11-25T14:21:17.175089+00:00

PASS for compiled ReaderBridge.lean source preservation. Cofactor sensitivity forces a later reader of the first binary gate input after the other input is fixed to a masking bit. Equal-length wire vectors and getD-default reasoning cover out-of-range/future reads. Arbitrary later operations are allowed because the proof only uses equality of their operand lists. Output-ne-u is explicitly required and necessary. Distinctness u!=v follows from the essential-witness premise if needed, so its absence is not a gap. No global lower-bound claim, no forbidden constructs, only Defs import. Scratch Pilot110ReaderBridge namespace must be adapted before integration. git diff --check clean.

## toolchain_setup — full checker disk blocker (2026-11-25 14:22 UTC)

The earlier Mathlib-root artifact only satisfied the initial existence check. CheckLemma dynamically imports full Mathlib, so full runtime closure is needed. Exact measurement of all 9,117 pinned archives: 7,032,216,931 bytes expanded; 6,213,035,400 bytes in required olean/private/server/IR artifacts. Existing files leave 4,620,204,936 additional required bytes. After compressed archive cleanup, free space is 719,810,560 bytes: minimum deficit 3,900,394,376 bytes. Static/editor/source cleanup cannot recover enough. See `results/orch/toolchain-validation.txt`.

A failed C-artifact cleanup triggered Lake source rebuilding; root stopped it and all 2,480 selected prebuilt modules were force-restored. Final Defs no-build check and fresh Defs import pass. Do not remove generated C or ilean files: Lake checks them even for dependent builds. Full Mathlib import remains unavailable; the checker executable itself built successfully. No further package-artifact cleanup is planned.

## counterexample — algebraic upper-bound proof and local synthesis

2026-11-25T14:24:10.860587+00:00: `UpperBoundAlgebraic.lean` replaces exhaustive finite evaluation with circuit simplification, canonical six-star expression, distributivity and Boolean AC simplification. Lean passed exit0,48.588seconds,peak2,912,376KiB (~2.78GiB), no diagnostics. Parent notified immediately. Original checked file retained separately.

Fixed-backbone local CNF synthesis passed independent audit from proof_strategy plus positive/negative controls (known20gate circuit fixed and with4free gates SAT, flawed19gate fixed UNSAT). All22 selected2–4gate windows and the6gate rectangle-builder window are UNSAT on74 boundary/error rows. Broader9/10/12/15gate windows timed out at15seconds. Two cross-component9/10gate windows are now running300seconds with at most4NOTs. Any SATmodel is checked on all1024inputs before claiming a witness. None found so far.

### status_review — third preservation sources 2026-11-25T14:24:20.060811+00:00

PASS for compiled UpperBoundAlgebraic.lean, extended SatCofactor.lean, and root/VertexCover.lean. Algebraic upper-bound proof retains exact20-gate circuit and uses Boolean distributivity/commutativity after unfolding. Cofactor extension constructs the required witness inputs and proves output bounds 10<=output<10+size for any circuit computing Petersen, using default-false invalid outputs and edge witnesses avoiding any input. Arbitrary gate operations do not undermine preservation of existing input wires. VertexCover proposition unchanged from independent exhaustive check; plain decide is permitted. No forbidden tokens/imports/attrs/options. No posted theorem yet; these are source-artifact partials only, not a proof PR.

2026-11-25T14:24:37.767910+00:00: both broader9/10gate local synthesis runs ended UNKNOWN at300seconds; noSATmodel obtained. All23 smallerwindow cases were UNSAT, but no global lower bound is established. No active counterexample search or Lean processes remain. Full solver logs preserved under the counterexample lemma directory.

## sat_strategy (2026-11-25T14:24:55.054617+00:00)
SatCofactor.lean now includes checked output bounds: every circuit computing the Petersen function has output index at least10 and below10+size. The finite cofactor-essentiality lemma and output bounds discharge the concrete hypotheses of the generic first-gate reader bridge. Latest compile passes with empty output after removing one deprecated theorem alias. SAT artifacts are preserved under results/orch/sat (about8MB compressed). No full lower bound or counterexample has been found.

### status_review — integrated named partial review 2026-11-25T14:27:03.480801+00:00

PASS for preservation of actual 590-line/25679-byte named module after reported lake build exit0. Compared body text against all six reviewed sources: TrimNot, CutLast, VertexCover, Endpoint, Reader match exactly excluding scope headers; SatCofactor differs only dif_pos versus cleaned dite_eq_left. Namespace nesting and scope ends are correct; sole import Defs, forbidden scans clear, git diff --check clean. Repository checkProofFile run on actual bytes reports exactly the two expected missing-final-theorem refusals, no other plain/import/namespace errors. Zero top-level theorem declarations, so the file makes no claim to prove the posted gap and is not PR-ready.

### status_review — symmetry table 2026-11-25T14:28:36.415537+00:00

PASS for compiled 147-line SatSymmetry.lean preservation. Independently parsed the table and verified all100 maps are permutations, all200 representative-image conditions, and all10000 ordered adjacency-preservation conditions. Adjacency is exactly undirected Petersen15edges; finite index bounds cover all list lookups. Own-file descendant namespace and four-limit option syntax valid; no forbidden tokens. This theorem gives finite automorphism witnesses only, with no circuit relabeling bridge or complete lower-bound claim.

## Root continuation state

- Job began2026-11-25 14:00:30UTC; minimum sustained-effort window ends15:30:30UTC unless the exact target is proved/refuted. Continue the held L-meta-2592 step.
- Own lease d30cd9f5-2ff3-41d8-b031-e33b731294ac only. Root renews every5minutes and before long work; full responses saved in scratch desk-log.txt. Never touch any other pilot lease.
- Branch pnp/pilot-110 only, authorized origin fork. Two preservation pushes already succeeded (c93f2f11,7b799d1f); next includes590-line integrated partial. No PR exists.
- Exact statement in /tmp/oec/pequalnp-pilot-110/statement.txt; gap metadata in gap.json.
- Named file builds, but has no exact final theorem. Local checker actually ran and returned exit3/CHECKER FAULT because fullMathlib closure does not fit. See checker-001 logs and toolchain-validation.txt. Do not claim acceptance.
- Full-table SAT remains running; proof_strategy and reduction_strategy pursue floor16/two-binary-gate deletion, counterexample builds vertex transitivity, sat_strategy owns pair symmetry/cofactor certificates.

### status_review — TwoDrop and SignedPrefix 2026-11-25T14:30:30.986185+00:00

PASS for compiled source preservation. TwoDrop proves that fixing p=false removes >=2 non-NOT gates under explicit NOT-only-prefix, first-gate-disappearance, first-gate-agreement-on-distinguishing-pair, and nonconstant-cofactor hypotheses. Restriction semantics and nonconstant cofactor justify constructing a Circuit from surviving inr output status; invalid reads handled by status/default invariant. Count is non-NOT gates (all AND/OR arities under FanInTwo), not strictly binary unless cleanliness is separately known. Restricted Circuit still has n input slots and computes f(update z p false), so a9-input lower bound needs a renumbering bridge. SignedPrefix proves every existing wire in a legal unary-NOT-only prefix is a signed original input; constants/invalid reads are excluded by explicit earlier-wire cleanliness, including empty-input boundary. Same-input binary and controlling-bit classifications are finite Boolean identities. No proof escapes, unsupported imports/options/attributes. TwoDrop scratch namespace needs own-file adaptation on integration. Neither source states the posted bound.

TwoDrop was extended during the review with zero_prefix_literal_constant and binary_drops_with_constant_input; both additional statements and proofs also pass source review. Current reviewed source882lines/39875bytes. Require a matching successful compile before preserving this latest revision.

### status_review — fourth preservation snapshot 2026-11-25T14:32:23.102383+00:00

PASS for immutable TwoDropChecked.lean (SHA25655348d2b8934430897f2c6542b4d4f4c04693aea5172e30030f54d7d5c2ab2a1), unchanged SignedPrefix, and new SignedFirst.lean. TwoDrop hash exactly matches previously audited source. SignedFirst Least means length-minimal among equivalent clean circuits with no greater non-NOT count; constant-gate removal preserves that budget and strictly shortens, proving least_no_constant. Clean NOT-only prefix yields signed literals; if first binary gate uses the same underlying variable, Boolean classification makes it constant or alias, both prohibited by Least. Thus least_first_binary_signed correctly guarantees distinct underlying variables with independent polarities. No global16-gate floor or posted theorem asserted. Repository plain/import guards pass both files with theorem helpers; namespaces/section ends are explicit and valid for source artifacts.

## reduction_strategy — signed-prefix normalization (2026-11-25T14:32:49.051151+00:00)
Three new files each pass lake env lean with exit0 and empty diagnostics:
- SignedPrefix.lean 94 lines SHA256 4d9261842a9d263c67457b7b14584f7f3bda377672249dc2eea9ab91a91e7faa
- SignedFirst.lean 998 lines SHA256 f20f1594929fce0dcd6cd6ff6d2786482e07d6602ea9957d014113e40e9d3553
- FirstBinary.lean 1056 lines SHA256 e49c6aea565a82d258c94c24b00c93ac4210abe1e3e780cad99e8404a6979096

SignedPrefix classifies each valid wire in a clean NOT-only prefix as a signed primary input, and supplies binary controlling values. SignedFirst adds Least.no_constant (via existing drop_core) and excludes first-binary operands with the same underlying input: identical signs give an alias; opposite signs give a constant. FirstBinary adds existence of a first binary gate for any nonconstant target not equal to a signed input, then returns A++g::B with A all-NOT, g binary, and signed inputs on distinct variables. It copies checked L7493 simplifier/Least infrastructure for standalone validation; final integration should deduplicate that infrastructure. SatCofactor.sat_nonconstant and sat_not_signed_input discharge the concrete target hypotheses. These are prerequisites to the proposed floor16 proof, not the completed lower bound.

[2026-11-25 14:33 UTC, proof_strategy] New checked generic two-binary deletion component: `proof_strategy/TwoDropChecked.lean`, 885 lines, SHA256 `55348d2b8934430897f2c6542b4d4f4c04693aea5172e30030f54d7d5c2ab2a1`. Complete matching Lean log is `TwoDropChecked.build.log`; warnings only, exit0. New theorem `Pilot110TwoDrop.Restrict.restrict_two_drop` handles a NOT-only prefix, first binary gate erased by restricting u=false, and an output-distinguishing pair differing onlyu on which the first binary gate agrees; it constructs a cofactor circuit with at least two fewer non-NOTs. Generic no-drop independence infrastructure is adapted from checked L3979; simplifier infrastructure from checked L5026. Additional new helpers derive literal-wire constancy after restriction and binary deletion with one constant input. Snapshot immutable for pushing. Assembly combines FirstBinary, SatCofactor, automorphisms, and checked residual14 floor L7493. Exact L7493 statement deletes vertex9 (Fin.lastCases false), correcting the earlier delete0 assumption.

[2026-11-25 14:37 UTC, proof_strategy] Important stronger dependency found: L6581/L5236 contain a signed 15-binary lower bound for the ordinary nine-input Petersen deletion graph, via `rootSImpossible` / `nineFloor`. The `edge` definition at L6581 line753 is exactly original Petersen with vertex9=false; all512 rows independently matched by status_review. L6581 already proves global16, so our novel two-drop theorem should instead yield global17. Working wrapper NineFloor15Core.lean copies only the checked certificate through orbitAllInputs, then proves `nine_binary_floor` for arbitrary FanInTwo circuits computing edge. Counterexample agent supplies arbitrary-u-to-last9 residual renumbering. PetersenTwoDropChecked.lean is frozen, compiled exit0, hash54a84ce89e4c2952f2e3a5e225b52336123f4f3a28fccddec381e39b6837ecbb.

## status_review: refreshed descendants and independent nine-floor audit 2026-11-25T14:38:28.665240+00:00

Refreshed public head timestamp 2026-11-25T14:31:57.269Z. Compared all1884 Petersen-tagged nodes against the prior proof-strategy map: zero newly checked Petersen nodes. Of712 checked Petersen entries, inspected710 local final theorem statements and fetched public statements for missing994 and1697 (only a floor15 total-gate fact and a conditional first-gate reduction respectively). No checked17/18 non-NOT floor, nor an unconditional full10-input one/two/three-NOT contradiction, was found in this census. Exact statement inventory is in scratch petersen-all-checked-statements.json. This is a bounded search result, not a proof that no such helper exists anywhere.

Important existing result: L_meta_6581.lean:4545 proves16 ≤ List.countP(fun g => !g.op.eval [false]) C.gates for every FanInTwo C computing exact Petersen10. Under FanInTwo the predicate counts precisely AND/OR. PR https://github.com/open-goat/pequalnp-proofs/pull/13148 merged2026-11-25T09:54:58Z; public node marked checked2026-11-25T09:55:03Z. Public exact JSON saved as L-meta-6581.json. The previously investigated floor16 route duplicates an existing checked theorem.

The stronger useful helper is L6581:4496 nineFloor : Lower true inputs graph15. Independently decoded the source hexadecimal truth tables: inputs at749 are exactly the nine independent coordinate tables, graph at750 matches original Petersen with vertex9=false on all512 assignments; edge at753–756 lists exactly its12 surviving edges. There is NO extra useful seed input: Lower roots are inputs only. Free constants and complemented signals are permitted, so this is a non-NOT bound. Extended pins at4443 map original vertices0..9 to row bit positions[9,7,5,8,6,4,2,0,3,1]; independent1024-assignment verification confirms its target. Low512 projection fixes original0=false and permutes the other coordinates to the same nine-input graph.

Simplest reusable ordinary-Circuit bridge: L6581:780 raw_signed C legal small computes, where small is C.gates.countP(fun g=>!isNot g)≤14 and computes is ∀x:Fin9,C.eval(ofFn x)=edge x, yields k≤14 plus Live true graph k S and S⊆inputs. Apply orbitAllInputs at3977 to rewrite S=inputs.toFinset, then rootSImpossible at3960 to contradict. This proves ordinary nine-input non-NOT floor15 without Extended or a new Lower realizer; combine with our checked two-drop lemma to aim for17.

L4727 remains conjecture. Its R_meta_4727_1 children: L8021 checked but vacuous (noNOT plus atLeastOneNOT), L8023 conjecture; cutLast child8295 checked and separator8297 conjecture. R4727 related merged PRs9316,9949,9977 and closed unmerged10086 found in fully paginated targeted structured search. Closest checked restricted3–4NOT case is L5236: an18-gate suffix after a free nonadjacent OR(x0,x2), ReadsBack11 and valid gate output, with3≤notCount≤4 cannot compute Petersen. This does not establish the unrestricted3NOT case. L5238 handles≥5NOT under the same free initial OR setup.

## counterexample — checked symmetry and residual renumbering

2026-11-25T14:39:04.860566+00:00: `ResidualRenaming.lean` passed Lean, exit0,32.548s,peak3,285,840KiB. First885lines are unchanged checked restriction infrastructure. The new `PetersenSymmetryDeletion.lean` fragment provides10explicit0→u permutations, finite bijectivity/adjacency checks, symbolic invariance of the exact Petersen function, a composed9→u equivalence, and the inverse-renaming/update identity. `ResidualBridgeFragment.txt` uses `Restrict.restrict_core` to turn any10-input residual computing F(update x u false) into a9-input circuit computing F(Fin.lastCases false y), preserving FanInTwo and not increasing nonNotCount. Its nonconstancy condition is proved with the all-false/all-true9-input assignments.

Parent/proof_strategy notified immediately. This bridge combines with the newly checked two-drop theorem and L6581 nine-input15 floor to target a17 non-NOT gate floor. It does not by itself settle L-meta-2592. Full success log/resource record are preserved next to source. Independent review requested from status_review.

## Replan: strengthen to17 non-NOT gates

- Read-only refresh found existing checked L_meta_6581 already proves16 non-NOTs for Petersen, so the16 endpoint is not new. Its internal nineFloor establishes15 for ordinary vertex9 deletion, not an extra-input function; independent truth-table/bit-order audit confirmed this.
- New PetersenTwoDropChecked proves deletion of some vertex saves at least2 non-NOT gates. ResidualRenaming now provides the exact9-input interface without increasing the count. Their combination with nineFloor15 should give17; final assembly is compiling. Do not claim17 until the combined file passes.
- This would exclude3+NOT at total size<=19, leaving1 and2NOT. The posted L-meta-2592 theorem is still not proved.
- Full1024-row SAT1200s run returned UNKNOWN; stronger<=3NOT full-row run began after14:37 renewal and remains bounded.

## status_review: approved first-binary/two-drop/residual artifacts 2026-11-25T14:40:26.359895+00:00

APPROVE partial preservation only. PetersenTwoDropChecked.lean SHA25654a84ce89e4c2952f2e3a5e225b52336123f4f3a28fccddec381e39b6837ecbb, FirstBinary.lean e49c6aea565a82d258c94c24b00c93ac4210abe1e3e780cad99e8404a6979096, ResidualRenaming.lean edc2ed33a351e3b4b78dbf1cfc119cbbe3e51759b7ea15c94a64310cf93ff505, PetersenSymmetryDeletion.lean8470aca4b0fbb7c94264acd396cafcab7713d221711cdf8ff35fa3bf34fe6a0f.

FirstBinary extends the reviewed SignedFirst proof: a minimal clean circuit computing a nonconstant nonliteral target must contain a binary gate; its earliest binary gate follows unaryNOTs and reads signed distinct original variables. Output range is proved, not assumed. PetersenTwoDropChecked:2086 then applies this to exact Petersen, chooses a cofactor sensitivity witness where the other input controls the first binary output, and applies reviewed restrict_two_drop. Final conclusion assumes only FanInTwo C and exact computation: some u=false cofactor circuitD has nonNOT(D)+2≤nonNOT(C). Budget-preserving least normalization and both copies of nonNotCount agree definitionally; no minimum-size hypothesis escapes the proof.

ResidualRenaming:1018 converts that10-input residual to exact Fin9 vertex9 deletion using a Petersen automorphism, then generic restrict_core. The statement preserves FanInTwo and nonNOT(E)≤nonNOT(D). Its first885 lines exactly equal TwoDropChecked. Independently checked all10 permutation rows as bijections/graph automorphisms, all1000 adjacency pairs, and all5120 assignments for the residual9→u identity. The graph is the same vertex9-deleted graph used by L6581 nineFloor15.

Raw forbidden-token scans clean in all4. Repo import/plain guard checkImports passes all theorem-bearing artifacts. SymmetryDeletion is lemma-only, so its sole refusal is expected: file holds no theorem. Its permitted synthInstance.maxSize option is local. Some artifact namespaces Pilot110* must be renamed inside final named module; these are preserved source partials only. No final L2592 theorem asserted and no PR acceptance implied.

## status_review: Floor17 source audit 2026-11-25T14:46:54.816353+00:00

APPROVE stable Floor17.lean for preservation contingent on its full kernel compile exit0. SHA2566ee36ba9225cd8cd533ebc13eaa88b4898fc4a155da248dd417a41fe6e0abfbe,361651bytes,6413lines. First3987 lines exactly match acceptedL6581 with namespace rename only. Entire reviewed PetersenTwoDropChecked body, PetersenSymmetryDeletion body, and residual namespace occur byte-exactly. New nine_binary_floor:3989 applies raw_signed then orbitAllInputs and rootSImpossible, correctly deriving15nonNOT for ordinary9input circuits. New finalcomposition:6380 derives17nonNOT for arbitrary Petersen10; predicateconversion is checked per allowedop, countpartition yields atMostTwoNot forsize≤19, and threeNot_impossible rejects≥3NOT. No extra global hypothesis is smuggled in. Import/plain guards and forbidden scans pass. ArtifactPilot110 namespaces must be renamed for named-file integration. This does not prove L2592 until1/2NOT cases close.

Follow-up bounded nine-input search: no checked size16/oneNOT exclusion or ≥17 totalgate bound found among712 Petersen checked finals. L1001 has explicit16gate allAND/OR C0 atline8 for exact vertex9 deletion, so monotone16 is attained; L8957 excludes monotone≤15. L8959 excludes circuits withanyNOT onlyat≤15, and8035/8037/8039/8367 also stopat15. No located theorem establishes that16gate oneNOT circuits are impossible. Search inventory in scratch nine-input-sixteen-candidates.json; appearances ofinteger16 insideedge encodings were distinguished fromgatebound16.

2026-11-25T14:48:10.205732+00:00: counterexample agent paused on rootHTTP410 instruction. All checked sources/logs already in results/orch/lemmas/counterexample. Newly preserved incomparable-orbits.json and RemainingCasesNotes.txt contain the5orbit finite classification and honest remaining-case obstacles. No active processes and no desk calls.
