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
