# L-meta-2448 orchestration notes

Root holds the sole lease for this job. Other leases under the same GitHub handle belong to other pilots and must not be touched.

## Goal

For a graph without triangles or four-cycles, prove that a minimum monotone circuit computing its edge function can have a star profile. The exact posted statement is in the task scratch directory, `gap.json` and `statement.txt`.

## Current findings

- L-meta-1035 is already withdrawn. Its opposite L-meta-1036 was accepted in PR 2095, using five inputs and twenty-one outputs.
- L-meta-2448 has three live reductions. No further reduction slot is available.
- Minimum-circuit existence is checked in L_meta_2666 and L_meta_7069. The named file currently contains an adapted helper proof of this part, without a claimed proof of the posted theorem.
- R_meta_2448_263 proves that a gate owning disjoint edges in a four-cycle-free graph fires on a nonedge pair or singleton among their endpoints. Circuit repair is the unresolved part.
- L_meta_8237 and L_meta_8415 study singleton witnesses and downstream blocking AND gates.

## Assignments

- Root: integration, lease renewal, builds, publication, alternate global argument.
- status_review: independent review and mathematical lower-bound route.
- structural_proof: local circuit exchange/repair argument.
- library_route: library search and adapted minimum-existence helper.
- finite_cases: exact small-case search and counterexample investigation.
- lean_setup: install the missing pinned toolchain and fetch the pinned Mathlib cache.

Strategy-specific notes go in separate Markdown files in this directory to avoid concurrent edits. Candidate Lean fragments go in the scratch strategy directories or the lemmas directory. Only root integrates the final named Lean file after coordinating ownership.

## First strategy review

Existing lower bounds and the one-junk proof do not close the target: they rely on a global assignment of residual edges and, in one critical case, on exclusion of a five-cycle. Earliest/latest bad-gate choices do not supply those hypotheses.

Continue four routes: whole common-singleton component extraction; graph-only guard classification with a separate small pentagon case; explicit context-preserving circuit repairs; exact and heuristic circuit synthesis on interacting-cycle graphs. The theorem remains unproved.

## Conditional one-junk result

`lemmas/OneJunk.lean` proves the cover-size bound for a least exact-two AO circuit in TopForm on a triangle/four-cycle-free graph, assuming exactly one junk AND gate and silence on singleton inputs. This removes the old global bipartition premise for that subcase. It imports checked L_meta_3760 as a prototype dependency, so it cannot be copied into the final gap file without extracting the used helper proofs. It does not address multiple interacting junk gates and does not prove the posted theorem.

## Second strategy review

The at-most-one-junk case now gives the desired star-profile existential conditionally, including zero junk and empty graphs. Multiple dirty gates remain unresolved. A concrete two-junk circuit blocks a fixed-prefix replacement within three added gates; this is not a full counterexample because the whole OR prefix can be rebuilt. Free-OR bounded-AND searches and finite total-gate synthesis support small instances but do not prove a global size bound. A fresh independent full-theorem route and allowed-import dependency extraction are underway.

Recovery phase concluded with a new own assignment L-gct-231 at09:35UTC, after15 nulls. All old proof attempts stopped. Final old-source location is final-partial/L_meta_2448.lean; checked partial only. Shared-neighborhood graph-pair and later-cone arguments in structural.md remain paper arguments, not Lean results.


## L-gct-231 replan at 2026-11-25T10:21:27.007552+00:00

Own lease remains active. Last timer renewal10:16:07UTC expires10:36:07UTC; heartbeat renews every8minutes. Never request another gap or touch another pilot's lease. Whole-job deadline remains approximately13:03UTC.

Named file now506lines, SHA256449df515d9a915699114a3680c21d9de5b4cbcf8e823143374ad52724ff48227. Build05 passes in10s; standard-axiom audit and independent source review pass. Checker05 completes with REJECTED(no-theorem). No full theorem or PR. All committed through8a1cb0d473ccb5302bff9dad9d83c14a296e61d2 and pushed to origin/pnp/pilot-75.

Completed Lean work reduces a hypothetical solution to one of the star/triangle/path coordinate charts and converts the permanent condition to a formal polynomial identity. Original finite-orbit existential decision caused a checker memory fault; explicit216-entry witness table fixes the fault and is independently verified.

Dead or scoped strategies: full denseOpenF4 charts hit memory/time limits, with no verdict; all support-only/rowzero/symmetry-stable exclusions remain restricted. Common2D star and block seeds cannot extend, by exact CAS/paper arguments. Numerical best is stationary at nonzero residual and is not a witness. Hidden connected linear stabilizer is scalar, so that Borel-degeneration approach is unavailable. None of these proves the full negation.

Priorities for this interval:
- lean_setup and finite_cases: get officialmsolve/neogb sparse exactQQ wrapper through controls, then bounded full charts; no char0 claim from modular unit alone.
- structural_proof: validated exact row-operation certificates, corrected Lean calibration, and built-in grind.ring prototypes. Independent pipeline review has passed; final source must stay within512KiB.
- library_route: robust coefficient extraction bridge for eventual full-chart certificates.
- fresh_main_proof and existing child: common-kernel/cyclic-symmetry constructive or scoped classification; stop numerical repeats of stationary nonroots.
- Root: integrate checked components, review/retain scopes, renew lease, preserve results by early commits/pushes. Do not submit incomplete file as proof.

All research archives are under results/gct231; current frozen manifests include finite82files, fresh-completed22files, path14files, coordinate-pairs5files. Eight distinct subagents total.


## L-gct-231 replan 2026-11-25T10:51:04.724353+00:00

Named partial624lines builds and audits successfully; checker06 rejects no-theorem. Compact neogb rowzero certificate46lines is checked, standardaxioms only. Fullstar nativeALL-pairsF1009 completed moredegree6 reductions but timedout600s withoutbasis. Active newstrategies: nativefullstarF1009pairs32/2threads600s6GiB and distinctdirect-C4tracedQQpairs32/1thread600s4GiB. Keep exactQQ/Lean requirement; modularunit alone isnotproof. A proposed diagonalrank1-pencil impossibility was disproved by a concrete2Dfamily; do notuse diagonal-injectivityshortcut. Everyknown3Dextension remainsexcluded onlywithin explicitlyscopedfamilies. Lastmanualrenewal10:48:46UTC expiry11:08:46UTC; timer renews every8minutes. Deadline13:03UTC. Eightdistinctsubagents.

## L-gct-231 replan at 2026-11-25T11:11:45.479992+00:00

All 31 individual full-star coefficient lemmas now compile (916 lines, 73,248 bytes, source d7bf606d..., 84.875s, 4,051,760 KiB). Independent mapping, source-delta and prefix reviews pass. Checkpoint f40c484d... preserves them. The named file is still the 624-line partial; checker06 says REJECTED (no-theorem). Root is integrating the interface with the existing canonical normalization, using narrower imports where possible.

The C4 quadratic+cubic system returns unit basis over F1009 (16 equations, 12 variables, 17.229s). This is not a characteristic-zero proof. Two rational runs are active: original compact trace (900s/4GiB/2GiB raw trace) and independently reviewed primitive-row trace (600s/4GiB/512MiB). Both must produce an exact replayed certificate before any Lean contradiction claim. Primitive normalization and dependency slicing have independent source/control reviews.

The full-star batch32 modular search timed out after 600s/126 rounds without a basis. Finite is developing reviewed per-round snapshots and grouped variable ordering before a longer run. Pure-pencil and first-variation-only subsystems have exact solutions; do not retry them as unit ideals. A proposed rank-one diagonal restriction for zero-edge pencils now has robust numerical rank-two counterexamples awaiting exact reconstruction; do not assume it.

The C4 hand route has independently checked whole-e=0 and all nine product-zero pencil branches. Nonzero-product pencils remain. These are scoped algebraic reductions, not a full result. Fresh and its reviewer pursue the remaining small branches while structural handles rational certificates. Library audits the 31 checked lemmas and prepares the small block-determinant square identity.

Last manual renewal at 11:08:17 UTC expires 11:28:17 UTC; heartbeat renews every eight minutes and currently has no error flag. Whole-job target deadline remains about 13:03 UTC. Eight distinct subagents have been used. No proof/refutation PR exists.

## L-gct-231 replan at 2026-11-25T11:35:50.798426+00:00

The named file is now1528lines/101116bytes, SHA42c23a47.... Lake build07 passed (module53s), audit07 checked35 standard-axiom sets, and checker07 returned REJECTED(no-theorem). There is still no theorem named PEqualNP.Outside.L_gct_231. Checkpoint1b74cb35 preserves the named integration plus new checked components.

Checked C4 components now include the full binary-linear-factor matching theorem, a complete common-isotropic-plane determinant-square theorem (including adapted-basis existence), and the first exact two-variable open-case contradiction. The compressed nonzero scalar contradiction also compiles and has independent exact source review, awaiting immediate archive/push. Combined case1 wrappers had one stale h2 proof bullet; this was caught independently and is being fixed before publication. The other two augmented open-case systems are unit overF1009 after adding the omitted square condition; exactQQ traces are pending. The C4 boundary and zero-product classifications remain reviewed mathematics rather than complete Lean coverage.

Fresh is formalizing the C4 coordinate/permanent-coefficient interface. Library completed the generic determinant bridge and a nonsquare coefficient criterion. Structural owns exact scalar certificates and wrappers. Finite owns the full-star computational search and checkpoint tooling. Global and c3 provide independent reviews.

The grouped full-star search restarted at11:31:53UTC for1800s,4GiB,1thread,pairs32. Export-only checkpoints now retain all original generators plus at most1million derived terms, with explicit omission counts; the active solver basis is unchanged. The first useful snapshot is preserved compressed as a partialF1009 restart set, never a basis or characteristic-zero proof. Previous snapshot-cap failure remains UNKNOWN with full logs.

The desk now requests renewals every5minutes. Root changed its heartbeat from8 to4minutes; active heartbeat session1622. Last manual renewal37 at11:34:28UTC expires11:54:28UTC. Only our L-gct-231 lease is held/renewed. Whole-job target deadline remains about13:03UTC. Eight distinct subagents; no proof/refutation PR exists. Latest complete GitHub title searches found no231/232 PRs.

12:03 UTC replan: preserve checked C4 scalar cases0/1 and all geometric interfaces; independently audit the new exact resultant classifications for cases2/3, then compile small endpoint consequences. Build one combined partial file. Full-star finite-field searches approach their resource caps without verdict; freeze latest restart subsets before deciding next steps. Triangle12-variable necessary system has a reviewed F1009 unit result, but requires exact characteristic-zero certification. No proof or refutation of the posted statement exists yet. Deadline remains about13:03UTC.

- 2026-11-25T12:28:15.892343+00:00: Replan: baseline named2593 remains compiled/pushed; forward/reverse C4 necessity and slopeboundary are now checked. Fix multi-block assembly before next namedbuild. Modular univariate resultant transfer may replace huge rational Bezout certificates while rigorously preserving characteristiczero, with leadingdegrees checked. Star-pencil classification has compiled; its audit and tiny no-extension identity remain. Generictriangle QQ grows too costly; final600s run will stop atcap. Fullstar31 system remains the global unresolved bottleneck. Preserve every checked result; no full theorem/PR.
