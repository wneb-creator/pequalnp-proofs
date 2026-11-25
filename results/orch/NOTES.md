# L-meta-2592 orchestrator notes

Only the root agent contacts the desk or changes git state. Agents use assigned scratch files in results/orch/lemmas and record findings here.

Goal: no fan-in-two circuit of at most 19 gates containing a NOT computes the Petersen graph edge function. Exact statement: /tmp/oec/pequalnp-pilot-97/statement.txt. Allowed project modules: PEqualNP.Defs. There are already three live reductions; focus on a proof or counterexample.


## Review audit 2026-11-25T13:49:12.523782+00:00

All three reductions have one premise accepted: binaryFloor = L_meta_4725; normalize = L_meta_7389; cutLast = L_meta_8295. The other premise in each remains the substantive lower bound. See lemmas/notes-review.md for candidate reusable results and definition edge cases.

Toolchain ready: use PATH=/tmp/oec/pequalnp-pilot-97/toolchain/lean-4.36.0-linux/bin:$PATH. Cache get passed; all 9117 files decompressed. Full log /tmp/oec/pequalnp-pilot-97/toolchain/cache-get.log.

2026-11-25T13:51:29.976234+00:00: library route found accepted full Petersen non-NOT count floor15 (L4725/L6194), full Petersen-minus-vertex size floor16 (L4033). Thus candidates have1..4 NOTs, and a4-gate elimination suffices. Full findings: lemmas/notes-library.md.

2026-11-25T13:51:48.386765+00:00 Counterexample route: Counterexample-search strategy (in progress):
- Verified Petersen graph has 76 independent sets and independence number4.
- Generated40 standard20-gate monotone circuits from maximum independent sets, assigned remaining edges to6-star cover.
- Implemented C++ full1024-row bitset stochastic19-gate search. Best so far5 errors (not a witness).
- Toolchain Cadical now available. 19-gate synthesis with1..4 NOT gates and30 critical inputs is SAT in2s; decoded model fails410 other inputs. Boundary tests alone are insufficient with NOT.
- CEGIS now adds zero, all-ones, singleton and co-singleton inputs, then bad rows.
- Exact-one-NOT 30-row SAT is running separately. All programs/logs in /tmp/oec/pequalnp-pilot-97/counterexample.


## Checked partial 2026-11-25T13:52:43.574526+00:00

Named L_meta_2592.lean builds (exit 0), 3245 lines. Copied sanitized L_meta_4725 binary floor into L_meta_2592 namespace, all helper theorem keywords renamed lemma, added notCount_le_four and no_five_nots. No exact posted theorem yet. Full build log and validation summary are in results/orch. Root notified for independent review and immediate checkpoint push.

## One-NOT route 2026-11-25T13:54:49.677752+00:00

OneNot.lean compiled: constant replacement under comparison; essential witnesses; kernel-checked15-edge/15-maximal-independent support certificates and essential_graph_witnesses. No gate-count bound yet. Five computational witness-pair symmetry orbits sent to SAT. See lemmas/notes-one-not.md.

## Few-NOT subclass checked 2026-11-25T14:01:47.955345+00:00

FewNot.lean compiled exit0, 4583lines/284541bytes. Proves16+notCount lower bound with free OR0,2 signal, hence any size≤19 circuit beginning OR0,2 has≤2NOTs. Frozen for independent review; full log saved results/orch/fewnot-build.log. Next route generalizes finite signed-firstgate support certificate across8 pair/polarity cases; toolchain agent supplies firstbinary induction bridge, structural agent pair automorphisms.

## Structural / symmetry route

`Structural.lean` proves the two-NOT final-output elimination at circuit level (213 lines; checked cleanly). `Permutation.lean` proves finite Petersen pair canonicalization by an automorphism: every ordered edge maps to (0,1), every distinct ordered nonedge maps to (0,2), and the edge function is invariant. `PermutationRename.lean` proves generic input relabeling for circuits, preserving evaluation after input precomposition, size, FanInTwo, and NOT count. It fixes arbitrary trailing inputs after the original n inputs, so it applies to free extra signal inputs too. All three checked files are frozen while root snapshots them.

## Root re-plan 2026-11-25T14:04:38.931360+00:00

Accepted library search now establishes full Petersen at least16 non-NOT gates (L_meta_6581). Stop four-NOT computational searches. Main proof route: seeded signed first-gate suffix floor16, generic first-binary induction, pair symmetry, and ordinary-circuit extraction should yield at least17 non-NOT gates and reduce remaining goal to exactly1 or2 NOTs. status_audit owns finite seeded certificate, toolchain owns generic bridge, structural_proof owns symmetry/renaming, library_route owns plain extraction/count arithmetic. counterexample_search and one_not_route focus signed-source synthesis for1NOT/18binary and2NOT/17binary. Stop further generic suffix abstractions now that useful pruning lemmas are archived. All full-gap claims remain pending.

## Arbitrary signed-pair floor checked 2026-11-25T14:10:52.895060+00:00

FewNotGeneric.lean checked exit0 with no output. New pair_sixteen handles ANY distinct inputpair and all4 signedgateforms: the remaining Live derivation needs≥16binarygates. Combines36finitecanonicalcertificates, Petersenautomorphisms, rowembedding, and projection_sixteen. ExactFirstBinary pairFloor premise now discharged; pending integration should establish≥17nonNOT universally and ruleout3/4NOT.

## 2026-11-25T14:17:17.649929+00:00 structural non-OR seeded bound
NonOrSeed.lean checked cleanly, 191 lines, SHA256 39fb20563b627597588da2fe64a94f9d29975bfc98357be205343ab6e2a54d11. `pair_seventeen` proves residual Live binary floor17 after any first proper signed binary other than OR. For AND/difference x_i AND (+/-x_j), setting x_i=false makes both retained input and seed constant; if seed absent use global pins-only floor17. Reverse difference swaps input order. Thus any full circuit whose first proper normalized binary is non-OR needs at least18 binary gates. Main unresolved tight candidate has first normalized binary OR. File frozen for root checkpoint/review.

## OR-case audit 2026-11-25T14:20:34.739616+00:00

Global17 and nonOR-firstgate18 routes now have checked components. NormalizedOR remains; it includes physicalOR and NOR. Genericduplicateprojection charge fails already for monotone P4 (finite signed3gate exclusion checked in Python); details in lemmas/notes-review.md. Input-NOT effective-reader bound is being strengthened by structural/library agents.

## One-NOT search/review update 2026-11-25T14:23:50.059760+00:00

Signed-source generator and DeMorgan phase optimizer implemented; known positive/negative smoke tests passed. Five essential witness orbits supplied to SAT. Reviewed Generic residual16 and NonOr residual17 bridge claims independently. See lemmas/notes-one-not.md.

## 2026-11-25T14:24:11.920104+00:00 structural input-NOT reader deletion
ReaderDeletion.lean (215 lines, SHA256 57d15eb715781fbc29b2d81ea31b9819b64844138b4073554bc408aa2aa68192) and ReaderRename.lean (119 lines, SHA256 6314e17d63b79ca529550cc1e9bf2309361d837d3aa0f34ff0b51b02264525ff) both checked with clean Lean output. Extracted only generic R deletion compiler from accepted L5367, strengthening its floor15 premise to accepted L4033 floor16. Conditional on exact h15 (no nine-variable Petersen-minus-vertex circuit size15), every size19 full Petersen circuit starting NOT[i] has at most2 suffix gates effectively reading i or its complement wire10. ReaderRename uses checked automorphisms to cover every i. No NOT-free suffix assumption is needed. Root must copy/cache accepted4033 certificate to discharge h15. Actual exclusion of <=2 readers remains open. Both files frozen for review/checkpoint.

2026-11-25T14:30:35.396335+00:00 one_not_route: CleanReader.lean compiled and frozen: SHA256 d707058e59dd8d32167b369b5afff086b9df6e3237e90b9ea69fd433e0d655fb, 182 lines, 8437 bytes. Generic antitone propagation treats each positive-literal reader paired with its complement as constant (AND/OR and fan-in <=2). Final clean_reader proves both positive input literals i,j have suffix gates that do not also read their own complement wire10/11 in prefix NOT i, NOT j, AND10 11 circuits computing Petersen. Finite singleton/edge witnesses are kernel-decided; only PEqualNP.Defs imported. Build exit0, empty /tmp/oec/pequalnp-pilot-97/clean-reader-build.log. Root independently reviewing; structural agent will combine with reader-count bounds to remove suffix reads of both complement wires.

### status_audit: SAT trust audit and two-NOT prefix swap
2026-11-25T14:32:06.165580+00:00

The pinned bv_decide tactic calls nativeEqTrue and has no kernel-only config; it fails this task's three-axiom allowlist. Full source/size/encoding audit: results/orch/bv-decide-feasibility.txt. Manual packed LRAT.checkW + decide +kernel remains theoretically valid, but the current signed CNF needs its own proved bridge and a measured small certificate. No expensive certificate build was attempted.

TwoNotSwap.lean compiled cleanly,174 lines,7186 bytes,SHA256594c178dbbd4a2a1fe6ca2a7020a6f3d2d3a6645df2cff69a3d4fa8c11a43fd1. Namespace TwoNotSwap: switched_eval/size/fanInTwo swap first input-NOTs using the Fin12 permutation10↔11; second_count_binary proves NOR suffix reader count for input j or complement wire11 is≤1, explicitly conditional on ReaderDeletion h15. No distinctness premise is needed. Frozen for independent review; scratch cache TwoNotSwap.olean.

Root replan 2026-11-25T14:33:46.722722+00:00: Current exact gap remains unproved. All completed Lean components preserved through230ff918. Reader lemmas retain explicit accepted9vertex h15. No new reduction slot (three live reductions at lease), so cannot submit conditional pieces as fourth reduction. Signed17 global bound rules out>=3NOT under19. TwoNOT normalizedfirstOR remains; current physicalNOR subclass has checked onegate compression under unusednegativewire assumptions, now deriving those via cleanreaders and≤2consumers. Independent rawpin nonOR secondgate may be reordered to invoke18binary bound. Do not use genericduplicateprojectioncharge: counterexample already recorded. bv_decide introduces prohibited nativeEqTrue axiom in pinnedLean; do not use it. Completed searches reportUNKNOWN or checked near misses, never fullUNSAT.

## 2026-11-25T14:34:40.097068+00:00 complete NOR-prefix compression
NorCompression.lean (156 lines, SHA256 5d327e7d60d4e8321450a0cc2bbbc0b695a6c514e7a17f1a1be8e8a32d1973ba) and NorReaders.lean (148 lines, SHA256 efa06b67c5ba49af6c1addf1545ee3f398606d7ccc43f11062e1e767ca08db54) compile cleanly. The first gives exact replacement of NOT[i],NOT[j],AND10 11 by OR[i,j],NOT10 when original negative wires are unused, saving exactly1 gate and1 NOT. Combined NorReaders.compressed_one_not proves unused conditions from ReaderRename + TwoNotSwap count≤2 and CleanReader clean-positive witnesses. Therefore any size≤19 Petersen circuit with that prefix, distinct i/j, and AND/OR suffix compresses to equivalent size≤18 circuit with exactly1 NOT. The only external mathematical premise is accepted L4033 h15; no extra usage assumptions remain. Frozen for independent review/checkpoint.
