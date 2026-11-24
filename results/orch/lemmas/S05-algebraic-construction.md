# S05 algebraic construction

Owner: former S03 agent, reassigned by main. Scratch: `/tmp/oec/pequalnp-pilot-18/orch/S05/`. No21-gate witness found; no global lower bound is claimed.

The completed cofactor/star recursion cannot beat22: every AND it constructs computes a target subgraph function and is clean, so the existing clean22 theorem applies to the entire family. This is a structural obstruction, not a conclusion from beam failure. The0.83s control completed911 induced nonisolated cores and generated68945 expression nodes, reproducing22-gate exact circuits checked on all2048 inputs. This family is stopped per main.

A separate delayed-factor probe used U_S = OR(S) OR F(G[V minus S]). Every factor is above the target; it rejects a maximal independent input I exactly when S is disjoint from I. Choosing factors whose rejection sets cover all24 negatives is therefore sufficient, with positive edge rows automatic. The bounded probe considered2777 factor implementations and455428 extensions in2.54s, retaining80 states; no21 witness. This is not exhaustive. Main has now directed concentration on the three-clause contributor route below.

The active route constructs clean contributors (OR A) AND (OR B) AND (OR C), with genuinely dirty intermediate ANDs, and OR-combines them to cover the16 target edges. Each contributor is checked on all24 maximal independent inputs. Ordinary star contributors remain available. Gates and common clauses/pairs are structurally shared.

First bounded pass:231 linear clauses of size1..3;1737703 triple combinations examined after preliminary pruning;2635 valid triples yield7974 total contributor implementations including69 stars. The contributor enumeration takes0.37s; the shared-subexpression edge-cover beam takes16.49s/40125168 extensions. It reaches15 of16 edges within21 gates but finds no full21 circuit. Beam retention1000, so this is not exhaustion.

A concrete cost obstruction helps focus the next pass: there are223 distinct positive edge masks among the dirty triple contributors. For each mask H, its cheapest enumerated contributor costs at least one more than the clean graph cost |E(H)|+vertex_cover(H)-1. Of these masks173 have overhead1 and50 have overhead3. Thus isolated three-clause replacement gives no saving in this pool; any successful construction must gain from sharing across contributors or further distributive factoring. Complete mask/cover/cost data: `triple-cost-analysis.json`.

Next bounded scalar step: factor common linear clauses across contributor sums, using A*B*C OR A*D*E = A*(B*C OR D*E), and allow shared dirty pairs. This can save a gate beyond counting a shared input once, so the initial union-of-DAG-cost beam can miss it. No solver or Lean run is used. Any complete candidate will be re-evaluated on all2048 inputs and passed immediately to the reviewed Lean emitter.

Artifacts: `cofactor-first.json`, `upper-factors-first.json`, `triples-first.json`, corresponding full stdout/stderr, `triple-cost-analysis.json`; generating sources `cofactor_dp.py`, `three_clause.py`. These are scalar construction evidence only. The three-clause search simplifies intermediate expressions using40row signatures; such transformations preserve that abstraction, not necessarily all intermediate functions. Any final exact target is still independently checked on all2048inputs.

## Dirty22 construction and annealer seed handoff 2026-11-24T04:06:25.413242+00:00

READY_FOR_MAIN_REVIEW. This is a 22-gate positive control, not a <=21 witness.

Source: shared-factor-compact-complete.json, SHA256 0cd2e6eaa92e2a5cd95d1bd20728ad9157e80b9e88a728ad7033f8af420c1299.
Pack: dirty22-seed-pack/seeds.txt, SHA256 7545d43b161bb5d1fab2cbf3e517c56a40dab5e8e26bdaff4bc4649760dbfe0a.
Primary manifest: dirty22-seed-handoff.json, SHA256 2b3503280a6413d8a2a1a79404559f8966380388e27e63a3d16a0c8a0279f9c7.

The existing reviewed stochastic_tools.py prepare command created seeds.txt and seeds.json unchanged. Four schedules: original, reverse-ready, earliest-junk, latest-junk. Sole dirty AND indices are respectively 14,13,4,18. Each has 22 live gates, output34, no constant reads. Original inputs0..10 remain unchanged; original gate wire11+g becomes13+new_index(g). The added virtual wires11 and12 are false and true. Gate operands are sorted after remapping.

All 2048 inputs pass for the original, each translated/reordered seed, and each packed roundtrip. All 180224 intermediate-value comparisons preserve the old/new gate map. Five runs of the unchanged independent raw validator (original plus four schedules) return expected exit2, EXACT_BUT_TOO_LARGE, size22 after normalization. Wrong-offset and false-output controls reject. Full stdout/stderr and command/result files are in dirty22-controls; all scalar diagnostics are in checks.json and dirty22-build.stdout/stderr. Tool sources and binary hashes are unchanged and bound by the primary manifest.

No engine, search worker, Lean build, solver, checker, or lease operation launched. The optional engine --self-test command is recorded as NOT_RUN in dirty22-controls/engine-self-test-not-run.json, per latest user direction. Main review and resource scheduling precede any launch. Existing solver/checker processes are untouched.

Reproduction source: prepare_dirty22_seeds.py. It refuses existing output directories and binds the source and all reviewed tools by SHA256. It writes only under orch/S05. In a fresh copied workspace, run python3 -B prepare_dirty22_seeds.py with this source and pinned tools at the documented paths. It performs no search.

Full delivery manifest: `orch/S05/dirty22-delivery-manifest.json`, SHA256 `74aa51ec266ec31be63503b4a68c73982383ccb4ec4249e8be59476f992ac678`.

## Dirty22 kernel certificate 2026-11-24T04:09:03.626074+00:00

The exact dirty22 source JSON `0cd2e6eaa92e2a5cd95d1bd20728ad9157e80b9e88a728ad7033f8af420c1299` now has a Lean-checked bound22 certificate. The unchanged fixed emitter generated `orch/S03/Dirty22Control.lean`, SHA `9a7014c902546881f3653782c4dbcc62213e91a6fe67f7faa6e7645029423969`, using existing helpers. Build PASS exit0/17.69s, both logs empty. Separate four-lemma axiom audit PASS exit0/6.83s; monotonicity uses propext/Quot.sound, size uses none, boundary and final certificate use only propext/Classical.choice/Quot.sound. Full source/hash/log handoff `orch/S03/dirty22-certificate-handoff.json`, SHA `361cd610b831905c5ef95185878101faf2a3d11d2a6f54d5a954df9a05b10b61`. Exact existential statement is retained in `dirty22-exact-statement.txt`.

Both runs held the exclusive Lean lock, used pinned Lean4.36.0 and -M4000/-j1, and followed main's04:06:32 lease renewal. The named2069 source remains unchanged. These Outside-import and axiom-audit files are scratch harnesses only; do not copy them directly into the final named module. This proves the bound22 control, not the posted bound21. The four-order offset13 seed pack was independently accepted by main on all8192 decoded inputs; main alone launched the coordinated290s annealer.

## Dirty22 local repair handoff 2026-11-24T04:16:59.224384+00:00

All44 left/right gate deletions of the exact0cd2e6 dirty22 source are retained under dirty22-deletions. Each seed has21 gate slots, augmented wire offset13, sorted fanins and valid earlier-wire references. Full2048 outputs and every retained intermediate wire were compared against direct original-circuit deletion/alias semantics:90112 input checks and1892352 intermediate comparisons. The unchanged reviewed local helper857f7082 independently supplied all full/boundary errors, liveness and gate-flip influences. The original source, engine and helper are untouched.

Prioritize three different missing edges, with3- and5-hole variants listed in dirty22-repair-shortlist.json (six input proposals, not a launched portfolio):

| Seed | Only missing edge | Full errors | 3 holes | 5 holes |
|---|---|---:|---|---|
| d08-right | (6,10) | 7 | 5,12,13 | 5,6,7,12,13 |
| d01-left | (7,9) | 8 | 5,6,13 | 1,5,6,13,14 |
| d05-right | (4,10) | 8 | 0,7,13 | 0,5,6,7,13 |

All three have21 live gates, zero false positives, and sole dirty AND13 (mapped from original14). These are incomplete candidates. Each analysis JSON also retains two recommended windows at each size3,4,5. Ranking considers proximity to the deletion reader and original junk gate, error-flip influence, and a necessary row-wise relaxation: each boundary target must remain attainable when the hole outputs are freely chosen per row. That relaxation does not establish the existence of actual shared gate functions.

S02 intake: load seed JSON and pass sorted free_gates to the unchanged helper.repair(base,data,holes). This keeps every outside gate and output selector fixed, with exact target40rows and no clean-prefix/junk assumptions. S02 may separately use its reviewed free-output wrapper. S05 generated no CNF and launched no solver. Main owns review/admission/launch.

The earlier exact algebraic probe found no gate saving:671492 cost-filtered zero-to-two-operation replacements across all22 roots (1.16s), plus1449285 three-operation tree candidates around roots14/15/16/20/21 (0.90s). These are bounded local enumerations, not global lower bounds. Every original gate has fanoutone. The five maximal linear clauses intersect pairwise in at most one variable, so OR reassociation alone cannot create cross-clause sharing. New savings require nonlinear or simultaneous changes.

Handoff SHA256 `5f20cd2772d29e1fcef44a9329968b2df7893cb435af7544aae70f43087313a3`; immutable family manifest SHA256 `0617f68492c4d9fc735d734f2afa00af65a6f03ca4240dca16af8573cde3b784`.

## Positive dirty seed shapes 2026-11-24T04:22:24.124653+00:00

Exactly14 of the44 left/right deletions have zero false negatives. All14 were independently classified on all2048 inputs by the minimal extra accepted independent sets. Thirteen are F OR OR(S) for a nonempty set of inputs S. Only d16-right has nonlinear extra terms:

    F OR x5 OR ((x0 OR x7) AND (x1 OR x4)).

It has14 bad maximal-independent rows and51 full false positives. Its original20live-gate realization simplifies to18live gates by absorption: the explicit x5 disjunct makes the x2*x5 term redundant. In the unchanged21-slot offset13 schedule, rewrite gate17 from OR(24,29) to OR(22,24). Dead slots become4,10,16; sole LIVE junkAND14. All2048 outputs remain identical. Source d16-right-absorbed18.json SHA f54738c35881deea8ba24b6f15cc533042e7db6342e6c31e481528868bc0b8cd. This is not an exact target circuit and has no Lean target certificate.

Best scalar singleton shapes: d13-left=F OR x10,18live/5boundaryFP/19fullFP, livejunk13; d14-left=F OR x8,19live/5boundaryFP/19fullFP, livejunk15; d14-right=F OR x9,19live/5boundaryFP/22fullFP, livejunk15. These retain the singleton-error pattern despite their dirty implementations. d16-left=F OR x8 OR x9 has15live gates and NO LIVE junk gate; its declared junk14 is dead. The new analysis distinguishes live from dead junk explicitly.

Each source analysis contains unchanged reviewed S02 suppression impacts, exact source/hash/error shape, and two recommended3/4/5-hole windows near junk gates. For the nonlinear18live source:3holes[10,14,15] or[4,14,15];4holes[4,10,14,15];5holes[1,4,10,14,15] or[2,4,10,14,15]. Dead slots are only retained in ranked windows when a later free gate could reconnect them. The row-wise oracle is a necessary relaxation, not an existence proof; all14 negative error rows can be touched, but8 positive edge rows are also at risk. These are analysis inputs only; no CNF or worker launched. S02 can use the reviewed local/free-output repair helper after main review.

A bounded full-context algebraic completion over existing signals considered299638 cost-filtered zero-to-three-new-operation trees in0.11s. Four exact completions exist, all22gates. No21 was found. One equivalent exact22 network, dirty22-factored-corrector.json, is separately scalar-checked on all2048inputs:

    F = Rprime OR ((x8 OR x9 OR x2*x5) AND (x5 OR A*B))
    A = x0 OR x7 OR x8
    B = x1 OR x4 OR x9
    Rprime = x1*x4 OR x3*(x6 OR x7) OR x6*x7 OR x10*(x0 OR x2 OR x4 OR x6).

The identity moves x2*x5 into the corrected nonlinear branch because x2*x5 implies x5. This changes the algebraic repair neighborhood, not the gate bound. It is a new scalar22 control, not a newly compiled Lean fragment. The earlier fixed-clause OR overlap obstruction does not rule out such whole-context absorption/distribution.

Handoff SHA256 `9619c1e0aef73ddf8dd9ab512c84864fe374dde788741c2a93eb1d51c969a480`.

## x10-factor check 2026-11-24T04:27:25.451924+00:00

Let A=x8 OR x9, B=x0 OR x7 OR x8, C=x1 OR x4 OR x9. The original circuit is F=R OR A*(x5 OR B*C), with R containing x10*(x0 OR x2 OR x4 OR x6).

The proposed new term x10*B*C adds exactly one minimal independent false-positive input {1,7,10}; its only independent supersets are1154 and1186 ({1,5,7,10}). However x10*B*C accepts NEITHER edge input {0,10} nor {4,10}. C is false on the first and B is false on the second. Therefore dropping x0/x4 from the x10 star loses two required edges. An added AND guard cannot recover any missing positive input.

All formulas below were explicitly built with binary gates/common-subexpression sharing and independently scalar checked on2048 inputs:

| Variant | Gates | Boundary FN/FP | Full FN/FP |
|---|---:|---:|---:|
| Replace only ABC by(A+10)BC; retain5A; reduce10star to10(2+6) |22|2/1|15/2|
| Compact(A+10)(5+BC), same reducedstar |21|2/2|10/7|
| Expanded replacement while retaining original10star |24|0/1|0/2|
| Retained-star expression AND sharedguard(R+A) |26|0/0|0/0|
| Factor the guarded expression algebraically |22|0/0|0/0|

The compact21 variant additionally accepts the nonedge {5,10}; maximal-independent errors1066/1186, missing edges(0,10)/(4,10), livejunk gates17/19. Its original-model JSON is ten-factor-analysis/compact_drop_04.json; a separately all2048-crosschecked offset13 form is ten-factor-compact21-augmented.json. This is a near-candidate only, not a witness or certified partial target proof. No repair CNF/solver is generated.

There is no guard consisting of one existing retained-network wire that preserves all target edges and removes both false inputs. Enumerating all one-operation AND/OR guards over the retained-network wires finds two syntactic ORs, both computing R OR A. This guard is valid, but distributivity gives

    (R + 5*A + (A+10)*B*C)*(R+A) = R + A*(5+B*C),

which is exactly the original22 construction. A purely linear guard false at1186 must use the unique cover {0,2,3,4,6,8,9}. These statements concern this expression and these finite guard choices; they do not rule out broader simultaneous nonlinear rewrites.

Full diagnostics, all five circuit JSONs, source, complete false-input lists, and hash manifest are retained in ten-factor-analysis and its outer stdout/stderr. No Lean or heavy worker was launched.

Handoff SHA256 `4909a31d13374760c5ac71b27c1d5014fcdf1672b1c27c77ba1bb37b99289d7a`.

## Separate direct21 restart engine 2026-11-24T04:33:33.802267+00:00

The original reviewed engine supports only exact22 seeds: COVER_ANNEAL version1, then a random gate deletion at each fresh restart. Its code/help were inspected; old-binary rejection of the direct21 pack is retained as a finite control. There is no existing21-seed path.

This separate version retains the original exact22 path and adds an explicitly tagged COVER_ANNEAL_DIRECT21 version1 path. Each entry is:

    21 OUTPUT FULL_FALSE_NEGATIVES FULL_FALSE_POSITIVES TRUTH_FNV1A64
    OP A B   (21 gate rows)

Inputs are0..10; FALSE11/TRUE12; gates13..33. OP0=OR/1=AND. The loader checks count1..10000,21gate entries, output bounds, canonical0<=A<=B<13+gate, then computes all2048 output bits independently. Full FN/FP counts and the FNV-1a64 fingerprint must match. The fingerprint is a diagnostic checksum, not cryptographic authentication; the unchanged wrapper binds all pack bytes with SHA256. Extra/truncated content is rejected. Inexact seeds are only initial search states and can never be accepted as target witnesses from this metadata.

The direct fresh-start function copies a21-slot circuit exactly, without deleting a gate. Both initial selection and ordinary restarts use it. The old25-percent best-perturbation restart path remains unchanged. Old baseline deletion, score, mutation, annealing, snapshots, final2048 candidate check, exit/status semantics, bounds and signal handling are unchanged. A source comparison verifies those blocks exactly, except the fresh-start call replacement. Legacy behavior uses the old random calls in their original order.

Four topological orders of the positive18live nonlinear state are packed. Their function is F OR x5 OR ((x0 OR x7) AND (x1 OR x4));0fullFN/51fullFP,0boundaryFN/14boundaryFP. Every21slot value (including dead slots) and output matches the original on all2048 inputs. Original source SHA f54738c35881deea8ba24b6f15cc533042e7db6342e6c31e481528868bc0b8cd. This is not an exact21 witness.

Build: g++ -std=c++17 -O3 -Wall -Wextra -Wpedantic, exit0/1.87s, no warnings; source/binary/command/compiler-version/log hashes in build-result.json. Independent controls use only --self-test and fake engines, not a production search:

- Four direct seeds:128 exact fresh-start controls,512 single-mutation scalar/boundary-vector controls; full scalar2048 evaluation per control.
- Existing exact22 pack:440 deletion-renumbering and440 mutation controls pass unchanged.
- Fifteen malformed direct packs reject (version/count/header/output/op/negative/forward/noncanonical wires/error counts/truth fingerprint/truncation/trailing data).
- Old engine rejects new direct format before search.
- The unchanged wrapper invokes the pinned raw validator for a fake candidate carrying the actual inexact direct seed; validation rejects and wrapper status is ERROR.
- The unchanged wrapper rejects a tampered pack before starting a child.

Existing engine/source/wrapper/raw-validator/oldpack hashes were verified unchanged before and after controls. Full logs and commands are under controls/. No exact21 positive end-to-end fixture is available. Candidate acceptance still requires the unchanged wrapper's pinned independent raw validator, then a Lean proof. Never launch this binary directly for production.

proposed-command.json records an UNEXECUTED60s/weight16 example through the original wrapper. Main/S08 review and main resource admission precede any launch. S05 did no production search, SAT, Lean, desk, credential, git or network action. The earlier authorized60CPU algebra enumeration was superseded and NOT launched.

Reproduction sources: prepare_direct21_engine.py in the parent directory derives the new source from the pinned old source, emits exact engine.diff, and creates the pack; test_direct21_controls.py runs finite controls in a fresh directory. Both refuse to overwrite prior artifacts. Parent source, nonlinear input, reviewed wrapper/raw-validator copies and binaries are preserved for review; existing files outside this new directory are untouched.

Handoff SHA256 `eb264a58371c14e63fc679545dc270b515973506da017ef82ee502b036ee17fa`.

## Triangle589 and direct21 pilot analysis 2026-11-24T04:40:59.583681+00:00

The six-input triangle-plus-leaves template `(a OR b OR f) AND (c OR ((a OR e) AND (b OR d)))` accepts the triangle/pendant edges plus the leaf triple d*e*f. Applying it to triangle {5,8,9}, with grouped external leaves2, (1 OR4), (0 OR7), and retaining the other graph edges gives a21-gate circuit. Its exact function on all2048inputs is

    F OR (x2 AND (x0 OR x7) AND (x1 OR x4)).

This is INEXACT: ten false positives, six maximal-independent false positives, no false negatives. Minimal extras are {0,1,2}, {0,2,4}, {1,2,7}, {2,4,7}; no singleton or pair is falsely accepted. Original source triangle589-positive21.json SHA2d99849c19f69c76b232e4d55ce487638721291dac4faea3e82dc3274414bfbe has21live gates and junkANDs6/8. All16positiveedges were checked explicitly. Three choices of center and four topological schedules plus the original topology give16direct21 seeds. The new pack is separate from the reviewed original engine and its nonlinear18 pack. Its32768 decoded input checks and688128 intermediate comparisons pass; the exact reviewed engine finite self-test passes512fresh starts and2048mutations. No production search or Lean build was run. Full hash handoff triangle589-handoff.json SHA909978e953b3c6a2b775bb62e7cf7fbd314c5f5709d295f21603396880cfdd0d.

Completed pilot134224 was independently checked in all six snapshots,12288inputs. Final/best4 computes exactly F ORx8 ORx9, has41fullfalsepositives,10boundaryfalsepositives,17syntacticallylive gates, no livejunk, dead slots0/3/4/7. Best1 is F ORx5 ORx8, best2 F ORx5 ORx9, best3 F ORx8 ORx9. Onlybest0 retains the initial nonlinear function, so no improved nonlinear repair source emerged. Error counts reported by the engine are boundary counts, not full-input counts. Full error masks, minimum extras, source copies and live/dead junk analysis are in direct21-134224-analysis/report.json SHA0e1d97a15e6cddbe35800ed2847106ac0b90c407be985391074aac0a43b6d767.

Reviewed engine/control preservation is ready: direct21-preservation-v1.tar.gz SHA70858a65855a12f1345980afbfd2c490bec7963fcf3c1c3aa58847108b441323,46691bytes/119regularmembers. One ELF binary is deliberately omitted with its exact hash retained; all source/build recipes/full controls and logs remain. manifest SHA6c838e8d549437e34a6bac8d2b6ac8ebea1035469a4a963d2b79cd45d501353b. Original engine/pack bytes remain unchanged. Main owns archive review/copy/push and production admission.

## Guarded-component scalar family 2026-11-24T04:44:58.414296+00:00

Enumerated all546619 literal expressions D=OR(A) AND(xc OR(OR(B)AND OR(C))) with nonempty A contained in N(c), arbitrary nonempty B/C, nonnested B/C, and D false on every independent input. The algebra cost counts the three linear OR trees independently.173995 A/B pairs yield274 covered-edge masks; completing the remaining target edges by optimal clean stars has minimum22,0.413seconds. This includes the previously found dirty22 kind and is a finite construction family, not a general lower bound.

A second complete0.721second pass evaluates81831 ways to reuse whole A/B/C clause signals in residual stars. Selected clauses with the same center are OR-merged; new leaves cost one OR each. After their already-covered edges are removed, residual cost is the remaining-edge count plus a minimum vertex cover after deleting activated centers, plus the activated-star fixed cost.58106 choices improve the separate cost, but minimum remains22. Single-residual-edge reuse is omitted because an ordinary leaf has the same cost and no saving; only entire clause nodes, not arbitrary OR subclauses or nonlinear signals, are considered. The literal costs do not purport to include all distributive simplifications. All full output and scope data are in guarded-component-handoff.json SHA421e70e8867e085ddab761c6da9cd66c76bbc2916297f1a1621832637913ec94.

## Triangle589 bounded context completion 2026-11-24T04:46:23.942985+00:00

Requested dedicated reuse of complete_positive_context finished:198251 candidates, zero exact-target hits,0.0667s. All32 original wires are available, with at most three fresh binary AND/OR operations and original live-cone union plus fresh-operation count at most21. The enumeration covers zero/one/two-operation trees and balanced/chain three-operation trees, using complete2048-bit truth functions and sound final-operator pruning. This is only the literal cost-filtered family: arbitrary internal rewriting and lower-cost realization of unchanged wire functions are outside scope. No raw validator or Lean run was applicable because no exact candidate appeared. Parent/delta/source/full logs and result are in triangle589-context-handoff.json SHA596bf7a0f09c9833c31cea36d72670a7a46043eb82f04bf4fcfaae3b2537cad0. Script SHAbaee2c77cea507912c29d5b5868d0907c3c1d255dc78f588c65d296f4a8ea9ba. Original emitter, engines, packs and previous completion files remain unchanged.

## Internal contexts and improved annealer seed 2026-11-24T04:49:15.731965+00:00

The original triangle589 source has no exact<=21 replacement found by887158checks over all21 single-root contexts, up to3fresh-operation trees,0.393s. Twelve roots cannot affect all errors at all; nine feasible-context roots were fully enumerated within the literal live-cone budget. Source triangle589_internal_context.py SHA19946c4b1909351f35fa29b336fba9036fd581b68aeea032c332af9f19b3478a. This is a local family only.

Main-launched weight16 pilot134226 saved best3 sourceSHA9a743d5d43f651198f908fd086b3307e036697ee9d9990f5c0edfcce6ff3fe96. Immutable independent scalar analysis confirms F OR[x2*x4*(x0 ORx7)] on all2048inputs. Five fullfalsepositives21/29/85/148/149; threeboundary29/85/149; minimalextras{0,2,4} and{2,4,7}; zero false negatives. All21gateslive, no dead slots, junkAND17/19. This is better than the initial four-extra-triple state but remains INEXACT. Originaloffset11 normalization SHA f3c2bacb85a0ce0e080072ad39b0a695f90affb6f7204880c44acdf496195790 preserves all43008 intermediate values. Fullinfluences and structural repair proposals3/5/7/8/10holes have only necessary row-oracle checks, no feasibility/solver claim. Handoff triangle589-best3-handoff.json SHAa8e23c84e1004ea91411b821d2e28de76d4af39caa644aa387e0a6acd5fb8aac.

## Improved-best3 shared contexts and restart pack

The improved source also has no exact single-root substitution in the tested family:954732 full-truth-table candidates over all21roots,<=3freshoperations,0.503s. Eight coupled root pairs(6,17),(8,17),(9,17),(13,17),(6,19),(8,19),(9,19),(13,19) were then checked with up to3fresh shared nodes. The first root may use at most one operation and the second at most two with reuse, or both can share a new first node. All eight stated families completed in13.295aggregate CPU seconds without a candidate. General3+0trees and other root pairs are outside this scope. Scripts/results/full logs retain exact roots, conditional constraints and source hashes.

A smaller algebraic core is T=14 OR18 OR48 OR25 OR58, with E=5 OR8 available for free inside the core because E is already used in the9-star. A six-operation core would make the whole construction21. Exact formula dynamic programming finds minimum7, after220649 operation pairs,0.045s. Allowing any one additionally shared intermediate computed by a<=3operation formula and a formula remainder with total<=6 also fails:426 intermediates,2087642operation pairs,0.514s. This does not prove a six-gate DAG impossible. The broader three-gate-prefix/small-tail enumeration was proposed but has NOT been run because main filled all CPU slots.

A separate best3-only direct pack now holds eight DISTINCT topological schedules of the immutable source9a743d5d43f651198f908fd086b3307e036697ee9d9990f5c0edfcce6ff3fe96. Pack SHA6c60f7617f1b797fd8408ddbf5f08d94a148c2c49eb66d9821d7f35e68606e9b; metadataSHAc6b4f5b90cfc656f9c1466da3ed5a33dd1e4fe950d073adde5b2f414f034cd66. All16384 decoded inputs and344064 intermediate values pass,0FN5fullFP3boundaryFP,all21gateslive. Exact unchanged engine finite self-test passes256fresh starts and1024mutations in0.266s. Handoff00844934f079b463147a46fc6f42a57a2ec90052b981c262b54f0f0745e5051b. Main independently reviewed and launched134228; S05 launched no production. Both earlier packs remain unchanged.

A portable archive is being prepared with both triangle packs, best3source, all bounded-context code/results/reviews/full self-test logs, and the already reviewed binary-free engine preservation package. It will retain exact original paths in provenance and provide a standalone archive verifier requiring no engine execution. Main alone owns final archive review, repository copying and publication.

Portable archive READY: triangle589-preservation-v1.tar.gz SHA6e927788b52cf15f0769a7cb73d95739ee84cf6e23039d39655bff1b4cef0bdf,123567bytes/249regularmembers. Portable verification passed all49152 packed inputs,1032192 intermediate comparisons and all manifest hashes in0.331s. No engine execution or binaries. Handoff SHAde2516c3c1a6071ec143a8586e6f53e2c9de96eadf767bcac9a3400ab75ae682. The archived report is the historical snapshot immediately before this completion note.

## Postarchive bounded core mathematics 2026-11-24T05:03:26.813571+00:00

A proposed normalform proof shows the five-input target14+18+48+25+58 with E5+8 free requires at least3AND gates, regardless of ORcount. Proof free_E_core_two_AND_obstruction.md SHA031501453a42c1b2460c1a06d734e70b23598b77926bb9e6b460e0af3d41b0c9. Its32input graph checks reproduce5maximalindependent sets, covernumber3, and8as onlydegree>=3vertex. This does not prove6total gates impossible and awaits independent mathematics review. Initialcontrol expected-list ordering error was corrected with fullfailure retained; proof unchanged. Separate free_E_six_gate_reduction.md SHA70fba198ef9932a35b2d19d38facc01f899e478895242c18cfaf217923e82534 explains why a complete3-prefix/3-formula-tail scan would decide6gatecore. That scan remains NOTRUN while4CPUslots are busy. These new files are outside the frozen triangle archive.

## Completed-solver statistics and one different approach

Following main's05:05 request, only completed hitting AAAO-RUP/T2/T3 logs were inspected and copied. Each used the pinned CaDiCaL --unsat preset and spent95.09–95.87percent of process time in unstable search, with no stable phase. They reached2.83–2.91million conflicts and251139–274314 restarts (10.6–11.6 conflicts perrestart), while peakRSS stayed112.79–113.36MiB. They hit the600second wall limit, not the1536MiB memory or512MiB proof cap. This supports changing the search regime before another identical ten-minute attempt; it does not predict satisfiability.

ONE recommendation: rerun the exact reviewed strongest AAAO-RUP input with the same pinned solver's --sat preset, which sets stabilizeonly=true and retains random walks. The preset is a heuristic, not a restriction on the answer: a finite four-clause UNSAT control generated DRAT and passed the unchanged checker through the complete runner. Bound the first real retry to600solver+600checker seconds, oneCPU held through finalization,1536/3072MiB AS,512MiBproof,>=1024MiBfree. Keep full-validation and provenance requirements. A run returns within20minutes including checking, but SAT/UNSAT is not guaranteed; UNKNOWN is not a proof.

New disjoint runner offline_stable_cadical.py SHA64958a6d0ef8eaa1e072547ade244cdb2de156815fca6545b4fcf829d331f7da has exactly three literal changes from reviewedaa5d13: --unsat to --sat, OWN S06 to S05, matching error label. Resource handling, pin/snapshot checks, proof checker, SAT validator, verdicts and cleanup remain byte-identical. Actual-parent preflight passes and creates no production directory. Tiny proof-path control passes in0.142s. Initial outer-control768MiB AS prevented the child's unchanged1536/3072MiB limit setup; its fullfailure was preserved before correcting the outer cap to4096MiB. No runner change was needed. A later inline packaging indentation error also occurred before any writes and is retained separately.

Full snapshots/statistics, pinnedbinaryhelp, source/diff/parent, toyproof/full logs, actual-parent preflight and one UNEXECUTED command are in solver-mode-review. Main/S08 review and main resource admission precede production. No active T4 file was read or changed.

Handoff stable-mode-handoff.json SHAc2a1358bb7f0c1090fb1e36ad6d1916c8525a4148228e9c2a5369c9ee84c1015.

## 134227 compact repairs 2026-11-24T05:13:47.940652+00:00

S05 CANDIDATE134227 BOUNDED REPAIRS: handoff candidate134227-repair-handoff.json SHAd751046916c7b7c6029f02ef7c554176a0bb61720c1e74a103d9a3843eef2e3d, 34fullartifacts. Independent4096outputs+79872intermediatechecks confirm best3 694cbc...=F minusONLYedge25 (24fullFN0FP),20pruned; best1cc855...=F ORx9 (22fullFP0FN),19afterduplicate8OR9merge. All20/19internalroots <=3freshformulaops literalcost<=21:1561993+1123314checks complete,noexact. Onefreshgate redirectedtoANYsubsetofasinglewirefanouts(includingrawinputs/output,oldconesclonedasneeded):14415+9000fullcontextchecks complete,noexactfunction. Allruns<1CPU,fullstdoutstderr/controls retained. FreeE core scan nowCOMPLETE7478states1.04wall,NO6gatecore; sourcef9acea...5b84 unchanged, mathematical3prefix/3tailcompletenessproof70fba... awaitingindependentreview; no global21bound. Nexttwofreshgatefanoutoncompact19, boundedscalaronly. S06nowownsreviewedstablemodehandoff; no further solverworkbyS05.

S05 TWO-FRESH-OP FANOUT COMPLETE: candidate134227-fanout2-handoff.json SHA28697eb5d4585d32e96689376442a7fbe49a09b8f2e19d8caf125a09b9f37321. best1compact19:531000fullcontextchecks,zeroexactfunction. best3compact20:879315checks,69exactfunctionrepairs,minimum22gatesafterstructuralhashcons/pruning; simplest raw8->8 OR(2 AND5) atthe8staroperand. No<=21. Fullformula/source/control/logs retained,0.40saggregate; no production. This coversselectiveusesofONEoriginalwire withup-to2freshformulaops,notarbitrarymultigaterewrites. Nextdifferentextensiononefreshsignal feedingup-to3portsfromdifferentoriginalwires, boundedscalaronly.

S05 GENERALIZED ONE-NEW-SIGNAL LOCAL DEAD END: candidate134227-multiport-handoff.json SHAc1ae7348534c6bb5b50950ff92011c739966e140254ef7bdbd4e40c692f92cdf. Both134227normalizedsources: onefreshgate(oraliasedexistingwire) fedtoup-to3ARBITRARYports,differentoriginalwiresallowed; all11521best3/9919best1portsubsets,8019545+4490100full2048contextchecks,zeroexactfunctionmatches.12randommaterialization/full2048scalarcontrols eachPASS;~2.3walltotal. Completeonlystatedlocalfamily,notglobal/candidateSAT/Lean. Combinedwithinternal<=3andfanout<=2results leavescrosscomponent/DAGsharing; preparingportablepostarchivepackage. MainS02componentmerger preservedownscope; noenginechange/production.

S05 NEW ONE-TRIPLE PACK READY_MAIN_REVIEW: allnegative-best4-pack-handoff.json SHAfb31cdf24db5e8964831f158ee1aa281589e361a709c59ea0e2cef8c08d3841c, 23fullartifacts. Packallnegative-best4-direct21-v1/direct-seeds.txt SHAf1316079fdd1c50eab3387c00ed7460130da5c6b862937241fa41b9ff13742a6;metadata0b3c2a8eed20aeb355be47e632689c70a1a7bd3d1d1c6d742fd2c17f29847642. Immutable b6da8...01b0 independentlyexactF ORx0*x2*x4,0FN4fullFP[21,29,85,149],minimalextra21only,21live,junk5/7. EightDISTINCTorders16384decodedoutputs+344064intermediatesPASS; reviewed141engine7d802...finiteSELFTEST256starts1024mutationsPASS3CPU/256MiB/8wallcap,NOproduction. Originalengines/packsuntouched. Mainquickalgebra independentlyverified2048rows; exactnormalizedsource441a221b84f6570ac59b0b9c776bcd6e90029232c8e649e34080f91d8db71f3a. Runningboundednewcontext/fanoutchecksnext.

S05 BEST4 REPAIR+GADGET RESULTS: allnegative-best4-repair-handoff.json SHA942e4e3213b28ad6c403efe9937d5080b23f74c9dd3ad952b518096998bc6f4f, 45fullartifacts. Immutableb6da8 normalized441a221b... exactF OR024 independently2048confirmed. All21internalroots<=3freshops790364checks no<=21. One/twofreshopselectivefanout15360/967680checks yields42/2546exactfunctionrepairs minimum22; onecommonsignal<=3arbitraryports7444480checks yields627exactrepairs minimum22. NEWcorrect-then-delete:9distinctexact22one-gatecorrectors,ALL396onegatealiasdeletionsfail; full7211840contextchecks1.26s. Simplestexact22corrector0->0AND9atcoreouterOR, retainedscalarcheckedcontrol. Focusedsubdivided-K4core7inputs9edges:full3linearclausecontributor enumeration256921triples thenbeam180/600pool finds12not11; with6-10extension8inputs10edges2238475triples/829poolfinds13not12. Bothbeamretainedstatescomplete~1.4walltotal, NOTlowerbounds. A12gate8inputcore WOULDlifttofull21 withthree2gateRstars+threeORjoins; currentlyonly13. No solver/Lean/production. Nextalgebraicallyequivalentcorecenterrotations yieldsame024functionbutdifferentgateDAGs, potentiallyfreshrestartvariants; originalnew8schedulepackfb31... alreadyREADY.

S05 DIFFERENT BEST4 DAG SEEDS READY_MAIN_REVIEW: allnegative-best4-rotated-pack-handoff.json SHA41bc836ef8ce7d277c02ddc9d4e298e1a57330478c73619f4439d14ec902c52f; packSHA7011217696ee0f16369cf72af22914b64ebc411a1c5e7adbcf5983e1b2a49b02;metadata25883566c60d982a6378afae2723a5cab0dd4d35f999bf1b6a5dac2fac1c6e16. TwoALGEBRAICcorecenters,notjusttopos: D5=(2+8+9)*(5+(0+8)*(4+9));D8=(4+5+9)*(8+(0+5)*(2+9)), sameR13 asb6da8. Each21live/F OR024/FP21,29,85,149;4distinctschedulespercenter=8newseeds. All16384decodedoutputs+344064intermediatesPASS; exactreviewed141engine finiteSELFTEST256starts1024mutationsPASS~0.4s, nosearch. Coulddiversifyrestartswithoutenginemutation; no improvementclaim. Originalf131packandalloldengines/packsuntouched. Packagingpostarchivecandidate/coreworknext.

S05 POSTTRIANGLE PORTABLE ARCHIVE READY_MAIN/S08: posttriangle-preservation-v1.tar.gz SHA572ffe05a24e4f1408c2990e6c06ce6320416ce029155c67ee541873a223aa4a,153531bytes/241regularmembers;manifest098c08e6750738f7871afeb3260c8e02dd144959012deddbdca9cf981632355c,handoffposttriangle-preservation-handoff.json SHA1107051b6b1d4f7e8d4c391ee6a3bde0fe6774ee1b2a64021d5253b9c8d51dbc. All241memberhashes+32768packoutputs+688128intermediates+8192source/controlinputs+384gadgetinputsPASS0.296s,NOengine/searchrun. Includesbothnew4FPpacks(originalf131.../rotated7011...), all134227andbest4boundedrepaircode/results/fullstdoutstderr,freeEcomplete7478scan+mathnotes/initialfailure,gadget7/8heuristiccode/exact12/13controls, fullfinite141selftests. Flattened73byteexactmembersofS08reviewed141archiveedfb...6f0 includescompleteengine source/build/fullcontrols/reviews andomittedbinaryhashes;NObinaries/activeoutputs. Onlyboundedlocaldeadends/inexact21seeds/exact22control; no21witness/globalproof. Producerlogs+handoffreceipt retainedseparately. S06gadget8generic12SATpreparationobserved; noS05duplication/production.

S05 IMPORTANT SMALLER GADGET LIFT FOR MAIN/S06: gadget7-lift-handoff.json SHA9b39fa156228c21bff211ee19f2d7298846732690a1211fbb0de99773e70901c. ANYexact7-input11-gateK4-subdivisioncore sufficesFULL21, withoutinterface/exposedhstar: complementsevenedges14,18,36,37,67,610,79 hasR9=6*(3+7+10) OR7*(3+9) OR1*(4+8), costs3+2+2+2OR=9; thenfinalOR1. Thus11+9+1=21. Independent128local/2048fullcontrolPASSusingknownlocal12->full22; edgepartitionexact. Thiscorrectsearlierconservativegadget7beam-scopewording(local11doesnotautomaticallylift), frozenarchivebytesunchanged/newaddendumexplicit. Generic7input11gateCNF maybesmallerusefulsufficientcasealongsideS06generic8input12; S05willNOTduplicateCNF/SAT. Bothactual11core/global21stillUNKNOWN. Fullmath/source/control/logs preserved.

S05 POSTARCHIVE ADDENDA READY_MAIN/S08: posttriangle-addenda-handoff.json SHAd05475ca6803c16dc9bbc243cec7577fcc9a6a5f3c23c03707097a5edee2e9b8,13files; archive572ffe...aa4a UNCHANGED. Includesexact7gadget11->full21lift9b39...901c andnewfreeEcompletionclarification: earliertext incorrectlysaidsmallcircuitsaretestedduringprefixgeneration; actualprogramcoversviaPADto3states, justifiedby10distinctrawpairANDfunctionsoutside6bases. Fullindependentset-generator reproduces25/456/7478states and4225ed...962b checksum; independentcost-layerDPon128sampledprefixes/1024tailtargetsPASS0.201s. Notfullindependenttailexhaustion/Lean/globalclaim; scan-sourcef9aceaunchanged. FrozenhistoricalNOTRUNwordingpredatescompletedscan,addendumexplains. Generic7/11and8/12gadgetSATbelongsS06, noS05duplication. Maincanpreservearchive+addenda together.

S05 SEVEN-INPUT GENERIC11 READY_MAIN/S08: gadget7-handoff.json SHAf57e1bfe20a7b5355d851076c6ab07e510086950a306c845e8adbb034f9e39e8, 66fullartifacts. Generator6bc53c66e01a9f7a3fbcede34ddba0893209636be60d4a1ea18505970b5b1c16;validator1eeceaaf05207387246634a12238389ba4059a5bf3cc43739edcf0173e8141bb. Generic11 847vars/10950clauses/16rows(9edges+7maxnegative),CNF186d15c94182fb9cd0cee60484dbab636419e267cf0980b00dcfed6bbcbc86a1,metadata8a67efc064d7ff414a573e439bc4eb4e18ac5fa51a9fd81134ffaff5f720ebd5. Exacttargetonvertices[0,2,4,5,8,9,10];allconstants/repeatedports/deadgates/dirtyANDs allowed,ONLYcommutativeorder+outputlastpadding. DerivedexactpinnedS06sourceswithfullparents/diffs/derivation; original8sourcesunchanged. Full128+full2048validator uses9-gateR+OR(total10); requireverified_inputs128andmeets_gadget_11_gate_limitTRUEplusfull21TRUE/exact4provenances inMAINfreshretainer. Positive12constructed936assignment ANDactualpinnedsolverSAT bothCLI0/full128/full2048/22gates,bothlimitflagsFALSE. Bad11=G OR024 hasonebadlocalinput/fullFP21,29,85,149; BCP835units/RUPchecker0 plusactualpinnedsolver20/DRATchecker0VERIFIED_UNSATONLYfixture. All7tinychildcontrols3CPU5wall512MiB8MiB caps,~0.28aggregate;64randomcircuits700800clausechecks/16kernel/128rowcoverage/6negativevalidatorsPASS. Generic11UNSOLVED,noproduction/no8/mainrunneredits. READMEexactrunnerkey/countdelta. Readyforindependentreview/ownrunnercopy.

S05 COMPACT7 ARCHIVE READY_MAIN/S08: gadget7-preservation-v1.tar.gz SHA599a252da72c3b5546271b665c2f006270bf703a628929717d939c0ce09cb13c,73974bytes/77regularmembers;manifest8c121a43ebe9b6df8bb9bd4af233e00bfb10fdd5926592dbe7b400b90f98d4b4;handoffgadget7-preservation-handoff.json SHA385f905dce9c6781b2bcadb8a29a4013b38e90809f9ec45cb8606b33221c5420. Noexecutables/rawCNFs/activeproduction. Portableverifier0.14srestoredall4CNFs+4metadataBYTEEXACT,all66historicalhandoffbindingsPASS; independentlyreplayedbothretainedpositivemodelsfull128/full2048andbad11rejection,NOsolver/checker. Allgenerator/validator/parentdiffs/fullcontrols/models/RUP+DRAT/solver+checkerlogs retained; positive12only22fullgates,bad11fixtureproofsonly,generic11historicalUNSOLVED. Source6bc53.../validator1eecea... frozenunchanged. S05stillassignedindependentS06KissatSAT-onlyrunnerreview; awaitinghisfrozenhandoffinNOTES, no production.

S05 INDEPENDENT KISSAT SAT-ONLY REVIEW PASS_MAIN_ADMISSION_CLEAR: exactrunnerfd05c03210c7d815ec81f0f3a292ef5d7eeb92f4380c8f4c5fde18d10aaa6bcd; reviewkissat-sat-only-review/review.json SHAf4d43dbd70113ab47b70de1eb3fa59bd7cf14b34db33ee309be82a72da2b969a;handoffkissat-sat-only-review-handoff.json SHAa7442833708c0264e301ab11336eac87c5660d77aad8dc9ab3a6fbc0cb3d08a8,65fullartifacts. Exactlifecycleaa5d13+Kissat21da5+validators7/8pinsverifiedbeforeafter; sourceinspectedacceptance/no-proofcommand/readonlysnapshots/hashbindings/abort+disko+wall+AS+logguards/sequentialPDEATHSIG/reaping. SIXfreshrealcontrolsunderOWNscratch~0.82s:7positive12+8positive13solver10/validator0full128or256/full2048/22gates correctlyUNKNOWNgate-limits;7bad11+8bad12solver20soleUNSAT remainUNKNOWN UNCERTIFIED_UNSAT_NO_PROOF/accepted_CNF_UNSATfalse,no proof/checker;prestartabort+wrongCNFpin stopbeforechild.52strictreport/provenance/count/type/flag mutationsreject;2syntheticaccept_reportbaselinesPASSclearlyNOTmodels/witnesses. Noexact21positivefixture exists, acceptancepathreliesonpinnedfullvalidator. Mainmaylaunch exactreviewedrunner afterresourceadmission; NOgenericsearch/productionbyS05. Frozen7generator/validator+8sourcesunchanged.

S05 REQUESTED7SOURCE+MAINREVIEW ARCHIVE COMPLETE_BEFORE05:48: preferredgadget7-preservation-v2.tar.gz SHAacca2f81671907cfd6c32ff252ff351445023df5f4ebbc00d015205c29e6476d,77159bytes/81regularmembers;manifestfeb9b212fd4741bf56805fe38761cd48116bfe6c9f9dab72bf0728c65c027db3;handoffgadget7-preservation-v2-handoff.json SHA958a221db12ac962d97158de0e24375b95db3dd1851e4cbaa2310e7d7252a6ed. IncludesexactcompletedMAINreviewaf69f66387be6371d6d04e09b48f86b44b2ef48b04ef2c83c140e3ed30dc8fed,frozen7source/validator/parents/diffs/allfullcontrols/models/RUP+DRAT/solvercheckerlogs and4portableCNFrecipes. FreshrestorePASSall4CNFs+metadataBYTEEXACT/all66originalhandoffbindings/bothpositivefull128+2048models/bad11rejection0.165s;NOsolver/checker. NOrawCNFpayload/executable/activeoutput; active7+8SAT-onlydirectoriesNEVERread. Originalv1599a...13c/gen6bc53.../validator1eecea... remainUNCHANGED. V2supersedesv1fordeliveryonly. S06ownsSAT-onlyrunner+S05reviewarchive separately; receiptbindsfullbuilder/derive/verificationlogs. No production/lease/git.
