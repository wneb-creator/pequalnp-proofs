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
