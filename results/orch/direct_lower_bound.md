# Direct lower-bound strategy

2026-11-25T13:48:51.488398+00:00 Initial investigation.

Definitions have no evident loophole: FanInTwo restricts each gate to AND/OR/NOT and at most two read indices; out-of-range reads are false. NOT reads only its first input (or false when empty).

Finite graph check (Python exhaustive subsets): 15 edges, independence number 4, vertex-cover number 6; maximal independent sets: {3: 10, 4: 5}. Triangle-free and C4-free. A star decomposition over a six-vertex cover gives the known 20 monotone gates: total OR gates within stars = 15−6=9, six AND gates, five final OR gates. This is an upper bound, not an unrestricted-circuit lower-bound proof.

The standard monotone intuition is 15+6−1=20. It relies on ruling out useful sharing; a general AND/OR/NOT circuit can cancel higher-degree terms, so the monotone intuition cannot justify the target. General rank/essential-variable bounds are too weak.

Existing reductions already occupy all three slots: R_meta_2592_271 (binary floor 15+NOT count plus 1–4 NOT case), R_meta_2592_408 (normalize invalid reads/trim output plus normalized lower bound), R_meta_2592_318 (last-NOT cut plus monotone-suffix separator). No fourth reduction should be submitted under current rules.

2026-11-25T13:51:04.930889+00:00 Existing binary-floor proof examined.

L_meta_4725 is a 3,200-line checked generic circuit/branch argument adapted to Petersen. It proves six first-branch groups, then binary count ≥10+6−1=15. The proof is already strong enough to exclude ≥5 NOTs under the budget. It does not yield the needed ≥19 binary gates in the one-NOT case; the monotone 20-gate construction uses higher branching multiplicities not captured by counting branch locations.

Potential alternate representation: normalize each wire by its all-zero value. NOT gates become copies in normalized coordinates. Each binary AND/OR gate becomes AND, OR, or set difference a∧¬b. This is an exact Boolean identity (checkable by four-case truth table), but no sound potential sharp enough to bound the remaining difference circuits has been found. A proof that ignores difference polarity falls back to the arbitrary Boolean gate lower bound and is insufficient.

Dead routes: adjacency rank over F2 only yields a weak bilinear bound; essential-variable counting only gives roughly nine binary gates; monotone star-cover optimality cannot be applied to unrestricted circuits without a new elimination theorem. The 20-gate upper bound and graph finite computations are independently checked by Python, not Lean in this agent.

2026-11-25T13:57:57.532914+00:00 Single-NOT semantic obligation and reduced core search.

For F=B∨(A∧¬G), with F,G monotone, any x satisfying F(x)=1,B(x)=0 has A(x)=1,G(x)=0. Any y satisfying A(y)=1,F(y)=0 has G(y)=1. Hence B(x∨y)=1: G stays true upwards, while F stays true upwards. For Petersen, x may be taken to be an edge using monotonicity of B; y can be extended to a maximal independent set using monotonicity of A,G. This is a necessary constraint, not a cost lower bound. An uncompiled Lean helper is in lemmas/direct.lean.

Reduced core: four OR triples bce,acf,ade,bdf and M=ab∨cd∨ef. They are the four stars and matching predicate of K4 edges. Triple outputs only need correctness on 27 inputs with M=0; other values are harmless in the final Petersen OR. Restricted exhaustive C++ search considered all81 ways to compute the triples with8OR gates, followed by any3gates with one NOT to obtainM. No witness in1,280,091 two-gate extension prefixes. This does not cover interleaved or relaxed-output circuits. Source and complete log in /tmp/oec/pequalnp-pilot-98/direct_or_extension.cpp and direct-or-run.log.

2026-11-25T14:10:55.681924+00:00 Finite obstruction strengthened and first Lean attempt failed operationally.

Both C++ and an independent Python set implementation checked all23,426 triples of helper subsets of six elements. Starting from the six singletons, even allowing union or arbitrary subset pruning as one operation each, three helper sets cannot make the four tetrahedral triples reachable. Four outputs plus three helpers account for seven operations. A positive control with four pair helpers constructs the targets in eight operations. Complete logs: direct-union-prune-run.log and direct-union-prune-controls.log in scratch.

The monolithic kernel decision in union_prune.lean exited137 after roughly five minutes wall time with no Lean diagnostic (last observed RSS3.25GB); this is an operational failure, not a mathematical rejection. Replacement union_prune_rows.lean splits the finite decision into53 first-helper rows of at most~1300 cases, then combines them by rewriting. It is not yet checked.

Further valid core relaxation: F=y1O1∨y2O2∨y3O3∨O4∧(y4∨H), requiring O4∧H=M. Thus H is constrained only where O4 is true, O1–O3 only where M is false, and O4 everywhere. An11-gate core yields19 full gates. The claim that known20 necessarily fits core12 was withdrawn as UNVERIFIED: existing20 may share satellite-dependent gates.

2026-11-25T14:25:26.254273+00:00 Checked partials and full table underway.

Using decide +kernel alone did not make1300-case rows fit2GB. Splitting by both first and second helper did: union_prune_pair_kernel.lean checked all51 remaining cases for helpers(3,5), and union_prune_row3_chunks.lean checked the complete minimum-helper3 row (1326 triples) using52 small pair lemmas. Both compiled exit0. Each source hash and complete output are preserved in corresponding validation.txt files under results/orch.

The semantic lemma oneNot_join_obligation in direct.lean also compiled exit0, with explicit Bool rewrites replacing an initially looping simp_all proof. It expresses the join obligation exactly and makes no size claim.

Full union_prune_all_chunks.lean is240513bytes/7202lines, with1378 pair lemmas and53 assembled rows. It is currently checking under -j1 -M2048. No full-obstruction claim has yet been made.

## 2026-11-25T14:37:14.434860+00:00: full finite certificate checked

UTC: 2026-11-25T14:37:14.434860+00:00
Source: results/orch/lemmas/union_prune_all_chunks.lean
SHA256: 953da8fd112cb367155e2c98d23af94a7ed60d40edd690cb9a93ee1c663177e1
Lines: 7202
Bytes: 240513
Lean exit: 0
Command: PATH=/tmp/oec/pequalnp-pilot-98/toolchain/bin:$PATH PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-98/toolchain/bin/lake PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-98/build-home MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-98/mathlib-cache LAKE_ARTIFACT_CACHE=false ../tools/bin/lake env lean --profile -j 1 -M 3072 /workspace/pequalnp-proofs/results/orch/lemmas/union_prune_all_chunks.lean
Formal conclusion: starHelperSearch = false. All 1378 pair lemmas and 53 row assemblies compiled, covering all 23426 unordered helper triples.
No claim: This certificate alone does not prove the Petersen circuit lower bound. Circuit-to-set generation and program-to-closure bridges remain unproved.
Resources: last sampled RSS 2966848 KiB, CPU 4m29s at wall 5m30s; exact terminal total was not captured. Process completed normally before next poll.
Full stdout: results/orch/union-prune-all-kernel-stdout.txt
Full stderr: results/orch/union-prune-all-kernel-stderr.txt
