# L-meta-1677 orchestrator notes

Assigned shard 6 of 20. Full goal: 16-gate lower bound for Petersen-minus-vertex edge function, first wire OR(x0,x6). Shard second gate: AND(x1,x2), OR(x1,x2), AND(x1,x3), OR(x1,x3), AND(x1,x4). Three reductions already live, so do not add another.

Strategies: sibling adaptation; structural lower bound; semantic/counterexample search; independent checker review.

Append findings below, naming the strategy and UTC time. No credentials or lease identifiers.

## checker_review — current upstream 29d8fbe

- Checker v4 supports check/refute/reduce. Guard and kernel checker are separate; run both on final bytes. Guard command: `node .github/scripts/outside-guard.mjs imports <file> <imports.json> lean/PEqualNP/Outside/L_meta_1677.lean check`.
- Every helper must be in a namespace named PEqualNP.Outside.L_meta_1677 (or its _aux namespace); final fully-qualified theorem stands at top level, last. Scope commands start at column zero and ends name their scopes.
- Assigned shard 6 restricts second-gate search to AND(x1,x2), OR(x1,x2), AND(x1,x3), OR(x1,x3), AND(x1,x4). The posted theorem still quantifies over ALL circuits with first gate OR(x0,x6). A shard-only result does not prove that exact statement.
- SEARCH exhaustion is a desk report with reason=exhausted and SHA256 of a program that fully searched the assigned range. A time-bounded or heuristic search without a witness is not exhaustion.
- Reduction currently unavailable: desk reductions_live=3, already the specified maximum.
- No independent review verdict on a proof yet; waiting for final candidate and saved build/checker logs.

## sibling_proof — 2026-11-24T23:13:59.771894+00:00

Checked OR siblings cover pairs (0,1), (0,2), (0,4); our (0,6) is degree-3/degree-2 nonedge and is not automorphic to them. L_meta_1676 supplies a reusable circuit-to-live-frontier extraction and ordinary graph lower bound 15, but its augmented OR certificate is specific to (0,4), requiring regenerated forests. Existing reduction R_meta_1677_1 uses an eight-input cofactor bound plus elimination of two reads and a single-read tail lemma. L_meta_3973 solves one branch of that latter lemma, not the whole goal. Full proofs already in pending PRs may be more promising than rebuilding certificates.

## Structural route findings

- The OR(0,6) seed is a distinct automorphism orbit: degree-3/degree-2 nonadjacent vertices sharing neighbor 1. Checked OR(0,4) is adjacent, OR(0,2) uses two degree-3 vertices.
- Defs imports contain definitions, not general circuit lower-bound lemmas. Existing Outside proofs must be inlined.
- Three existing reductions of L-meta-1677 are already merged: R_meta_1677_1 (13-gate 8-variable cofactor + deletion of two reads + single-read obstruction), R_meta_1677_361 (at least 13 binary tail gates + low-NOT obstruction), R_meta_1677_704 (14-gate boundary lower bound + optimal boundary obstruction).
- L_meta_2541 internally proves unconditional 15-gate lower bound under an input polarity; its theorem ignores its single-read assumption. This is a potential stronger base certificate if a first-OR overhead can be isolated.
- Ordinary support counting is insufficient: 9 inputs alone yields only 8 gates. Generic monotone graph formula bound would be 12 edges + cover 5 - 1 = 16, but allowing NOT and shared gates is the actual missing difficulty.

## Counterexample / semantic audit (independent)
- Circuit semantics are ordinary AND/OR/NOT, fan-in at most two. Forward wire references read false; empty gates yield constants. No semantic loophole found.
- Exact finite graph audit: degree sequence [3,3,3,3,2,3,2,2,3]; 12 automorphisms; minimum vertex cover size 5, with covers (0,1,3,7,8), (0,2,3,5,6), (1,2,4,5,8). Standard monotone cover constructions use 12+5-1=16 gates.
- Pair (0,6) is degree-3/degree-2 nonedge. Its orbit excludes the proved OR sibling pairs (0,1), (0,2), (0,4); direct graph-automorphism transfer does not apply.
- Installed libz3.so.4 is accessible through ctypes although Python z3 bindings are absent. A 15-gate CEGIS synthesis search has started in scratch, fixing first OR(0,6) and restricting the second gate to assigned shard 6. It checks proposed models on all 512 inputs; no bounded search failure will be reported as exhaustive without an UNSAT result.

## checker_review — 2026-11-24T23:15:24.272437+00:00

Reviewed original PR10495 candidate, SHA256 `65e331d2ceb61e70d00216f4e25e753032e13f5d57dbb21bf4de214e1b5b6854`. Full imports/plain/own-namespace guard PASS. Posted theorem byte match PASS. Size 521151 bytes (3137 bytes below limit). Ten custom inductive/structure declarations trigger manual-review condition but are not forbidden by guard. No declaration-shadowing concern identified. Final proof chain has correct all-512-assignment semantics and full first-OR hypothesis; it is not restricted to assigned shard. Build and kernel acceptance remain unverified, and final adapted candidate still needs review.

Toolchain setup: official Lean 4.36.0 installed at /tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux. Prepend bin to PATH. Mathlib cache downloading (9117 artifacts); MATHLIB_CACHE_DIR points to /tmp/oec/pequalnp-pilot-46/toolchain/mathlib-cache. The distribution includes cadical. No lake update and no Mathlib source build.

## Root integration, 2026-11-24T23:15:58.800781+00:00
Existing complete public candidate PR10495 by zakpgrove fetched and credited. Original521151bytes; guard passes; exact statement independently confirmed. Adapting custom datatypes to library types for automatic review. Sibling owns Live/Reach/Run/BoundPool/IndexTree/Forest; structural owns Grouping/Rule; root owns SignedForest/Six3640. Optimization agent profiling rank and certificate evaluation. Original kept in scratch as fallback.

## sibling_proof — core datatype conversion prepared

Scratch convert_core.py ports Live, Reach, Run to Church encodings borrowed from checked L_meta_1676, BoundPool to products, IndexTree to List, Forest to Sigma/product/subtype. Result remains uncompiled until cache setup finishes. It updates elimination proofs and compresses whitespace; apply this script last after original-text transformations. Source transformed alone is 522238 bytes, close to the 512KiB cap.

## Structural semantic audit and type conversion — 2026-11-24T23:16:38.180807+00:00

- Audited fetched PR10495: final theorem statement is byte-for-byte desk statement; independently recomputed512-row graph table matches; all9 essential input witnesses change target and preserve OR(0,6). No hidden proof holes or executable tactics found. Final first-gate removal and seeded/bare frontier split match the posted semantics, including default-false invalid wires. Full kernel build/check remains required.
- Grouping and Rule type-free conversion script: `/tmp/oec/pequalnp-pilot-46/structural/convert_grouping_rule.py`, exports `transform(text)`. Grouping becomes subtype of labels with pair/cut proof conjunction; Rule becomes Sum of tuple payloads. Init-only constructor/accessor/pattern shape test passed. Full converted proof awaits cache/build.
- Boundary sanity check: an explicit 16-gate monotone circuit with first OR(0,6) and second OR(1,3) agrees with the target on all 512 inputs. Data is in scratch/counterexample/upper16.json. This confirms the requested bound is tight in at least one assigned second-gate case, without proving its lower bound.
- Direct CNF CEGIS search now uses the installed CaDiCaL: 62 selected assignments initially, 2,992 Boolean variables / 53,462 clauses, 15 gates. It includes constants/copies via normalized AND/OR/NOT gates and permits false wire reads, so no well-formedness assumption is silently added.

2026-11-24T23:17:02.460404+00:00 toolchain setup complete: Lean 4.36.0 binary works, lake exe cache get exit 0, all 9117 Mathlib artifacts downloaded and decompressed with zero reported errors. Prefix PATH with /tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin. Logs: /tmp/oec/pequalnp-pilot-46/toolchain/cache-get-2.stdout and .stderr. Normal project Defs build remains.

## checker_review — 2026-11-24T23:18:46.102662+00:00 — partial artifact review

Mask.lean SHA256 `4d0b357bc4e1ff983584f84de5127c072abb4ca73c256d49d2f4bcea8b88bbc3` independently compiled under Lean 4.36.0 with exit 0. It proves the optimized mask-cons equation by eight Boolean cases; no proof holes or kernel bypass. Its compile log has only an exponentiation-threshold warning. Mask source/log and notes/timeline passed credential-pattern inspection. Approved only for clearly labeled partial artifact preservation, not as the posted gap proof or PR.

## Certificate optimization (2026-11-24 23:20:27 UTC)

Decoded all 3,442 rank checks in public PR10495; Python confirms each explicit constraint set is unsatisfiable. Existing rank variable order explores213,690 labels; greedy order181,008, but extra ordering cost makes this unlikely useful.

A checked helper proves skipping identity bitwise intersections in FrontRanks.mask preserves semantics. Isolated512-row interleaved benchmarks: [{"name": "maskOld", "exit": 0, "cpu": 4.479641, "system": 0.490508, "wall": 8.002898591999951}, {"name": "mask", "exit": 0, "cpu": 3.162993, "system": 0.21117199999999997, "wall": 6.321900516999904}, {"name": "mask", "exit": 0, "cpu": 4.093433, "system": 0.382578, "wall": 10.321932280000055}, {"name": "maskOld", "exit": 0, "cpu": 4.523508000000001, "system": 0.3358460000000001, "wall": 7.104607616000067}]

Optional patch: /tmp/oec/pequalnp-pilot-46/optimization/skip_identity.py; not applied to full candidate. No full-proof runtime claim. Core helper Mask.lean compiles with Init using Lean4.36; this is only a partial lemma, not gap1677.

## checker_review — 2026-11-24T23:20:35.575552+00:00 — adapted full source

Independent source review PASS for SHA256 `330e4b55a2d556c1acb6dccc58952a95c09e5e2c701a46c348b40ac44f48501a` (522178 bytes,5995 lines). Entire normalized diff reviewed: Church eliminators, tuple/subtype/Sum encodings and projections, constructor rewrites, duplicate-proof aliases. All249 hexadecimal certificate literals unchanged; final posted statement exact; full guard PASS; no custom datatypes, attributes, prohibited shortcuts, declaration shadowing, or credentials found. IndexTree changes to flat-list lookup, so concrete certificate evaluation must validate the new lookup behavior; its generic soundness still rests on read_mem. Full build and kernel checker acceptance remain pending. Any source hash change requires incremental review.

## Structural conversion verification — 2026-11-24T23:20:36.758118+00:00

Grouping/Rule conversion passed isolated Lean compile (exit0) of actual Grouping, Rule, checksRule_sound, Digits.compile_sound, rankCheck_sound, rankHuffCheck_sound and their prerequisites; only existing unused-simp warnings. No corrective patch needed. Full main candidate build remains authoritative. Log: `/tmp/oec/pequalnp-pilot-46/structural/GroupingRuleTest.log`.

## sibling_proof — 2026-11-24T23:20:43.609686+00:00 — generic prefix compiled

The transformed 2194-line generic prefix compiled successfully (exit 0) with the pinned Lean toolchain and built Defs. This validates Church Live/Reach/Run, their updated induction/elimination proofs, BoundPool products, and Forest Sigma/subtype representation before certificate data. Full stdout/stderr is sibling/prefix.log under the job scratch directory. Separately, a balanced IndexTree implementation using only a subtype of List × lookup function compiled successfully; optional snippet sibling/index_tree.txt preserves original pivot lookup semantics and avoids linear list lookup. Root owns integration and full-file validation.

## checker_review — 2026-11-24T23:21:29.679991+00:00 — second checkpoint

GO for preservation checkpoint. Prefix.lean (`75fa93700d2e416b53a8b1748b8f99e6fdf6c9dde9a617fb1536e8c5e0ecf496`) is exact full-source prefix plus namespace closure. GroupingRuleTest.lean (`7e4399da35697eaae66791f6f318e1e7fb9e032eac57e9d2839b4d8589f2ee62`) is an ordered extraction of reviewed source with only the broader Mathlib dependency added. Both logs contain warnings and no errors, consistent with reported exit0. No prohibited proof holes or credentials found. Full source hash unchanged from previous review; preserve it explicitly as pending certificate, not a checked full proof.
- Counterexample search completed without a result: Z3 returned UNKNOWN at its five-minute limit; CaDiCaL reached its five-minute wall-time limit without SAT or UNSAT. Both solver processes have exited. These runs do not justify an exhaustion claim. Complete generated formulas and solver logs remain under /tmp/oec/pequalnp-pilot-46/counterexample/.
- The tight 16-gate witness was independently revalidated with a second Boolean-tuple enumeration implementation over all 512 assignments, also checking gate indices and the shard-6 prefix. No counterexample to the posted lower bound was found.

## sibling_proof — 2026-11-24T23:22:40.847901+00:00 — conversion follow-up

Full-file profiling exposed two later Live induction variables named l and a whitespace compression issue in an inline bullet. Converter now recognizes all explicitly typed Live/Run/Reach proof-variable names and preserves every original relative indentation by subtracting only one leading space. It also restores balanced IndexTree lookup using the separately compiled standard subtype representation. New core-only output521166bytes5986lines; root integrates into combined candidate and reruns full validation.

## checker_review — 2026-11-24T23:23:11.659145+00:00 — v2 delta

Source-only delta review PASS for `e300d0c36141a27da3c7d8a22b1a27a9f9731212bea3bdc41deb4ec9d61b8da2` (522615bytes,6002lines). IndexTree subtype restores original pivot-based read semantics while storing read-membership proof; two remaining inductions explicitly use Live.induct. Other differences are indentation. Full guard passes; exact posted statement and all hexadecimal certificate data retained; no custom datatypes or credentials. Build/kernel acceptance pending.

## checker_review — 2026-11-24T23:40:37.908794+00:00 — audit-block splitting

Independent AuditParts.lean compile exit0, empty stdout/stderr. Helper SHA256 `b6164ef7f7642253006d16294c07e39d3565bf8bfa97cfec25ba0ef0a6df748d`. Reviewed splitter script; independent rerun reproduces exact preview bytes. Preview SHA256 `91ccfc37d5eee47cee1b6d82d2de9240105c33306cf73126cce980d15b717ceb` (521499bytes6253lines) passes full guard, keeps statement identical modulo whitespace, retains every hexadecimal certificate literal. All60 interval partitions independently checked complete and contiguous, with nonempty leaves at most8 nodes. No credential patterns found. GO for partial artifact push and source adoption; full optimized proof build/checker still unverified. One transient exec-server transport failure occurred, then retry succeeded.

## checker_review — 2026-11-24T23:42:47.308576+00:00 — adopted split preview

GO for pending checkpoint of `5439dbcaa6f90064037f257c999c1cb3cc19233ab9dd2deddf75d6821ec08f54` (521507bytes6253lines). Independently confirmed only change from reviewed split preview is final theorem whitespace restored to byte-exact desk statement. Entire source identical modulo whitespace; prior source/guard review carries forward. Full build/checker remain pending.

## Re-plan at30minutes
The full library-type certificate is the primary route. Structural-only bounds do not close the16gategoal; counterexample searches timed out without a witness or exhaustion. Baseline fullbuild was interrupted by the environment restart after about19minutes, with memory spikes above10GB. Reviewed partition proofs now bound each closed audit to8nodes; all certificate data and the posted statement remain unchanged. Toolchain/cache survived; restarting named build on the partitioned version.

## sibling_proof — 2026-11-24T23:58:12.130611+00:00 — runtime audit

Read-only audit found no convincing speed improvement in datatype conversions or packed-data readers. Balanced IndexTree lookup remains logarithmic and is used by the smaller signed-search tail; the dominant rank path reads only stateSet/readNode, whose unwanted Decor sample fields stay lazy. Forest projection chains are bounded by eight product projections. packedAt/lookupWord already use primitive Nat arithmetic and bitwise operations. A direct Huffman-to-Rule decoder could remove packing/unpacking, but tag lengths are modest and the correctness changes are unlikely justified without profiling. Recommendation: retain current core, focus effort on forced/mask/checksRule and memory-bounded certificate batches. No benchmark or final-file change performed.

## checker_review — 2026-11-24T23:58:41.530833+00:00 — specialized mask helper

MaskSpecialized.lean independently compiled under pinned Lean4.36.0, exit0. Hash `079a47990adde8d200fa2c2ca2e847d8b26117214bf4e3ca9fa6147f93f89210` (1695bytes). Specialized up/down/exact recursion selected once by mono/desired; mask_nil and mask_cons prove original equations. Only exponentiation-threshold warning. No proof holes, axioms, prohibited shortcuts or credentials. GO for partial artifact push; not yet a full-candidate change.

Authoritative workflow enforces1200s TOTAL for our no-Outside-import proof: cold proof build plus serial kernel replay. Trusted Defs/Mathlib/verifier build precedes timer. Default2cores/3Leanthreads. Lean4.36 Replay.lean checks declarations serially using addDeclCore, so replay cannot benefit from compiler task parallelism.

## sibling_proof — 2026-11-25T00:07:09.605693+00:00 — rank certificate pruning rejected

Python decoded 3442 rule-bearing mode certificates: 23302 rules, no duplicate coloring constraints after normalizing the symmetric first two vertices. On 19 representative certificates (largest, hardest coloring searches, deterministic random sample), all 493 original rules were individually necessary: deleting any one made the remaining coloring constraints satisfiable. Thus these samples are inclusion-minimal and cannot be shortened by selecting a proper subset. This is a computed search result, not a Lean-checked theorem. Runtime0.21seconds. Complete program and records live in sibling/minimize_rank.py, sibling/minimize-rank.log, and sibling/minimize-rank.json under job scratch. Stop this route; prioritize the optimizer’s cube row-sharing check.

2026-11-25T00:08:10.954379+00:00 Optimization: natural-row plus specialized mask semantic spec compiled (NaturalChecksSpec.lean, exit0,3GB cap); exact equality preserves mask/forced/checksRule semantics. Isolated512rows ×3modes benchmark: original mean3.572CPU seconds vs natural1.468CPU seconds (59% less; four interleaved exit0 runs). Final full-certificate speedup unverified. Scratch natural_rank_patch.py derives checksRuleNat from current checksRule, changes rankCheck via checksRuleNat_eq; preview521658bytes afterassignment-space compaction, source SHA5439dbca. Independent reviewer notified; target untouched.

## checker_review — 2026-11-25T00:08:27.228911+00:00 — natural-row optimization

Independent NaturalChecksSpec.lean compile exit0 (warnings only), SHA `0f6363e07da5e94434feb5b34202b7663aa471ae929a2cc6f2e483d6917ce40e`. Complete patch/preview semantic delta reviewed. Natural masks equal old masks on bit rows; putBit implements one coordinate update; row_pair preserves update priority including coincident indices; checksRuleNat_eq proves unchanged checker function, and rankCheck_sound explicitly uses it. Preview `9d23fefb1aac1967171e36ca4615e60e8e6e5cf0cf836ace41d732ad007294e3` (521658bytes6319lines) passes full guard; exact statement and all249hex literals retained. Script independently rerun reproduces preview byte-for-byte. No prohibited constructs or credentials. GO for partial checkpoint and source adoption; full preview compilation/kernel check pending.

Conservative source scan found no uniquely named declaration without textual references; no obvious safe dead-helper deletion candidate. Certificate evaluation remains the main grounded optimization target.

Natural-row evaluator: equality to the original finite-index mask and rule checker proved in Lean. Independent reviewer PASS, preview preserves the exact statement and all249hex certificate values. Partial result only; full optimized candidate not yet adopted. Representative rule-pruning search found all493sampled rules necessary; strategy stopped. Public predecessor PR10495 has authoritative timeout FAULT(exit124), so reducing kernel work is necessary.

2026-11-25T00:13:15.736874+00:00 Optimization follow-up: natural evaluators returning Nat directly compile with exact mask-toNat, forced, and checksRule equality proofs (NaturalChecksDirectSpec.lean exit0). Explicit finite complement (2^512-1) xor input; no infinite-width complement. Four interleaved pairs suggest ~9.5% further CPU improvement over natural Word return (1.563 vs1.415 mean CPU seconds), noisy. Combined six-corner + direct-natural checked wrapper SixNaturalDirectSpec.lean exit0; scratch combined preview524128B6397lines, using assignment and comma-space compaction, target untouched. Separate 512-bit literalconstant benchmark only~2%withinnoise; not adopted.

## checker_review — 2026-11-25T00:13:27.642256+00:00 — full build and next optimization

Independently confirmed full named build log `d18b5b77921d1eeb7d8889fb4dc13ada0a57eb3e9c2781f8dbe7be29af0d108e` ends Build completed successfully(5147jobs), zero error lines, target build1730s. Source remains reviewed `5439dbcaa6f90064037f257c999c1cb3cc19233ab9dd2deddf75d6821ec08f54`. Built olean15507272bytes SHA `952ff865f3ae09447b99df2c69ed4e5f5657611ecbcb1e7ff9e1e8ce172f5b24`; trace non-synthetic. Kernel checker pending.

Combined six-corner+natural-row+directNat preview source review PASS at `5de1e631e3cc5728438f77dedec6f082fbb93b95f95120340dee034853d8921f` (524128bytes6397lines,160byte headroom). Independently compiled SixNaturalDirectSpec exit0 (hash `474ee1ff189ba8420b94d77ef72eb69b6ac7fc20c7788e53938cbf1e7ff6b31c`). Monotonicity supplies omitted square corners; finite512bit XOR complement and toNat equivalence preserve mask checking. Full guard passes, all249hex certificate values retained, statement identical modulo whitespace. Independent composing-script rerun reproduces exact preview. No credentials. GO for source adoption after current checker; full optimized-file build/checker still required.

Full baseline proof compiles: target1730s, final Build completed successfully (5147 jobs). This does not meet the authoritative20minute total budget for cold compilation plus replay. Local checker initially could not find elan; the repository wrapper explicitly supports PEQUALNP_REAL_LAKE, now set to the installed pinned Lean4.36.0 Lake. Warm checker is replaying the built proof. The next independently reviewed evaluator adds direct Nat masks and six-corner monotone square checks; no optimized full-file build yet.

## Structural runtime optimization — 2026-11-25T00:16:17.700178+00:00

- Six-corner monotone-square checker and four-check monotone-cube checker are implemented in composable scratch transforms `structural/six_corner_patch.py` then `structural/cube_corner_patch.py`, before the optimizer natural-row transform. Both full checksRule_sound proofs compiled in isolated minimal-import tests (exit 0). CubeCheckerTest SHA256: d803452a0732032d59141543c18ef1e1bc13523f199fa881d82a87b8e858fba1.
- Shared lemma: if a monotone Boolean function has output b, setting any coordinate to b preserves that output. This supplies omitted AND00/OR11 square corners and omitted cube high/low checks. Signed cases retain all original checks. Independent semantic review passed.
- Complete packed-rule census: 7041 monotone squares, 12271 monotone cubes, 2387 signed squares, 1603 signed cubes. Every monotone cube has bit=sign. The two changes eliminate 26353 of 144794 forced evaluations, about 18.2 percent.
- Cold 256-square Init-only benchmark after natural masks: old kernel typechecking 2.96/3.38 seconds, six-corner 2.93/2.19 seconds; mean 3.17 to 2.56 seconds, about 19 percent, with shared-CPU noise. All passed and peak RSS was below 0.82 GiB. No cube benchmark was started after root memory warning; all helper compilation had already finished.

Decoder invariant proved: each decoded cube rule agrees with its shared raw row outside the two selected coordinates. Both corner and full decoder helpers compile under Init; independent source/log review passed. Integrating this invariant could remove the repeated finite-coordinate scan. The current full source remains the compiled baseline while its checker runs.

2026-11-25T00:21:14.270683+00:00 Decoder optimization completed: every cube emitted by ruleCode shares all coordinates outside i/j because each row is raw OR two one-bit patches. DecoderInvariant.lean proves this for each readRules member; Init-only compile exit0 at512MB. DecoderBridgeInitSpec.lean proves the restricted checksRuleNat equality plus conversion of all decoded checks, exit0 at512MB. This removes cube sharing scans entirely while retaining generic checksRule_sound. Final combined scratch preview candidate-decoder-compact-preview.lean SHA814065a5d0301e00b6f2ac9969c36ea38cb8d44a15aa8344d6eee19130c76b85,523865B6483lines,423Bheadroom. Includes natural rows/directNat, six-square and cube monotonicity skips. Independent reviewer passed full composition, guards, posted statement and exact certificate preservation. Source target untouched; full performance measurement pending baselinechecker completion.

Best composed candidate is preserved under candidates/L_meta_1677_optimized.lean (SHA814065a5d0301e00b6f2ac9969c36ea38cb8d44a15aa8344d6eee19130c76b85). It combines natural-row/direct-Nat masks, monotone square/cube shortcuts, and removal of decoder-guaranteed sharing scans. Full candidate source review/guard passed; semantic bridge helper compiles. Full candidate compilation and checker remain unverified. Current named target is still the previously compiled baseline.

Active step changed to L-meta-2585 after deskHTTP410 on1677. No1677PR opened: fullbuild passed but localchecker was intentionally stopped on lease loss and has no verdict. All1677source/results are preserved in history. L2585 asks size-preserving read1 replacement for C4-free incidence AO2 circuits. Read1 means a squarefree proof tree for each prime implicant, not global variable fanout. Several useful partials compile. The conditional3-child cut is not an accepted reduction: public2585metadata lacks reductions:true, and printed-child/kernel checks were pending at checkpoint. The unrestricted global cover lower bound remains hard.

## L-meta-2585: independent semantics and finite tests
- `TopForm.IsAO2` means AND/OR, exactly two earlier wires. `ReadK.IsReadK ... 1` means every prime implicant has some proof tree reading each of its variables at most once; it is not global formula read-once. For incidence functions the prime implicants are exactly edge pairs. Empty incidence is vacuously read-1; a zero-gate out-of-range output gives false.
- The cover upper-bound hypothesis proposed by the structural agent is plausible without any 4-cycle restriction: assign every edge to one covered endpoint, build one star per nonempty assigned center, then OR the stars. Its cost is m + k - 1, with k at most the selected cover size, and every edge has a squarefree tree.
- Exhaustive ordinary-computation tests of that construction passed: all 512 relations on 3+3 inputs, all 13,009 valid covers, all 64 inputs per case; also all 18,521 4-cycle-free relations on 4+4 inputs with a minimum cover, all 256 inputs per case. Gate legality, the cost bound, exact function, and squarefree edge proof trees were checked.
- CaDiCaL found UNSAT for seven-gate AO2 circuits computing the six-cycle on 3+3 inputs, against all 64 inputs, in 3.406 seconds. Its cover construction has eight gates. This is a computational SAT result, not a Lean-checked theorem.
- Testing the maximal 4+4 theta graph (nine edges, cover size four) for an eleven-gate AO2 circuit; its canonical read-1 construction costs twelve. No counterexample has been found so far.
- Code, formulas, complete logs: /tmp/oec/pequalnp-pilot-46/gap-2585/counterexample/.

L-meta-2585 structural agent: three-child reduction drafted and Lean-compiled under Defs only. Children: arbitrary AO2 normalization, cover-cost charge for normalized C4-free incidence circuits, read1 star-cover synthesis. Exact canonical printed lengths 592/1036/606 (<2000 each). Scratch gap-2585/structural/ReductionDraft.lean, PrintChildren.log. Independent reviewer source pass. Reductions public eligibility absent, so this remains a conditional result. Generic normal-form census checked 4045 irredundant3-input and81985 irredundant4-input AO2 circuits through4gates; no minimum-cost difference for the19/117 output functions found. Normalization proof assembled from checked4742 erase lemmas and4295 lift/count lemmas: NormalizeBase.lean 1648lines/80KB compiled exit0; new extremal Nat.find proof pending compilation after root checker frees memory.

Recorded 2026-11-25T00:35:15.151944+00:00 by counterexample agent.


### L-meta-2585 counterexample audit update

- All 16 nonempty C4-free bipartite graph representatives with at most 3 vertices per part were checked against AO2 synthesis with one gate fewer than `m + minimum_vertex_cover - 1`. All returned UNSAT (the one-edge, zero-gate case was checked directly). This covers every 3x3 relation after deletion of isolated variables and relabeling; isolated variables may be identified with an existing input without changing the function. This is ordinary SAT/Python evidence, not Lean checked.
- The 4+4 theta graph with 9 edges, vertex-cover minimum 4, and canonical cost 12 was searched at 11 gates for 300 seconds. It timed out with no SAT/UNSAT verdict. No solver remains active.
- Full CNFs, solver stdout/stderr, construction audit, and summaries remain under `/tmp/oec/pequalnp-pilot-46/gap-2585/counterexample/`.
- Literature read on 2026-11-25 has not established the exact unrestricted lower bound `m + tau - 1` for C4-free bipartite incidence functions: that general claim remains UNVERIFIED. Jukna's single-level counterexamples use saturated, explicitly non-bipartite graph extensions; the C4-free graph-representation problem in *On Graph Complexity* concerns only two-hot assignments and a different circuit model. Mehlhorn's nearest disjoint-sums result concerns multiple OR outputs, not this one quadratic output.
- Subdivision does make a simple graph's incidence graph C4-free, but replaces each old edge with an independent input: `F(x,z) = OR_{e={u,v}} z_e AND (x_u OR x_v)`. No transformation preserving an old general graph-function circuit's size advantage has been found.

2026-11-25T00:35:34.473144+00:00 Gap2585 direct route: checked clean-block rectangle/star semantics (CleanBlockBridge.lean), uniqueness of opposite-side center for any ≥2 pure OR leaves (PrivatePureOr.lean), and generic shared binary OR budget leaves≤gates+roots (SharedOrBudget.lean). All independently reviewed. Safe clean-case global charge groups top stars by center; sharing within a center remains allowed, across centers forbidden for nontrivial pure-OR supports. This does not handle dirty internal AND blocks. Existing L4742 has full liftAt semantic/size helpers; L3243 and L3245 prove concrete coverCircuitB size/semantics/model. L3444/L3446 refute naive maximal-core aggregate budgets.

2026-11-25T00:36:37.090658+00:00 Gap2585 additional finite evidence: NormalFormWitness.lean (SHA5b483b47e214f7bcafcc3b857d83c958c35932fd15ad0fa70b35cc3665054b08) compiled exit0, empty log. On2+2inputs with incidence l≤p, the5gate CNF (x0∨x1)∧(y0∨y1)∧(x1∨y0) satisfies the exact proposed generic below-wire normal form but is not ReadK1; explicit4gate star circuit computes samefunction and is ReadK1. This only refutes the shortcut NF⇒ReadK1, not gap2585. Dirty mixed-block size charging remains essential.

L-meta-2585 structural agent CHECKED COMPONENT: NormalizeLeastFull.lean Lean exit0, SHA256 b04f0b2ad3a760d7705cf574b1f84ca46c44e4b97c74496d4f243ebe287a608e. Defs-only, no sorry/new axiom/custom type/instance. Proves arbitrary AO2 circuit can be replaced at no greater size by a globally minimum equivalent circuit such that every below-output gate feeds only below-output OR gates. Proof: minimum gate count, maximum number of below-output gates; erase below-output AND readers, LIFT below-output wires entering non-below OR gates. Copied foundational lemmas credited to checked4742 and4295. Strengthened reduction variant ReductionLeastDraft.lean also compiles, printed children777/1245/606characters. Current accepted draft remains root-owned; public reduction eligibility still absent.

The original three-child R_meta_2585_46 is now locally ACCEPTED(reduce), with only standard axioms and1648constants rechecked. The named source replaces the old1677file in the current tree; the compiled1677baseline is preserved under candidates and history. Official eligibility guard explicitly REFUSES submission because2585does not carry reductions:true. This is not a full proof or a published reduction. Independently reviewed NormalizeLeast2585 proves the generic normalization component (including global minimum size); SharedOrBudget proves cardinal accounting with sharing allowed; NormalFormWitness proves normalization alone does not imply read1, without refuting2585.

Research read2026-11-25: Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, section3.5 gives edge-count lower bounds for K2,2-free graphs under the SINGLE-LEVEL restriction; section8 Problem8.2 historically asks for explicit quadratic functions with superlinear monotone circuit bounds. Inference: the remaining all-C4free cover charge is substantial, since dense incidence graphs would give such bounds. Current2026 status of that historical question UNVERIFIED: no current primary resolution located. This is context, not a proof or refutation.

The current R46 now restricts the charge child to globally least normalized circuits. Its exact posted conclusion is unchanged. The short function-equality transport removes five lines (48 to43); named build and local reduction checker pass again. This remains a conditional theorem, and public submission eligibility is still absent. A new closed CleanNF bridge proves ReadK1 for normalized circuits when all AND wires lie below the output; the remaining issue is handling dirty AND gates in least circuits. The current checkpoint preserves all source and checker outputs.

Recorded 2026-11-25T00:50:28.818406+00:00 by counterexample agent.


### L-meta-2585 separate gate-count SAT attack

A stronger finite encoder now tests a bound on one gate type while allowing arbitrarily many of the other type. Flatten every uncounted-only region into a nonempty aggregate of input variables and earlier counted outputs; each counted gate keeps two aggregated inputs; the final output is another aggregate. This is equivalent to unrestricted AO2 circuits with at most k counted gates for nonconstant targets. Identical operands are allowed. Unused counted gates may be pruned; exact-count padding uses counted duplicate-input gates at the output, preserving liveness. Structural agent independently checked this collapse argument.

SAT truth constraints use every edge-positive input and every maximal independent set as a negative input, sufficient by monotonicity. Every SAT witness is expanded into binary gates and validated on the complete Boolean truth table. The encoder passed expected SAT/UNSAT boundary cases for the 3-edge path. Solver memory is capped at1900MiB, each invocation at300s or less; complete CNF and stdout/stderr retained. These are computational checks, NOT Lean proofs.

- C6: AND count≤2 is UNSAT with no OR-count limit (0.006s). OR count≤4 is UNSAT with no AND-count limit (0.217s). Thus both proposed split bounds hold on this graph computationally.
- Theta4x4,9edges: AND count≤3 is UNSAT (0.034s). OR count≤7 search was terminated after about140s without a verdict to prioritize a stronger test and improved symmetry.
- C12 (6x6 cycle incidence): AND count≤5 now searching. It has29 maximal independent sets, so the elementary maxterm-count bound forces only5AND while the proposed vertex-cover bound predicts6; this is the first cycle where that elementary count does not settle the desired bound.
- Fano7x7 has37 maximal independent sets, similarly allowing a nontrivial6AND test against the proposed7AND bound.

Scripts: `macro_count_search.py` (gate-count collapse), `ao_boundary_search.py` (total size with boundary rows and optional root normalization), scratch `/tmp/oec/pequalnp-pilot-46/gap-2585/counterexample/`.

2585 split-count route: testing #AND>=minimum cover and #OR>=edgecount-1 separately. Defs/AndCountCircuit flattens freeOR regions. ExistingL217 proves cover<=AND only up tocover5 by451KB finitecatalogue; L634 Fano7 is290KB certificate; no generic bipartite bound located. L1006 refutes generalC4free graph cover<=AND using11vertices(two triangles+pentagon),6AND vscover7; nonbipartite so not a refutation here. Counterexampleagent macroSAT independently sanitychecked: arbitrary nonempty free-op aggregates over inputs/earlier counted gates exactly exhaust all circuits, copies allowed. C6 AND<=2 andOR<=4 UNSAT with unlimited opposite-type gates; theta4x4 AND<=3 UNSAT. C12 AND<=5 targeted because29MIS leaves ceil-log lowerbound5 belowcover6, unlike C6/C8/C10. Dual OR problem is AND lowerbound on vertex-cover2CNF; K2,2 factorization is elementary saving obstruction, but absence alone does not yet prove multilevel lowerbound.

UTC 2026-11-25T00:55:56.344047+00:00
### Structural count-route update

- Checked search for matching/fooling-set helpers found16 Outside files, all specialized certificates or plane bounds; no generic C4-free matching-to-AND lower bound.
- The proposed split remains unproved: AND count at least minimum cover (or maximum matching) and OR count at least edge count minus1. Free-OR macro SAT from the counterexample agent verified C6 needs3AND and C12 needs6AND, plus the theta4x4 graph needs4AND. These are finite computational checks, not Lean proofs of the general split.
- Important semantic correction: L_meta_1006 refutes a boundary-only assertion. Its6AND circuit does not compute the full11-vertex graph function. Exhaustive2048-input evaluation found39 mismatches, including missed edges (4,10),(5,9),(6,7),(6,10),(7,9),(8,9). It does not refute full-function AND-cover or AND-matching bounds.
- Matching edges are only a communication fooling set at clean AND gates; a dirty first rectangle may create nonedges that later AND gates filter. An induced matching does yield the standard exponential zero-assignment family and hence the AND bound via L634.proj_count, but a general matching does not supply those independent assignments.

### 2026-11-25T00:56:21.429664+00:00 — least-gate private boundary (certificate_optimization)
Checked `gap-2585/direct/LeastGatePrivateBoundary.lean`, SHA256 `984de15ff09224c0e0357c88123492acc9b8108da9facdd17ddb9aedeec442bb`, Lean exit 0; complete log `least-gate-private-boundary.log`. Extends the private positive-edge witness for every OR operand in a least AO graph circuit with the dual negative-boundary witness for every AND operand. Any cofinal family of negative inputs suffices, including maximal independent assignments. Proof deletes the AND and redirects readers to the chosen operand, uses monotonicity to extend every negative input to the boundary, then contradicts least size. This is a necessary condition for least circuits and safe minimum-count SAT pruning; it does not establish the missing dirty-AND charge.
Read L3706 frontier accounting and residual-cover reductions R2384: existing proof only charges squarefree/read-one edges. Extra missing debt is |U| + tau(G) - tau(G\U); the reductions assume rather than prove its compensation. No unproved cone-disjointness or NF-implies-Read1 claim is being used.

## 2026-11-25T00:57:45+00:00 sibling: conditional refutation machinery compiled

`/tmp/oec/pequalnp-pilot-46/gap-2585/sibling/CoverLowerBoundFull.lean` compiles with Defs only (`lean -j 1 -M 6000`, exit 0, full log `cover-lower-bound-004.log`). 2037 lines, 102060 bytes, SHA256 c427b0a1552ed95907de089a8e0ae078b676dd077b3293b8c0887a366d4c2983. First 1961 lines adapt checked L4897 by namespace rename and dropping redundant Mathlib import; new tail proves matching-cover lower bound and exact negation of L2585 conditional on a correct small AO2 witness. No witness or refutation claimed. Matching size k plus edge count m requires witness size + 1 < m + k. Independent review requested.

The derivative/semi-disjoint literature follow-up is in sibling/LITERATURE.md. It supplies no verified unrestricted size-preserving Boolean cofactor conversion. Lingas-Persson semi-disjointness excludes incidence outputs with repeated endpoint variables; Baur-Strassen is arithmetic and loses a factor up to five.


### Count-search update 2026-11-25T00:58:49.824387+00:00

C12 with at most5AND gates and arbitrarily many OR gates is UNSAT in45.089s. This establishes a finite computational6AND lower bound beyond the elementary29-maxterm bound; not Lean checked. Full CNF/log: `cycle12-macro-topo-and5.*`.

Theta4x4 with at most7OR gates and arbitrarily many AND gates remained unresolved after300.062s, even with private-boundary/copy and topological symmetry constraints. No SAT/UNSAT verdict. Fano6AND search was stopped after~120s without verdict once Structural identified the existing checked7AND lower bound L_meta_634.

Private-boundary SAT constraints permit either both operand-private boundary witnesses or an identical-aggregate copy gate, preserving exact-count padding. Certificate agent subsequently Lean-checked the dual AND negative-boundary lemma in direct/LeastGatePrivateBoundary.lean.

Next search varies the C4-free6x6 incidence graph itself while fixing a diagonal perfect matching and5AND gates, with unrestricted OR regions. Initial2-hot assignments enforce the chosen graph; full truth tables find higher-order false positives, which become dynamic graph/circuit SAT constraints. Script `variable_graph_search.py`; no result yet.

Additional checked components: LeastGatePrivateBoundary proves necessary private positive/negative boundary conditions for gates in a globally least circuit. CoverLowerBound contains the checked read1 cover-cost bound and matching-based conditional refutation adapter. The adapter would turn an actual26gateFano or11gateTheta witness into a refutation; none has been found. These are partials, not a proof/refutation of2585. The source for the current accepted conditional reduction is unchanged.

### 2026-11-25T01:00:09.611115+00:00 — dirty NF finite check
C6 at optimum8 gates with strong NF and at least2 dirty ANDs is SAT-UNSAT (1.571s,496vars4521clauses), recorded in direct/dirty_nf_search.py and direct/c6-size8-nf-dirty2-boundary.log. No Lean UNSAT certificate, hence evidence only. Counterexample agent resumed the sole solver slot. Direct/FINDINGS.md records the exact missing global debt and why unique-dirty lemmas do not iterate automatically.

### 2026-11-25T01:01:05.223085+00:00 structural GitHub census

Fully paginated targeted searches found no new complete2585 proof. PR9697/9707 heads unchanged; read actual126line9659 and81line11141 sources, both conditional reductions with no closed charge. Full report/sources: /tmp/oec/pequalnp-pilot-46/gap-2585/structural/PR_CENSUS.md.

Explicit fresh bot eligibility rejection: https://github.com/open-goat/pequalnp-proofs/pull/11110#issuecomment-7149020857

Closed: this step is not open to reductions (its row in the desk file does not say reductions: true), so this reduction will not be checked. A proof of the step is still welcome. This is an automatic message.

Root re-read Jukna single1.pdf on2026-11-25: Theorem2.4 refutes the generic all-graph AND-count/biclique-cover inequality using saturated non-bipartite matchings. It does not settle the bipartite C4-free case. Historical Problem8.2 asks for explicit superlinear quadratic monotone lower bounds; current global open status remains UNVERIFIED. Source: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf .

### 2026-11-25T01:06:24.685418+00:00 focused biclique/AND route

No new proof/counterexample. Generalgraph biclique≤AND is false by Jukna; bipartiteC4-free case remains unresolved here. Katz low-CNF result is graphrepresentation only; semi-disjoint bilinear methods assume matchinglike outputs. Detailed source distinction and dirtypath obstruction: structural/BICLIQUE_AND_RESEARCH.md.

### 2026-11-25T01:11:02.328261+00:00 — forest gate elimination pieces checked
Within the capped forest investigation, direct/ForestElimAO.lean compiled EXIT0, SHA256 `19d902c7a0af4b85ca07de07c688831acf7091874097ca8e03300321b924df3f`; complete log forest-elim-ao.log. Attributed compiler prefix from L2502→L1543 and operation-count helpers from L2752; new annihilator status, two-gate budget, selected-operation count drop, and exact AO2 shape preservation. Reviewer has frozen source. Earlier checkpoints ForestElim.lean and ForestElimCounts.lean also compiled. Full input-restriction wrapper/path lemma/forest induction are not assembled.
Mathematical forest route in direct/FOREST_ROUTE.md: leaf=0 loses one OR if residual function nonzero; leaf=1 loses one AND since singleton leaf is rejected; then neighbor=0 yields graph minus pendant pair, whose cover number is one less. This plausibly proves the sharp forest bound. Explicit obstruction on cyclic cores: a degree-d deletion removes d edges/possibly d cover contribution but path reasoning guarantees only one corresponding operation, leaving d−1 uncharged. Root requested freeze and preserve before pivot; no running helper process.


### Counterexample strategy frozen 2026-11-25T01:12:01.291017+00:00

No full-function counterexample or Lean proof/refutation was found. Final queued C8 OR-count search is UNSAT76.503s, excluding≤6OR with unlimitedAND. C12 AND-count search had already excluded≤5AND/freeOR in45.089s. These are external SAT evidence only.

Graph-varying6x6/5AND search rejected20 models on full4096-input truth tables; its sorted-degree continuation at344inputs timed out299.14s, so the6x6 question remains unresolved. Relaxed4x4 fooling-set family (other4cycles allowed) at3AND is UNSAT0.31s. Independent scalar fulltruth audit rejected all25 retained candidate models and produced concrete failure assignments.

Evidence archive: `/tmp/oec/pequalnp-pilot-46/gap-2585/counterexample-evidence.tar.gz`,641877bytes, SHA256 `b7a698c677cc833088a6abd8dae642e39df1672762a475c44ded6b2abc349819`.168files include portable scripts, complete stdout/stderr, summaries, models, independent rejection audit, successor cutsets, manifest/inventory and8 small completed-UNSAT CNFs.63 large/regenerable CNFs (~15MB) were omitted with hashes recorded. Five completed macro CNFs regenerate byte-identically under named profiles. Archive content hash audit passed; no solver remains active.

## 2026-11-25T01:41:22+00:00 structural_bound:1342 exact-two-junk sieve and public proof audit

Checked L1490+L2695 close the trace needed for Q>0 or R>0. Combined checked L1491/L4183 forces u2 corner B5,Q0,R1. Python deletion enumeration finds16 tight disjoint edge pairs (not Lean checked). Existing R2260_2 derives full nested u2 witness, closed by checked L5226. Fresh PR11107 is an apparent complete L5228/u3 proof (6482lines, immutable61604cf1), author-claimed checker acceptance not independently verified. L5230 PR10447/10624 are only reductions; no full u>=4 proof found. Detailed sources and report: /tmp/oec/pequalnp-pilot-46/gap-1342/structural/STRUCTURAL_REPORT.md. Route docs absent/404. Reviewer owns1342 live-PR census.

### 2026-11-25T01:45:39.558045+00:00 — constructive1342 dirty-prefix near witnesses
Direct route found5 full-function22gate witnesses with3gate dirty rectangle prefix and19gate continuation; all2048inputs audited, eachhas exactlyonejunk. Data in gap-1342/direct/neutral-units22.json, firstcase unit-prefix22.json. Units are (1∨5)∧(2∨8), (2∨8)∧(4∨5), (0∨5)∧(2∨9), (0∨8)∧(1∨9), (0∨8)∧(4∨9). Each shares a triangle{5,8,9} filter OR with the third-center star, making the CNF substitution cost-neutral. No21gate witness. Full findings and explicit false-triple obstruction for rejected gadgets in direct/FINDINGS.md. Direct Unit22 Lean finite check hit2GiB; sibling owns a faster replacement proof.

### 2026-11-25T01:47:45.627985+00:00 — exact two-junk22 construction
New gap-1342/direct/two-junk22.json computes full target on all2048inputs with22gates,7ANDs, exactlytwo junk{2,7}. Adds wrappedtriangleB block (6∨7)∧(3∨((7∨10)∧(6∨9))) to the neutral shared-filter unit. Toolchain CGP nowusesseed; sibling formalizingfastLeanproof. Earlier one-junk22/tail19 is alreadyLean-checked bysibling. No21gate witness yet.

2026-11-25T01:54:51.478661+00:00

## L-meta-1342 exact local search checkpoint

Counterexample agent: no <=21-gate witness found. All reported candidate audits use all 2048 inputs, with raw and boundary-merged/dead-pruned gate/junk counts separated. The strongest 21-gate, seven-AND, genuine-two-junk near-circuit computes F OR (x9 AND x10), with exactly four false positives. Its <=2-change and <=3-change exact-two-junk SAT repair neighborhoods are UNSAT (1.373s and 21.838s). The genuine two-junk22 construction has no <=3-change repair after any of 32 allowed non-unit gate deletions/reconnections with both dirty units fixed (UNSAT42.530s). Six-AND/free-OR/exact-two-junk synthesis with first dirty AND among five neutral units is UNSAT9.493s; unrestricted six-AND synthesis timed300s. These are limited ordinary SAT exclusions, not Lean certificates or exhaustion of the assigned shard. Final four-change queries remain in progress at this checkpoint. Full logs, CNFs, scripts, scope and replay details: /tmp/oec/pequalnp-pilot-46/gap-1342/counterexample/FINDINGS.md. Positive known22 and negative incorrect21 fixed-circuit encoder controls passed.

2026-11-25T01:56:36.693338+00:00 L1342 exact-search freeze: final row39 and two-junk22 deletion four-change queries both timed180s. No witness and no solver active. Complete74-file evidence archive /tmp/oec/pequalnp-pilot-46/gap-1342/counterexample-evidence.tar.gz; SHA25694b231f9f791ece73b9c282a3215ea1f91f7052500d1fe497ca9aaa1c1590178; internal hash audit PASS. Includes full CNFs, stdout/stderr, scripts, seeds, controls and precise scope. Ordinary SAT exclusions only, not a Lean proof.
