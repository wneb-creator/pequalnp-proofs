# Independent mathematical and format audit

Reviewed 2026-11-25. No definition-level counterexample found. FanInTwo restricts every listed gate to AND/OR/NOT and <=2 inputs; Circuit.size counts every listed gate, including NOT; missing wire reads are false; NOT ignores its optional second input. The 15 posted edges are the standard Petersen graph, with ten distinct input variables. Extra unreachable NOTs do not create a shortcut because they consume size.

## Exact reusable checked components

- `lean/PEqualNP/Outside/L_meta_4725.lean` (3224 lines) proves exactly: every FanInTwo circuit computing Petersen has `15 + NotBracket.notCount C <= C.size`. This is the first premise of existing reduction R_meta_2592_271. Under size<=19, only one through four NOT gates remain.
- `lean/PEqualNP/Outside/L_meta_6194.lean` (3255 lines), helper `petersen_binary_lower`, proves the same non-NOT floor using circuit normalization, six branching wires, and a finite graph mask argument. L_meta_5238 and L_meta_8127 contain duplicate machinery.
- `lean/PEqualNP/Outside/L_meta_8039.lean`, helper `binaryFloor` at line4187, is stronger than its exported theorem: the nine-input Petersen-minus-vertex function needs >=14 non-NOT gates. This can support a restriction argument. Exported theorem rules out total size15 with exactly2 NOTs.
- `lean/PEqualNP/Outside/L_meta_8033.lean` proves the same nine-input function needs >=15 total gates. Its file is7136lines, so copying full machinery may exceed the512KiB limit.
- Assigned imports permit only PEqualNP.Defs (and Mathlib), so Outside helpers must be adapted into our own namespace; direct Outside imports are prohibited.

## Existing reductions and remaining difficulty

All three reduction slots are already occupied: R_meta_2592_271 (binary floor +1..4 NOT cases), R_meta_2592_318 (last-NOT cut + separator bound), R_meta_2592_408 (normalization + bounded legal circuit rejection). R_meta_4727_17 and R_meta_4727_53 reduce the1..4 NOT subcase to semantic gate-list or signed-binary-circuit lower bounds. None of these reductions alone proves the assigned statement.

A plausible structural route is vertex restriction: nine-input Petersen-minus-vertex has >=14 binary gates and >=15 total gates. To reject a19-gate ten-input circuit one needs a provable restriction cost of>=5 total gates, or a suitably stronger argument at the boundary. This is an unproved strategy, not a lemma.

## Final red-team requirements

Helpers inside the assigned module namespace or its _aux namespace; final theorem fully qualified and last. Exactly one added regular UTF-8 Lean file <=512KiB in the final PR diff. No _root_ text, double quotes, forbidden commands/words, new axioms, sorry, native_decide, or unsupported attributes/options. Imports contiguous at top; exact desk statement. Local check-lean acceptance does not alone establish the separate PR-format requirements.

## Partial-draft review

Independently inspected PetersenBinaryFloor.lean (145926 bytes) and LastNotCut.lean (3308 bytes). Static review passes for authorized branch-only partial preservation, contingent on successful compilation. No final L_meta_2592 theorem is claimed. BinaryFloor differs substantively from upstream L_meta_4725 only by namespace adaptation and sound counting consequences; four local simp attributes and two permitted limit options remain. LastNotCut correctly models the final NOT using the prefix output wire and passes all prefix wires into the suffix; empty NOT inputs use a deliberately invalid prefix output index, which evaluates false before negation.

Full static scan: /tmp/oec/pequalnp-pilot-121/partial-red-team.txt. Full adaptation diff: /tmp/oec/pequalnp-pilot-121/binary-floor-adaptation.diff.

The nine-input14-binary lower bound alone does not automatically exclude3/4 NOT gates. For total<=19 and N NOTs, a false-vertex restriction must save at least6-N binary gates:2 forN=4,3 forN=3,4 forN=2,5 forN=1. First-gate removal alone saves onlyone. A first AND containing a primary input may propagate false through another binary gate, while a first OR under false restriction merely becomes a copy. An unconditional elimination argument remains to be proved.

## Kneser graph constructive angle

Use the independent Petersen vertex set {0,2,8,9}. Write a1=x0, a2=x2, a3=x8, a4=x9 and p=x6, q=x7, r=x3, s=x4, t=x5, u=x1. Define:

- c1 = s OR t OR u
- c2 = q OR r OR u
- c3 = p OR r OR t
- c4 = p OR q OR s
- H = (p AND u) OR (q AND t) OR (r AND s)

The exact posted function is H OR (a1 AND c1) OR (a2 AND c2) OR (a3 AND c3) OR (a4 AND c4). This is the K5 matching characterization: the a variables form a four-edge star; the six remaining variables are K4 edges. The c_i are the triangles avoiding vertex i; H is an internal matching of size two.

A simultaneous circuit for c1,c2,c3,c4,H with <=11 gates and at least one NOT would yield a19-gate counterexample after adding four AND and four OR gates. The direct monotone construction costs13 auxiliary gates and21 total. The known20 construction instead uses the six-vertex cover and orients the three internal matching edges. This focused64-row,5-output synthesis request was sent to circuit_search.

The profile-search lower bound for c1..c4 alone was independently reproduced using all14 non-XOR binary Boolean truth tables, allowing free constants and free complement. No circuit using <=7 binary gates survives the seven-row abstraction; all0..3-extra-profile subsets were checked (1,53,1378,23426 cases). This prevents the simplest shortcut of generating just the four c_i more cheaply, but does not rule out sharing with H.

## Additional partial reviews

BracketWitnesses.lean reviewed again after Bool-order proof repairs and reported successful compilation. Frozen SHA256 d63099b3262a1efc22a96f6d9bce56f98d49be498988f8c369b547465d2a292d approved for immediate partial preservation. Elimination.lean also passes static review: its finite certificate explicitly checks closure and a missing target, so it does not depend on proving that seven iterations reach a fixed point. Neither result establishes the whole Petersen lower bound.

## Generic profile pruning

ProfilePruning.lean compiled successfully under pinned Lean4.36.0. Its independent reviewer proof_route approved frozen SHA256 f0c75432b495610abbef42877460111856cc84ea56032450d60ffad43fdc3307. It defines a generic construction trace whose step relation is monotone in available values, then removes duplicate and initial-seed outputs. Pruned traces remain valid, preserve all output coverage, contain distinct values outside initial seeds, and never grow. If any trace output is already an initial seed, pruning strictly shortens the trace. This supplies the extra one-gate saving required for auxiliary H, whose seven-row profile is constantzero.

The full auxiliary family therefore needs at least9 binary gates once connected to the profile certificate: four OR outputs require8 productive binary profiles, while the nonconstant H output requires a binary producer with initial-seed profile. An11-gate auxiliary witness can have at most2 NOT gates. This remains a mathematical deduction pending the actual circuit-to-profile connection.

Additional independent final-byte approvals: EliminationSound SHA2566b34a3d59df3101cd32166aa655bf1c2b61ef1749dbc36c3ced8ad83e8f9c932; EliminationBound SHA256bd8385aa5a11b5196b5d128af831366d950fa78273693317624e66f1dd20c16b. The latter uses cardinality to show any build covering four targets has at least8 entries, conditional on checked=true. It explicitly handles duplicated and initial-seed entries.

## Optimal eight-profile census

An independent C++ enumeration checked all292825 sets of four nonseed/nontarget helper profiles on the original seven rows. Exactly81 are constructible, exactly the3^4 expected choices of one pair-OR helper per triangle. A separate dependency audit of those81 sets found no alternate construction rules: each triangle target requires its own pair helper plus remaining primary input; before that target exists, the pair helper must be generated from its two primary inputs. Evidence files: scratch/gate-elimination/profile-eight.stdout, profile-eight-dependencies.stdout; reproducible C++ source profile_eight.cpp. This is computational evidence, not a Lean certificate.

## Eight-row cover-ledger audit

Independently audited block_cover_rows.py with argument0,1 and reran it successfully. Rows are zero, six singleton core assignments and the nonmatching pair{0,1}; the internal matching function is false on every row. Its17 cells are the zero coordinates of the four triangle profiles. All256 raw block masks are enumerated, yielding61 useful canonical blocks; complement collisions are asserted to agree on coverage. Recursion branches on all blocks covering a selected uncovered cell. The lower-bound prune uses current block count, a valid remaining-coverage count, and the number of distinct already-required nonseed profiles. The core synthesis search exhausts signed-AND gates with free complement and constants; when remaining slots equal the number of missing goals, excluding auxiliary-profile steps is sound.

Independent rerun: answerNone,212443 cover states,40266 core checks,2.55seconds, exit0, empty stderr, no timeout. This supports the abstract ledger obstruction at budget11. It does not itself prove that every Petersen circuit yields that ledger; the port and circuit bridge remain necessary. Full rerun saved in scratch/gate-elimination/block-cover-review.stdout and .stderr.

## Completed budget12 cover census before lease pause

The complete budget12 search has exactly one feasible state pattern:4 selected blocks, required nonseed keys(51,85,105,112), and8 binary synthesis gates. The census explored765883 cover states and691433 core-build states in16.55seconds with no timeout. This confirms tightness of the budget11 obstruction and the unique optimal cover pattern. Full output: /tmp/oec/pequalnp-pilot-121/gate-elimination/block-cover-census12.stdout and .stderr; script block_cover_census_12.py.

This does not yet exclude3 NOTs: the current TerminalTen proof guarantees the four terminal variables only for nonNOTcount<=15. Extending terminal structure at count16, or locating an additional matching-output cost, remains unproved.

Urgent final-byte review of compiled ProbesTen approved SHA25672c53a03fb42380d6cbc5553accf1715dd20bd34a4b96cf9c44b9283623f9333. Its no_ledger conclusion explicitly assumes the finite noCover lemma; no unconditional full lower bound is claimed. The8-row fixture and cover cells match the independently audited finite search. Research paused on root notification of desk410.
