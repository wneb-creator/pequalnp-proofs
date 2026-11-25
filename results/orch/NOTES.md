# L-meta-4675 shared notes

Assigned 2026-11-25 17:06:33 UTC. Only root controls lease and submissions.

Exact statement: /tmp/oec/pequalnp-pilot-161/statement.txt
Desk data: /tmp/oec/pequalnp-pilot-161/desk-answer-001.json

Append findings under strategy name; keep Lean experiments in results/orch/lemmas or scratch. Final proof adds only lean/PEqualNP/Outside/L_meta_4675.lean.

## Counterexample strategy (17:08 UTC)

No initial definition loophole: `IsAO2` requires AND/OR, exactly two earlier inputs. Missing outputs only compute false (then E empty, empty cover works). OR reach resets to empty at AND gates, so an idempotent AND copy can hide a colour for one gate; finite search will preserve this possibility. Local Python lacks z3/pysat; sympy/numpy available.

## Toolchain setup (17:09 UTC)

The claimed warm environment was absent: no elan/Lean binaries, prepared marker or lean/.lake. Verified the repository-pinned elan v4.4.0 installer SHA256 and installed it into `/tmp/oec/pequalnp-pilot-161/elan`. Installing pinned Lean v4.36.0 binary release, then root can fetch Mathlib cache. No repository source files modified.

## Normalization strategy (17:13 UTC)

- `tCount = 0` forbids only syntactic OR paths to both input colors. It does not imply every gate has one-color singleton support: `(x AND x) OR (y AND y)` has empty OR-reach at its OR and accepts both singleton inputs. Any normalization must pay for those masking ANDs.
- Existing `L_meta_4897` proves the exact bipartite edge+cover size bound under ReadK.IsReadK 1 (about 1,960 lines). Read1 is not immediate from tCount=0; `(x AND x) AND y` refutes direct implication. Need size-nonincreasing simplification or a new charging argument.
- General LowerPart helpers address one dirty AND at a time under strong least-circuit/lift-normal assumptions, not a global size-preserving cleanup.

Toolchain ready: Lean 4.36.0 and Lake 5.0.0 verified. Set `ELAN_HOME=/tmp/oec/pequalnp-pilot-161/elan` and prepend `/tmp/oec/pequalnp-pilot-161/elan/bin` to PATH. Root notified to run `lake exe cache get` from lean/.

## Lemma inventory (2026-11-25 17:12 UTC)

- Exact word-boundary search for `tCount` / `IsTwoColour` finds only `Defs/TwoColour.lean` and `Outside/L_meta_4791.lean`. No existing direct lower-bound theorem uses the new tCount predicate. Beware searching `tCount` without boundaries also matches `notCount` and produces hundreds of unrelated files.
- `Outside/L_meta_4791.lean` (1414 lines): normalization to tCount=0 with size bound `D.size + 4 <= 6 * C.size` for arbitrary singleton-off AO2 C. In particular the new class still subsumes general edge-circuit complexity up to factor six. Useful helper API: `mem_orIn` 708; `orIn_self` 716; `orIn_up` 719; `orIn_reach` 728; `orIn_val` 737; `q91_reach` 1298; zero-colour proof `q91_fin_tc` 1324.
- `Outside/L_meta_2235.lean` (1771 lines): `main_aux` 1759 proves `E_read1.card + T.card <= C.size + 1` for read-once accepting edges; `core` 1638 isolates the counting assembly. `s2230` extracts a top AND for each read1 edge; `s2231` gives star shape by C4-freeness and a vertex cover; `s2233` counts top AND gates <= top OR gates+1; `s2234` charges summed star leaves to lower OR gates plus tops. All are adaptable from source, not importable under the desk allowance.
- `Outside/L_meta_2237.lean` final theorem 1877: exactly graph edge bound for NoFourCycle AO2 circuit with additional `ReadK.IsReadK n C 1`.
- `Outside/L_meta_4897.lean` final theorem 1929: bipartite version with split cover A,B and `E.card + A.card + B.card <= C.size + 1`, again ReadK=1. Compact conversion helpers at lines1880–1924: `cross`, `graph`, `noRectangle` (Fin.addCases + simp), `counts` (edge injection); exact graph-function conversion at1934–1946.
- `Outside/L_meta_8933.lean` final1469 gives graph edge bound assuming no dirty AND gate accepts two distinct nonread1 edges. tCount=0 does not visibly imply this because duplicate singleton AND masking makes many edges nonread1.
- `Outside/L_meta_8545.lean` final448 constructs monotone star-cover upper bound `|E|+tau-1`; helps show intended exactness only, not lower bound.
- `notes/note-1-edge-function-exact-size.md` describes proved special cases: forests, cycles, long-thread graphs. It explicitly distinguishes unrestricted C4-free general case from known single-level/formula bounds. No direct full lower bound found.
- Only Defs and Mathlib can be imported, so outside/helper proofs must be adapted into permitted namespace in final single file. No Lean files modified by inventory agent.

### Finite counterexample checks (17:09 UTC)

Exact C++ exhaustive search stores every wire as its complete truth table and OR-reach colour set. AND resets colour to empty; OR unions colours and mixed colours are forbidden. Duplicate signals with identical truth/colour may be eliminated; independent adjacent gates are canonically ordered. No counterexample for all 14 nonempty C4-free 2x2 graphs through 3 gates, all 53 2x3 graphs through 4 gates, and all 188 2x4 graphs through 5 gates. Each range covers every gate count below the claimed bound for those graph dimensions. Code and complete logs are `/tmp/oec/pequalnp-pilot-161/counterexample-search.cpp`, `counterexample-2x2.log`, `counterexample-2x3.log`, `counterexample-2x4.log`. All 333 C4-free 3x3 graphs through 7 gates are running. Empty graph is trivial, and one-side-size-one graphs obey the ordinary input-support lower bound. These are computational evidence, not Lean proofs.

## Combinatorial strategy (17:15 UTC)

- Syntactic `tCount = 0` does not force semantic singleton supports to be monochromatic: AND buffers erase OR reach. A direct homogeneous-support induction is invalid.
- The clean-circuit counting theorem in `L_meta_7649.lean` proves a star-cover cost bound, assuming every non-output-below gate is OR and its children are also not below output. Lines 570 onward give the rectangle-to-star argument; main proof starts at 805. This can be copied if a suitable normalization is obtained.
- Drafted `results/orch/lemmas/Rectangle.lean`: rectangle cardinal bound, choice of a star center, cardinal identity, and a family-cover theorem yielding a vertex cover of size at most the number of rectangles and total cost bound. Awaiting toolchain to check.

- 2026-11-25T17:11:39.001937+00:00: Rectangle.lean checked successfully with pinned Lean v4.36.0; all four lemmas accepted, no diagnostics. Command: explicit scratch lake env lean ../results/orch/lemmas/Rectangle.lean from lean/.

### Normalization formal partial

`results/orch/lemmas/Masking.lean` (uncompiled until toolchain arrives) formalizes a useful charging prerequisite: every true wire has either a true input in its OR-reach or a true AND in its OR-closure. Thus a tCount-zero OR that accepts singleton inputs of both colors has an AND witness in its OR-closure accepting a singleton. If the output rejects singletons, this witness is a dirty AND (not below output). Existing wire-fold and OR-reach helper proofs were copied into the required own namespace from L_meta_7649 and L_meta_4791, with no new project dependencies.

`Normalization.lean` isolates the simpler monochromatic OR-reach facts and finite masking examples. Neither file claims the posted gap theorem.

## Support partial compiled 2026-11-25T17:13:30.071269+00:00

`results/orch/lemmas/Support.lean` (201 lines) compiles with Mathlib + PEqualNP.Defs only. Namespace `PEqualNP.Outside.L_meta_4675.Support`; final lemmas `essential_card_le` and `incident_card_le`. Hash de3b61906d0bb6a82a44dfcf95b41e71d07514e7e5037daa7799ff93bb8bfda6. Bare fan-in at most two suffices; no AO or ReadsBack needed. Full Lean output is empty at `/tmp/oec/pequalnp-pilot-161/support-build.log`.

Normalization/Masking compiled successfully at 2026-11-25T17:13:47.932649+00:00. Build logs: scratch normalization-lean.log and masking-lean.log. Only unnecessarySimpa warning; all finite masking examples kernel-checked with decide. Masking now includes prior_wire_singletons_same_colour (before first dirty AND all wire singleton supports are monochromatic).

## Star partial compiled 2026-11-25T17:15:55.213887+00:00

`results/orch/lemmas/StarNext.lean` (335 lines) compiles with Mathlib + Defs only; includes unchanged Support source plus Star.row_incident_card/row_bound/column_incident_card/column_bound. Both star orientations prove the exact target cover conclusion, using only fanin<=2 and computed edge-function equality. No C4-free, AO2, or tCount hypothesis required in these special cases. SHA256 fa00116fb39a56e38f5c5be45e0a2fd7bf2ddd7d4bcc9d0131486acd32af56fa. Lean output empty, exit0: `/tmp/oec/pequalnp-pilot-161/star-next-build.log`. Row-only Star.lean remains stable at271 lines.

## First dirty AND classification (2026-11-25T17:17:07.757241+00:00)

`FirstDirty.lean` compiled successfully. `first_dirty_pair_witness` proves: under AO2 and exact edge-function behavior, if all earlier ANDs are below output but gate g is not, then there are vertices a,b in its two child OR-reaches such that g is true on pairInput a b while output is false. Thus the earliest dirty AND always has a witness of size at most two. This does not require C4-freeness or tCount.

Correction to an attempted simplification: on edge inputs, earlier BelowF ANDs need not vanish; replacing a same-colour first dirty AND by the OR of intersected child supports may lose carried edge terms. The exact OR-reach characterization applies only to rejected inputs.

### Counterexample search complete on six inputs (2026-11-25T17:17:14.265965+00:00)

3x3 exhaustive search completed: 333 nonempty C4-free edge sets; 9,281,809,818 canonical depth-seven extensions; no violation, 299 seconds. Together with 2x4 and trivial stars this covers all bipartite graphs on at most six inputs below the claimed bound. Full log: `/tmp/oec/pequalnp-pilot-161/counterexample-3x3.log`.

Split-bound evidence: exhaustive 2x3 through5 gates has AND >= tau and OR >= edges-1. Native `libz3.so.4` is available through ctypes despite absent Python bindings. `/tmp/oec/pequalnp-pilot-161/freegate-synth.py` tests one gate count with the other type free: AND operands become arbitrary ORs of prior AND outputs and raw inputs of a single colour; OR operands become arbitrary ANDs of inputs/prior OR outputs. Repeated functions and AND input buffers are allowed. Positive edge assignments plus all maximal independent-set negative assignments exactly characterize the monotone edge function. C6 with at most4 ORs and arbitrary ANDs: UNSAT (no colour restriction, hence stronger); theta(3,3,3) with at most3 ANDs and arbitrary tCount0 ORs: UNSAT. Theta OR7 and Fano AND6 underway. These are exploratory solver results, not Lean proofs.

- 2026-11-25T17:19:49.416257+00:00: `FirstDirtyClass.lean` compiled (603 lines, SHA256 ff8e6d730c08495d308a6e3f3ff3d9aa26045fe3fb77ec2366ca57baa56abbaf). Adds `and_below_iff_cross_pairs`: after a clean prefix, an AND is BelowOutput exactly when all cross pairs of its two child OR-reaches are accepted. This yields the exact first-dirty classification, but not a global gate charge. The two files share frozen normalization helpers; retain only the latest if consolidating.

## Star forest partial compiled 2026-11-25T17:21:38.951423+00:00

`results/orch/lemmas/StarForest.lean` (282 lines, including unchanged201-line Support) compiles with Mathlib + Defs only. `StarForest.endpoint_card_le` gives the bound on the sum of distinct point and line endpoints. `point_degree_one_bound` proves the exact target conclusion if Prod.fst is injective on E, using all nonisolated lines as cover; `line_degree_one_bound` is symmetric. Only fanin<=2 and computed edge-function equality needed. SHA256 fb1028deed3b55fd1749a1aea16aefc03676099ba35a46495f78f148156329bd. Lean exit0, no diagnostics (`/tmp/oec/pequalnp-pilot-161/star-forest-build.log`). Source stable.

## Restriction/rank strategy (2026-11-25T17:22:52.459285+00:00)

Candidate split is OR-count >= |E|-1 plus AND-count >= tau. Neither is proved. Ordinary real matrix rank cannot imply tau: the C8 bipartite adjacency matrix has rank 3 but matching/cover number 4. Point restrictions give a pairwise-linear family of neighbor ORs, but one circuit OR gate can serve two distinct rows: `RowSharing.lean` is kernel-checked and demonstrates this on the C4-free path with 2 point inputs, 3 line inputs, 4 edges. The 6-gate circuit is a=x0 AND y0; b=x1 AND y1; c=a OR b; d=c OR y2; e=x0 OR x1; output=d AND e. Gate d becomes y0 OR y2 on row0 and y1 OR y2 on row1, although its syntactic OR reach is only {y2}. An extra AND supplies this sharing, so row counting needs an explicit AND credit. This is not a counterexample to the posted theorem.

Boolean equality also implies equality of the corresponding min/max lattice polynomial by thresholding: target becomes max over edges min(vertex weights). A comparison-network adversary might supply a separate route, but no invariant yet handles reuse of selected values. No general lower bound is being assumed.

### Additive buffering conversion (compiled)

`Buffering.lean`, namespace `.Buffering`, proves additive_buffering: any IsAO2 circuit on n inputs has an equivalent IsAO2 circuit of exactly size+n with tCount=0 for every coloring. Construction prepends n AND[i,i] gates and shifts every old wire by n. Full wire-list invariant is D.wires xs = xs ++ C.wires xs. All old OR inputs now name gate wires, giving empty orIn at every gate. Compiled cleanly (exit0) at 2026-11-25T17:23:01.563928+00:00. This is a conversion/partial, not the target lower bound.

## Root: one-sided buffering idea
Buffer only all point inputs, leaving raw line inputs unchanged. Original OR reaches then contain only lines, so T=0 with p extra AND gates (symmetrically l). This strengthens the n-buffer construction; normalization agent formalizing. For tau=p on balanced graphs, the target would imply arbitrary AO circuit size >= |E|-1.

### One-sided buffering (compiled)

`OneSidedBuffering.lean` extends the frozen Buffering foundation in the same namespace. `one_sided_buffering` proves an equivalent IsAO2 circuit for a p+l input circuit, with overhead p only, and tCount zero for the point/line split. Only point inputs receive identity AND buffers; raw lines remain directly readable. Prefix relocation is oneMap, with all mapped old gate input indices at least p. Compile clean exit0 at 2026-11-25T17:26:30.194679+00:00. This sharpens the full n buffer conversion; does not prove the requested lower bound.

### Exact min/max translation compiled (2026-11-25T17:27:06.449520+00:00)

`Lattice.lean` (99 lines) proves threshold commutation for the original AO2 circuit DAG evaluated over natural numbers with AND=min and OR=max. Its `edge_value` lemma derives `natFun C x = E.sup (fun e => min (x point(e)) (x line(e)))` from the exact Boolean edge-function semantics. No C4-freeness or colour hypothesis is needed; no gates are changed or duplicated. This gives a rigorous comparison-network formulation. Complete Lean log is scratch/lattice.log (empty, exit0). This is a bridge, not the missing gate lower bound.

## Independent computational review 2026-11-25T17:27:59.656826+00:00

lemma_inventory reviewed exhaustive C++ pruning, free-gate SMT encodings, archived input restrictions, graph/isomorphism coverage and four SAT controls. No flaw found in main reported scopes. Important caveat: synth.py exact irredundant-size UNSAT is not automatically <=k; author added caveat. Exact SMT inputs/stdout and hashes were initially missing from archive and now included. Full review: `/tmp/oec/pequalnp-pilot-161/SEARCH_REVIEW.md`; small independent checks: `search-review-small-validation.txt`. All results remain exploratory, not Lean verification or certified UNSAT.

### Clause-set obstruction and existing AND results (2026-11-25T17:31:01.467415+00:00)

The one-side-per-AND choice representation in `L_meta_217` gives vertex-cover clauses C_q and avoidance sets Z_v={q:v not in C_q}. Exact graph semantics implies this avoidance family is 2-Helly. Without dependencies the sets are subcubes; dependencies break this even under tCount0. `RowSharing.lean` now kernel-checks exact clause semantics and `avoidance_not_cube_convex` for its P5 circuit: Z_y0 is {q_out=right} union {q_out=left,q_a=x0}. Its cube hull is the whole cube, so taking hulls erases a real edge. An attempted cube-rank proof must address this obstruction.

Additional existing results: `L_meta_217` proves C4-free AND-count>=t for t<=5 (finite classification), `L_meta_634` proves Fano >=7 AND gates in the free-OR model, and `L_meta_1898` proves PG(2,3) >=13 AND gates under its listed tests. `Defs/AndCountCircuit` is the relevant free-OR model; `L_meta_4682` contains conversion machinery. General AND>=tau has not been obtained here.

The C8 rational-rank obstruction was independently computed in scratch/rank-obstruction.py: rank3, tau4, no rectangle, explicit perfect matching4. Full output saved in rank-obstruction.log.

## AND-count investigation 2026-11-25T17:31:25.198182+00:00

Nested agent and_count: no general proof of AND-count >= minimum vertex cover obtained. Global false-child choices at AND gates give at most 2^k maximal false assignments; this proves the needed AND count for C6 (5 maximal independent sets) and K4 incidence (12), but only 6 for Fano (37, versus cover number 7). The profile machinery is already formalized in L_meta_217 lines 2544 onward; its final theorem proves the C4-free AND bound only for cover threshold t <= 5, by a 361-graph finite catalogue. No generalization is assumed.

The one-junk TopForm classification supplies an AND-only corollary: if every clean top accepts a star on edge inputs, choose one centre per top; if a nonstar top exists, the exceptional two-column decomposition supplies one additional star after setting the junk gate false. Same-colour sole junk produces reader pair graph (P union (A intersect B)) cross Q, always a rectangle/star. This remains conditional on TopForm plus at most one dirty AND.

OneJunkGraph.lean compiled cleanly (48 lines, SHA256 15ec6c3278bfa5f854ae6f45086da8a6a73fd6080d48b8ff7ca726f91fd7e92f). It proves two_column_edges, the exact exceptional-edge decomposition inside A cross {b0,b1}, and cross_triples_iff, the universal-neighbour classification for a dirty rectangle times a same-side input sum. These overlap parts of the stronger ReaderCharge work, so consolidate if useful. Complete compile log: /tmp/oec/pequalnp-pilot-161/onejunkgraph-build.log (empty; Lean exit0).

## Combinatorial agent: nonstar reader shape and semantic star restoration

ReaderCharge.lean (89 lines, Lean exit 0, empty log) proves: for a sole dirty rectangle A×B and a productive nonstar reader `(g OR P) AND Q`, C4-freeness and the exact productive condition force B={b0,b1}, P={b0}, A intersect Q={q0}, and E inside A×B equals A×{b1} plus the exceptional edge (q0,b0). The condition used is Q×P subset E and every a in A,b in B,q in Q satisfies E(a,b) OR E(q,b). Exhaustive checking found 180 such configurations across all 334 C4-free 3×3 graphs, zero violations.

RestoreStar.lean (Lean exit 0, empty log) gives the gate-independent semantic consequence: if F0 is monotone, lies below the graph function, preserves all edges outside A×B, and preserves exceptional edge (q0,b0), then the full graph function equals F0 OR the star A×{b1}. For the proposed circuit transformation, F0 is C with g forced false. The exceptional edge survives via selected reader b0 AND Q; TopForm supplies its OR-only path to output. Forcing g false removes its AND gate and at least one OR blending g with P, paying for a replacement star AND plus output OR. Normalization agent is implementing the generic false-prune compiler.

This is partial progress, not a proof of L-meta-4675. Multiple dirty gates remain the main gap: forcing the earliest dirty rectangle false can remove an arbitrary C4-free subgraph inside that rectangle, while downstream dirty gates filter its bad pairs. The single-reader classification does not directly apply through such a dirty region.

AND-count follow-up 2026-11-25T17:33:50.003487+00:00: accepted L_meta_634 proves the Fano incidence AndCountCircuit minimum exactly 7 by a finite no-model argument; the weaker certificate-count bound does not indicate an open Fano AND problem. L_meta_1898 similarly proves AND-count at least 13 for PG(2,3) under positive-edge and selected maximal-independent negative tests. Counterexample agent notified to avoid duplicate Fano AND synthesis. ReaderCharge.lean independently reviewed against exact hash a06690c2574cd367c0cef3c7e4454479ac43378bd12b3916ee78e5942426f671 and approved as a conditional partial graph lemma; its assumptions do not contain its shape conclusion.

### Matching consequence compiled (2026-11-25T17:34:41.474286+00:00)

`MatchingConsequence.lean` (59 lines) proves `cover_card_of_matching`: an injective matching from all p points into lines forces every endpoint cover S to have p<=S.card. `size_overhead_cancels` then cancels the one-sided buffering overhead p from an assumed target cover inequality, yielding |E|<=s+1 for original circuit size s. Combined with checked one_sided_buffering, a proof of the posted target would therefore give the unrestricted AO lower bound |E|-1 on every C4-free bipartite graph with a point-saturating matching. This is a conditional consequence, not a proof of the target. Full Lean output empty, exit0, scratch/matching-consequence.log.

Research source read directly via curl on 2026-11-25: https://pequalnp.com/papers/note-1 section7. The site attributes to Jukna Problem24 an open explicit superlinear bound for general monotone graph functions, distinguishing its restricted-model lower bounds. Underlying cited papers were not independently read here; no current literature-resolution claim made. Full page saved scratch/note1-page.html and note1-page.txt.

### Whole conditional implication (2026-11-25T17:35:43.425165+00:00)

`TargetImplication.lean` (430 lines) combines frozen OneSidedBuffering and MatchingConsequence with the EXACT desk statement as a proposition `Posted`. Its checked `posted_implies_edge_count` states that Posted implies |E|<=C.size+1 for every unrestricted AO2 circuit computing a C4-free bipartite edge function with a point-saturating matching. No tCount hypothesis is imposed on C. The proof applies Posted only to the constructed buffer D, then cancels the matching lower bound on the cover against the p added gates. The result is conditional on Posted and does not establish Posted. Compile exit0 with empty scratch/target-implication.log. Latest RowSharing source is 64 lines, Lattice99, MatchingConsequence59.

## Combinatorial agent: remaining one-junk cases

SameColourCharge.lean is a checked 38-line graph lemma for the same-colour case. Let g=(OR A_points) AND (OR B_points), I=A intersect B. If |I|>=2, every productive reader has a pure-line OR support Q. The lemma proves all reader Q sets lie in one singleton {b}, and either all A or all B are neighbours of b. Consequently force g=false and restore H AND b for one existing operand H (A or B). All lost positive pairs lie in I×{b}; any newly added pairs H×{b} are valid edges. A live forced non-output gate and its first downstream consumer both disappear during false-pruning, paying for a new star AND and output OR. If I is empty, force g=false with no restoration; if |I|=1, alias g to the unique point. The latter needs trimming dead gates and proving no useful OR cone mixes g with raw line inputs: a subsequent productive AND would otherwise admit a one-colour false positive. Counterexample agent independently checked this reasoning on paper.

For opposite-colour g=(OR A) AND (OR B), the checked ReaderCharge/RestoreStar handle a nonstar productive reader. If all productive reader footprints are stars and |A|,|B|>=2, every point-oriented reader carrying g has a unique full-row centre a0, shared across all such readers by C4-freeness. For a reader (g OR P_lines) AND OR Q_points, if |Q|>1 then P must be empty (otherwise its footprint is nonstar), and its AND can become a0 AND OR B. If Q={a0}, replace g by OR B throughout its line-colour OR cone. Symmetric column readers use OR A. T0 prevents nonempty raw-support OR cones from serving both orientations; g-only OR nodes can alias away. This suggests a gate-count preserving clean rewrite, but no circuit compiler for this contextual retargeting has been proved.

If |A|=1, say A={a0}, choose a missing edge (a0,b) inside the dirty rectangle. Any productive line-oriented reader forces its pure-line support Q to consist entirely of neighbours of a0, by evaluating {a0,b,q}; replacing g by raw a0 through point-colour cones is therefore safe. Point-oriented readers cannot have a0 in their pure-point support, so g contributes no positive edge pair there and may be deleted from line-colour cones. The symmetric |B|=1 case is analogous.

These are one-junk proof routes only. The full multiple-dirty lower bound is still unresolved.

## OR-reach API compiled 2026-11-25T17:39:53.553060+00:00

`results/orch/lemmas/OrReachAPI.lean` (291 lines) compiles, SHA256 2f9e74db9b2e6216aa75b81fe91e753c44833249346bbb161927be2ba56e14a0. Namespace `.OrReachAPI`. New API: `orIn_input`, `orIn_non_or`, `mem_orIn_or_iff`, `orIn_or_pair`, `orReaches_append_prefix`, `orIn_append_prefix`. Arbitrary append preserves orIn below n+oldGateCount, without ReadsBack. Basis is the OR-closure portion of checked MaskingNext, extracted into own namespace, no unallowed imports. Full build output empty at `or-reach-api-build.log`; frozen copy `OrReachAPI-frozen.lean`. Normalization agent uses this for tCount-preserving pruning.
