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
