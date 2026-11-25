# Amplification implementation and peelability review

## Existing-wire helper amplification

Independent preservation verdict: PASS for `gate_elimination/reusable_helpers.py`, SHA256 `093cf1a173360aa38b62957c200e7243a06b2476dcea94bd3f12496dbc9bbe9a`, and the saved results within their stated search domain.

Full truth masks encode assignment x at bit x; singleton support is correctly read at bit 2^i. Normalization aliases only exactly equal full truth functions, and a direct two-input replacement is used only when it has exactly the same truth mask. Every retained canonical record depends on earlier canonical records or old inputs. Cone bitsets use original gate positions as unique record identifiers, so their union counts each required gate once, including helpers outside the output cone. No unused raw-genome gate is charged merely because it appears in the original file.

Helper selection checks singleton support size at least two, compatibility with component colorings, at most one selected support neighbor at each old vertex, and the exact pointwise absorption inequality h<=F OR OR(S). The reverse inequality OR(S)<=h follows from monotonicity and is also directly asserted against the full truth mask. Multiple selections have pairwise support intersections at most one and are subjected to a fresh coloring of the entire augmented graph, correctly ruling out inconsistent component flips.

The subset objective is `old_m+old_tau-1 + sum(|S_i|-1) - size(union of required cones)`, exactly the predicted gap between the enlarged graph's standard cover bound and the constructed circuit. The pruning upper bound is safe: remaining weights can only increase the objective by their sum, while the union of required cones cannot shrink. Reported completeness is limited to these recorded canonical cones and selected helper candidates. Semantic normalization does not enumerate every alternative implementation of an equal function, so these results do not exhaust all possible circuit rewrites or counterexamples.

Construction allocates all 2t fresh inputs first, keeps old inputs at their original indices, and maps each retained old internal record to `new_input_count + emitted_gate_index`. It then adds OR(h_i,leaf_i), AND(center_i,...), and OR(current_output,...). Matching on the verified bipartite enlarged graph supplies its exact cover number by the bipartite matching/cover theorem; the implementation also checks the predicted increase by t and the exact final profit before emitting a witness. The final enlarged truth table is compared in full.

The independent bounded control script `audit_reusable_helpers.py` passed. It independently verified input truth-mask construction through n=8, a shared-cone accounting example, and the complete known C8 extension: eleven old output-cone gates plus one helper gate plus three new gates gives fifteen gates on ten inputs. Every one of its 1024 assignments was independently reevaluated, its cover number was independently enumerated as five, and all common-neighbor counts are at most one. A second control used old matching edges (0,1),(2,3),(4,5) with supports {0,2},{3,4},{5,1}: each support alone admits a component flip, but the joint extension creates an odd cycle, and the implementation correctly rejects it. Complete results are in `reusable-helper-audit.json` and `.log`.

The preserved result JSONs were inspected in full through structured parsing:

| Result set | Valid cases | Cases with safe helpers | Maximum profit | Complete subset searches |
| --- | ---: | ---: | ---: | ---: |
| helper-audit-results.json | 29 | 3 | 0 | 29 |
| helper-dp-audit-results.json | 2130 | 2130 | 0 | 2130 |
| helper-all-safe-audit-results.json | 110 | see individual records | 0 | 110 |

All contain zero reported errors and zero counterexamples. This review did not rerun a solver or claim a global negative result.

## Peelability and fix_many audit

Independent source-and-results verdict: PASS for `lean_setup/PEELABLE_AUDIT.md`, `peelable_audit.py`, and their completed JSON/log output. Source hashes:

* Python: `1ecd2db7eafb6151c9e622e7786e94f971785ab963e79fb264e913fcb57a4954`.
* Markdown: `892989165a4c85f486668b4bb0fca28d3cac29a0b8a0ff683a5e04fd75534a2d`.
* JSON: `a1587c5a1904c4f1318245baccd888efd8b5c456300833faab2341a0479ab51e`.

The initial good-leaf and six-distinct-vertex run tests match `Defs.Peelable`: leaf parent degree at most two or a second leaf, and four degree-two internal path vertices with endpoint degree at most two. Failure of this initial test suffices to rule out Peelable. The audit correctly treats that as an obstruction to the proof route, not to the circuit lower-bound statement.

The independent-set dynamic-program recurrence is exact, so `tau(active)=|active|-alpha(active)` gives exact cover cardinalities. Setting x_v=false removes v's incident edges. Setting x_v=true yields free OR variables at every neighbor, with all their incident edges absorbed, leaving the induced graph off v and its neighbors. Thus the reported zero/one potential calculations match `Phi1=|A|+|E|+tau`.

`PermInputs.fix_many` explicitly requires nonempty T. Consequently every feasible L is independent: an assignment making both ends of an internal L edge true would make the remaining function constant and destroy every terminal T dependence. For independent L, the implementation computes robust terminal inputs and directly checks that characterization against full truth-table sensitivity for every independent set. The reachability dynamic program examines all prefix sets and all admissible next inputs; a superset always has a larger bitmask, so the traversal order is valid. Taking all robust terminal inputs maximizes T's cardinality, and its nonemptiness is enforced.

The complete final log and JSON agree:

| Graph | Phi1 | Initial peel | Exact maximum fix_many potential | Size lower bound | Independent sets checked |
| --- | ---: | --- | ---: | ---: | ---: |
| Heawood | 28 | false | 16 | 15 | 458 |
| 5x6 fourteen-edge graph | 19 | false | 14 | 13 | 160 |
| C8 extension | 16 | false | 12 | 11 | 119 |
| C6 with a pendant leaf | 10 | false | 9 | 8 | 31 |

The stated limitations of the T7 and relaxed-run developments are accurate: bipartiteness and C4-freeness do not imply their stronger structural premises, and `RunAsm5.asm_a1` still takes the explicit `asmChain` and `AsmEndOO` assumptions. The numerical audit is investigative Python evidence, not a new Lean theorem.

## Pendant insertion amplification

The second proposed construction is mathematically sound. If an existing AND gate has operands x_v and h and has an OR-only path to the output, inserting one OR gate to replace only h by h OR fresh_leaf changes that gate to old_gate OR t, where t=x_v AND fresh_leaf. Induction through all later AND/OR gates gives new_wire<=old_wire OR t. Monotonicity gives old_output<=new_output, and the surviving OR-only path gives t<=new_output. Hence the new output is exactly old_output OR t, including when the edited gate also has other paths through AND gates.

Distinct edited AND gates allow sequential application: no OR-only path traverses any other target AND gate, and the selected original-input operand at each later gate remains intact. Each leaf must be fresh, and each gate may receive at most one operand edit. Editing both operands of one AND would introduce an unwanted product of the two fresh leaves, so that restriction is essential.

t edits add exactly t gates and t pendant edges. If the exact cover number rises by r, the circuit deficit decreases by r. Bipartiteness and NoFourCycle are preserved because every new vertex is a leaf. For distinct attachment vertices, the exact cover number is also

`min over covers T of the old graph: |T| + number of selected attachment vertices outside T`.

This validates the use of exact matching/cover checks for r. Old gate indices must be remapped after adding fresh input slots and inserting intermediate gates; retained-cone charging must reflect the actually emitted circuit. The pendant-edit implementation itself was not yet supplied or audited here.

The operand may also be an existing old wire f with singleton support {v} and the pointwise inequality f<=x_v OR F, where F is the old graph output. Monotonicity supplies x_v<=f. The edit then adds a AND f, which is absorbed modulo F: `F OR (a AND f) = F OR (a AND x_v)`.

This generalized operand condition remains valid across several distinct gate edits. Maintain, for every mapped old wire w, `old_w <= current_w <= old_w OR current_output`. The lower bound follows from monotonicity. At one edit, the changed gate gains t=a AND current_f; its surviving OR-only path ensures t<=new_output. All downstream wires are at most their previous values OR t, preserving the upper invariant since the output itself only increases. Thus an originally eligible f satisfies `x_v <= current_f <= x_v OR current_output` at its later edit, even if earlier edits changed its value. Applying the same absorption identity proves exactly one additional pendant edge at each step. Fresh leaves, distinct target gates, preserved OR-only paths, and at most one operand choice per target remain essential qualifications.
