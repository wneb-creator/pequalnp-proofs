# Support accounting for L-meta-4970

No finite SAT argument is used. These are checked partial lemmas, not the posted theorem.

All sources below are frozen under `/tmp/oec/pequalnp-pilot-99/gap4970/sat_encoding/`; the coordinator owns independent review, copying, and pushing. Each uses only Mathlib and PEqualNP.Defs, with every declaration inside a namespace below `PEqualNP.Outside.L_meta_4970`.

| Source | SHA256 | Lines / bytes | Successful complete logs |
| --- | --- | --- | --- |
| `SupportBudget.lean` | `39024ed2f2f3056bff56dc112abba2d60f5c5f85e1cf378f5118a43523051752` | 234 / 10368 | `support-budget-01.stdout`, `.stderr` |
| `SupportSemantic.lean` | `cd5d23bc1b6c4c804cb17584bc40a6d51ad59813fa6f5f9d893547a56e687e3c` | 363 / 16379 | `support-semantic-02.stdout`, `.stderr` |
| `SupportFamily.lean` | `7f127d69efd6d855c8b74cf9e93241c8b1bf6e2257b6a7a92518fe91c77babde` | 603 / 26431 | `support-family-02.stdout`, `.stderr` |

Each compile exited 0. The final artifact includes the earlier two plus the independently developed and frozen `SemanticSupport.lean` from library_route. It is standalone. From repository `lean/`, run `lake env lean /PATH/SupportFamily.lean` using the pinned cached toolchain. The final format scan found no `_root_`, double quotes, or attributes. No new axioms or prohibited evaluation tactics are used.

The key set `singleSupport n C w` consists of inputs whose singleton assignment makes wire w true. For an allowed leaf set S, `good n C S w` says w is valid and is false on the input that sets every variable outside S true and every variable in S false. A good wire's singleton support lies in S by monotonicity.

At a good AND gate, at least one operand is false on that complement assignment. Every singleton accepted by the AND is accepted by the chosen operand, so support can pass to one earlier wire without charging a gate. At a good OR, both operands are good, and their singleton supports union exactly. The generalized `merge_pass_bound` charges only two-predecessor merging steps; it permits an uncharged single-predecessor step even when the support has more than one input.

`support_budget` proves that a finite good root set R satisfies

`card (union of singleton supports of R) ≤ R.card + (charged n C S).card`.

Here `charged` contains only OR gates good for S whose singleton support has at least two inputs. For sets S and T with intersection cardinal at most one, `charged_disjoint` shows their charged gate sets are disjoint. Thus `support_family_budget` gives

`sum over centers (card (union of root supports)) ≤ sum over centers R.card + orWires.card`.

The exact side condition is pairwise intersection cardinal at most one for distinct selected centers. Lower_bound is preparing this condition for the bipartite C4-free neighborhoods in the posted statement. The bridge lemmas `pure_or_support`, `pure_or_good`, and `pure_or_budget` use the explicit semantic OR-of-a-finset hypothesis of the posted witnesses.

Limits: this counts roots, not overlap components; an improvement to components is not assumed. It does not use `tCount = 0`. That condition constrains syntactic OR reach, which stops at AND gates, and does not imply that every OR function is a pure single-color disjunction. An AND gate can hide input colors. The witness OR gates may also be dead. Therefore the remaining unrestricted AND/combining-OR budget needs an additional argument accounting for unused witnesses, redundant coverage, and the number of roots. The current partial does not claim that each witness has a corresponding productive center-AND gate.

## Checked overlap-component improvement

The root-count limitation above is resolved by these later frozen sources; the remaining AND/combining-OR issue is unchanged. All are in the same scratch directory, compiled with exit 0, and sent for independent review/preservation.

| Source | SHA256 | Lines / bytes | Successful complete log stem |
| --- | --- | --- | --- |
| `MergeGraph.lean` | `c036ecc036074fdeaf2e8d6c0766082f444a5a2c0f460050183504c196cd6709` | 119 / 5125 | `merge-graph-01` |
| `MergeRank.lean` | `44b33a33a3df0ee44def86a62bde7f8bbd18a969da7ccb6486240b0cbea05be6` | 188 / 8358 | `merge-rank-02` |
| `SupportRankBudget.lean` | `018dd774664c38ad8e132fc9d6c24613dc8e1014ddfad7c37e2059aa070a3937` | 887 / 38970 | `support-rank-budget-01` |
| `OverlapComponents.lean` | `eceb7b30324d547714b507adcaded156fc6b14d675be1aa7458ba6415bc95708` | 253 / 11179 | `overlap-components-03` |
| `SupportComponents.lean` | `ff3908b3741ea63068993eb253a3bc4f8bbb3319bdfd36df605e478c518a86d3` | 997 / 43765 | `support-components-01` |

`SupportComponents.lean` is the standalone aggregate. The generic `merge_graph` constructs a graph with at most one edge per charged OR, and every good wire's singleton support lies within one connected component. AND steps use the previously checked free pass. The overlap graph joins distinct leaves that occur together in a selected root support. Its paths therefore remain within constructed-graph components. Summing Mathlib's connected-graph vertex/edge bound over components gives the rank inequality.

`rootComponents` counts only overlap components meeting the union of root supports. The checked identity `overlap_component_card` cancels isolated unused input vertices. Consequently `support_components_budget` states

`unionleafcard ≤ chargedOR.card + nonemptyoverlapcomponentcard`,

and `support_components_family_budget` sums this over separated centers with total charged gates at most `orWires.card`. This proves the requested stronger OR ledger, still without using T=0 or claiming the full gap.

The counterexample agent independently exhaustively tested the proposed stronger inequality on all 17,244,252 commutative binary AO2 prefixes on three inputs through five gates and 1,437,020 on four inputs through four gates, with every nonempty S and all eligible pure-OR roots. No counterexample was found. Those computational checks were a preliminary control; the Lean lemmas above establish the result.

## Self-charged family corollary

`SelfChargedBudget.lean` is frozen and checked with exit 0, including cached olean output: SHA256 `d4344153b9eaf7c19cc5568d122729878de145a0840d9dc7ce37dfbf2557f4a2`, 631 lines, 27,709 bytes. Full successful logs are `self-charged-budget-02.stdout/.stderr`. This contains `SupportFamily.lean` plus the compact lemmas `charged_family_card_le` and `self_charged_family_budget`.

Choose the root set at center c to be the charged OR set itself. Disjointness bounds the sum of these root counts by `orWires.card`; the original support budget then gives total covered singleton-support incidences at most `2 * orWires.card`. Every posted pure-star witness belongs to the appropriate charged set. Library_route owns the remaining finite edge-cover bridge from those exact posted hypotheses. This approach proves the requested half-edge OR lower bound without requiring the more elaborate component theorem. It does not prove the full `|E| + cover - 1` gate bound.

For cached module reproduction, Lean's documented package-root flag is required when writing oleans outside the project directory: from `lean/`, use `lake env lean -R /PATH/TO/SCRATCH -o /PATH/TO/SCRATCH/SelfChargedBudget.olean /PATH/TO/SCRATCH/SelfChargedBudget.lean`. The initial attempt without `-R` failed only because the input was outside the current root; the recorded successful second run uses the explicit scratch root. `SupportFamily.olean` was also generated successfully with logs `support-family-olean-02.stdout/.stderr`.

## Direct induction investigation

No complete proof of the posted bound was found. A precise candidate induction tracks `W(C,E)`, the subset of graph edges served by existing qualifying pure-OR star gates, and aims for `C.size + 1 ≥ W.card + τ(E)`. Initially W is all of E. After setting a vertex v to false, let C_v be the folded circuit, E_v the graph with incident edges removed, and W_v the surviving witnessed edges. A sufficient step would save at least `W.card - W_v.card + τ(E) - τ(E_v)` gates, with the final additive-one adjustment when the remaining graph is empty. This addresses the real closure problem: a two-leaf star can become a singleton, so the original all-edges-witnessed hypothesis need not survive restriction.

The unconditional local-elimination claim is false. Start with the canonical eight-gate six-cycle circuit F and its three pure star OR roots Q. Append, once for each Q, `H = F_previous OR Q` and `F_next = F_previous AND H`. The function remains F. T=0 is preserved: the graph-function wire has empty syntactic OR reach, and Q has only one color. These six absorption gates keep every Q structurally live after any single vertex deletion.

The counterexample agent verified the resulting 14-gate circuit on all 64 inputs and checked every posted premise. For all six vertices, literal constant/idempotence folding plus maximal output-cone pruning saves exactly two gates, whereas degree plus cover decrease requires three. Keeping all surviving star roots also saves two gates. The W-tracking induction requires three for point deletions and five for line deletions. Full source/results are `gap4970/counterexample/restriction_obstruction.py`, `.json`, `.stdout`, and `.stderr` in scratch; the stdout was inspected. This is a computational counterexample to the proposed elimination lemma, not a refutation of L-meta-4970.

Global minimality or absorption normalization would remove that particular obstruction, but a replacement saving lemma under those conditions remains unproved. It cannot be justified by pretending T=0 means semantic one-color purity. In fact, prepending one `AND(i,i)` shield per raw input and redirecting all original raw-input reads to the shields makes every original OR's syntactic reach empty at a cost of only n gates, without restricting the original monotone functions. Same-color dead star witnesses can still read raw inputs. Thus a proof needs an actual budget for hidden mixed dependencies, not a syntactic purity assumption or an unproved conversion to star form.
