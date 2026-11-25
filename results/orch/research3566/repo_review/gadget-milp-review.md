# Independent structured MILP search review

Reviewer: pilot-178 subagent repo_review. Reviewed source `gadget_milp.py`, SHA256 `fc4bdbbfefb2875aea002b98801d9bffb6f9b844ca938f7ff71072aa7211fa49`.

Verdict: PASS for the soundness of any successfully emitted and fully checked witness. The model is a restricted search and supplies no general lower bound or completeness result. No improving witness was present in the reviewed `bip5x6-gadget.json`; its complete solver log reports a time limit with no feasible solution.

## Acyclicity

Every recipe for a nonclean node has both operand IDs smaller than the output ID. The only exception permits a clean/guarded node to use later nonclean nodes. This exception is safe in the current generator because nonclean nodes never depend on clean/guarded nodes: linear nodes depend on earlier linear/input nodes, dirty products depend on linear nodes, and mixed nodes depend on dirty products and inputs. Therefore a dependency path that leaves a clean node enters the acyclic nonclean subgraph and cannot return to a clean node. The initial kind of a semantically deduplicated node does not invalidate this distinction: clean signatures are false on all negative rows, whereas input/linear/dirty/mixed signatures have a negative-row witness in these graphs.

The standalone `audit_gadget_library.py` checked an even stronger condition on both available generated libraries: the union of every alternative recipe is acyclic. It also checked every recipe's AND/OR signature, all dependency indices, active-set closure, clean output signatures, input signatures, and the exact positive/maximal-negative row list. It performs no solver calls.

| Library | Nodes | Recipes | Active nodes | Clean outputs | Recipes with later operand IDs | Maximum union depth |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| heawood-library.json | 4097 | 10213 | 2250 | 434 | 1288 | 8 |
| bip5x6-mixed-library.json | 7184 | 16902 | 2920 | 541 | 667 | 8 |

All checks passed. Complete output and artifact hashes are in `gadget-library-audit.log` and `gadget-library-audit.json`.

## Cost and producer accounting

For each selected noninput node, the equality sum(producer variables)=node variable chooses exactly one producer. Each selected producer requires both noninput dependencies. Each selected output requires its node. The integral objective charges one unit for every selected noninput node and one for every selected clean output.

Recursive emission shares every selected node through the wire table, so it emits at most the number of selected noninput nodes. Combining t selected outputs uses exactly t-1 binary OR gates. Thus the emitted size is at most sum(node variables)+sum(output variables)-1. With the default objective cap `<=star_cover_upper`, this gives a circuit strictly smaller than `star_cover_upper`. With `--allow-baseline`, the cap increases by one and permits equality with the baseline. The final size assertion matches these inequalities. Selected but unused nodes can only overcharge the objective, never undercharge the emitted circuit.

Every graph here has at least one edge; edge coverage therefore forces at least one selected output. Recursive emission produces backward gate operands. If the solver returned a numerically inconsistent selection, missing dependencies or failed assertions would prevent an accepted artifact. Independent checking of any actual witness is still required before its Lean translation.

## Sample signatures and output correctness

Semantic node deduplication uses positive edge assignments and maximal independent sets. These signatures need not identify the same internal Boolean function on every assignment. That is sufficient for this model: every selected recipe computes its stored signature on the boundary rows, and the selected clean outputs cover all positive rows while remaining false on every maximal negative row. Their OR is monotone. Positive-edge and maximal-negative completeness therefore imply the exact graph function on all inputs. The source additionally evaluates every one of the 2^n assignments and refuses to write a successful witness if any differ.

## Search limitations

The restricted circuit layers, selected linear disjunctions, dropped dirty products covering fewer than two edges, recipe caps, maximum clean-output size, optional mixed constructions, and optional exact edge partition all restrict the search. Infeasibility in this model does not establish infeasibility for arbitrary AO2 circuits. Source cost estimates order/prune recipes but are not used to undercharge the MILP objective. The parsed `--rounds` option is currently unused; this affects expected search coverage only.

The reviewed 5x6 run had 31 boundary rows, 926 active nodes, 3262 recipes, 4365 MILP variables, and 7107 constraints. Its time-limit result is accurately recorded as no feasible result found, not as UNSAT or a proof of the expected 18-gate optimum.
