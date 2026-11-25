# Residual tap: exact constraints and unchanged-star obstruction

Let R be the25-input residual function in R_meta_650_517 and Q=y12 OR y13 OR y15 OR y21. For any monotone tap T, its conditional requirement is equivalent to the global interval Q<=T<=Q OR R.

Upper bound: when R=false the requirement says T=Q; when R=true the upper bound is automatic. Lower bound: each designated line singleton has R=false and Q=true, so T is true there; monotonicity then forces T=true on every assignment with any designated line selected. Thus the don't-care freedom only permits extra true values supported by R. It cannot permit dropping a designated line on a residual-true input.

In the canonical59-gate residual DAG, every existing wire is true on at most one of the four designated-line singleton assignments. Input wires are obvious. Each row-neighborhood OR contains exactly one designated line, because any remaining point lies on exactly one line through the deleted point. Every row product and every OR of row products is false on all four line singleton assignments.

For any new AND/OR gate, its set of accepted designated-line singletons is contained in the union of its parent sets. A connected binary DAG with at most two new gates has at most three distinct existing-wire leaves, hence accepts at most three of the four singleton assignments. Therefore no choice of output wire or tap position, no rebracketing of the existing star ORs, and no two appended gates can turn this canonical59-gate DAG into the required61-gate two-output witness. A successful61-gate solution must alter internal residual computation and share a wire carrying at least two designated-line singleton supports. This is a precise analytic restriction on the canonical family, not a lower bound for all residual circuits.

On the all-points-false restriction, T must equal Q exactly. A proposed shared internal union containing an undesignated line singleton cannot simply be ORed into T; it needs a filter that removes that singleton. This is where any nonlinear sharing must repay its gate cost.

## Common-line guard sharing

For two row stars a(q OR U) and b(q OR V), their OR equals

`((a OR b) AND (q OR U OR V)) AND (q OR (a AND U) OR (b AND V))`.

The first factor is the merged rectangle. Its false positives force q=false; the second factor's false positives require q=true. An unchanged outside residual R can be ORed once after this product. Factoring R out of the earlier two-factor whole-output construction saves one gate.

With four-neighbor rows this construction costs four more gates than canonical stars:13 instead of9 for the pair block. The exact k6 seeds therefore improve34 to33 gates; all15 pairs are saved in k6_pair_line_guard_shared33.json and pass the complete76-test basis. The analogous full-plane cost is68 and the25-input residual cost63, with no tap supplied. This is an actual sharing improvement, but remains over budget and is not a proof of optimality of the construction.

No new exhaustive search lane was launched.
