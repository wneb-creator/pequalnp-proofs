High-eligibility residual constraints, 2026-11-25

These are finite necessary-condition experiments, not Lean theorems, Boolean circuits, witnesses, or impossibility results. The accepted Heawood labeling is used. Residual-unit support may contain eligible labels only, and every residual unit has nonempty support.

For each ineligible input i, the assigned operand initially carries N(i). Sharing comes only from residual-unit supports and these assigned operands. Iterating the existing residual co-label rule adds t when an original neighbor x has residual mask contained in t's and a known wire shares x and t. The generic assigned-position budget, plus one eligible adjacent-input slot when available, is tested at every eligible t.

For each eligible cofactor center c, X contains every eligible x distinct from c whose residual mask is contained in c's and which shares a known wire with c. The old score is card(ru(c))+card(X)+7 when no eligible free K4 original remains outside X, and +8 otherwise. The prospective score raises this to +9 when at least three such free originals remain. The +9 wrapper was mathematically derived from the in-progress K4 surplus7 eligibility theorem and multi-unit normalization slack, but is not claimed compiled here. An independent set-based verifier checks every subset of each permissible X for60 saved examples, not just the maximal X used by the enumerator.

For p13, I={0}, one residual unit: all8192 states were enumerated;8191 have nonempty unit support; all8191 satisfy assigned budgets;2079 survive old cofactor scores and1200 survive the prospective score. A simple survivor has residual support {1}, assigned neighborhood N(0)={7,8,10}, and maximum prospective score11.

For p12, two residual units, only the first65536 of16777216 states were examined in each case. For I={0,1},65025 have nonempty units,48896 satisfy budgets,2786 survive old scores,1712 survive prospective scores. Residual supports {7} and {2} give a concrete surviving abstract state (maximum prospective score14). For I={0,9}, the corresponding counts are65025,65025,7195,4941; both units supported on {1} survive (maximum score13). These bounded counts are not exhaustive p12 censuses.

All experiments finish in under one second combined. The source, full logs, JSON examples and independent verification are preserved. The surviving states show that this selected collection of necessary constraints alone does not exclude these high-eligibility cases; additional circuit structure is needed.
