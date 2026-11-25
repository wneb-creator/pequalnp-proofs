# AND-only audit for pilot152, gap L-meta-3754

This bundle contains computational checks, not a Lean proof or a refutation of the posted statement.

## Existing C12 result rechecked

The immutable earlier encoder `../search/and-synth-extreme-ordered.py` with p=6, k=5, t0=false produced UNSAT after 271.72 seconds. Its existing complete log is `../search/and-synth-c12-extreme-ordered.log`; its exact query is `../search/and-synth-c12-extreme-ordered-t0False.smt2` (SHA256 0d53d60f69bc891e8a886f79a7c4b4d8c0186d98d1e47bdb9579e334f32df1c6). Regenerating that query from the preserved encoder produced byte-identical SMT (`and-cycle-c12-regenerated.smt2`, verified by cmp exit0). The UNSAT query was not needlessly rerun; no proof certificate was generated or Lean-checked.

The query permits arbitrary ORs of raw inputs and preceding AND outputs as operands, and an OR of AND outputs as the final output. It tests the 12 edge inputs and 29 maximal independent sets. Since all modeled gates are monotone, agreement on those 41 rows implies agreement on every assignment. Nonempty operand subsets are appropriate for constant-free binary AO circuits. Unused gates can be discarded, and an at-most-five circuit can be padded by idempotent ANDs to exactly five used gates. The operand-order constraint is commutativity. The adjacent independent-gate key-order constraint has a canonical topological ordering: independent adjacent gates can swap without changing their keys, since their operand indices are earlier than both. A lexicographically least topological order therefore obeys the constraint. This normalization argument has been inspected mathematically, not formalized here.

## Positive control

`and-cycle-six-control.py 6 30000` keeps the same encoder but uses 6 ANDs and fixes the standard six-star circuit. It returned SAT in 0.002 seconds and independently verified the resulting circuit on all 4096 assignments. This circuit uses 6 ANDs, 6 neighbor-ORs, and 5 output-ORs, hence 17 total gates. The full model, query, and log are preserved here. A free-OR model alone would not imply any total-gate bound.

## New C14 experiment

`and-cycle-search.py 7 300000` changes only the output artifact path from the earlier encoder. It sought at most 6 ANDs with unrestricted free ORs for C14, using 14 edge minterms and 51 maximal independent sets. It returned UNKNOWN because of timeout after 300.05 seconds. This supplies no lower bound and no model. Its full SMT and stdout/stderr log are preserved here.

## Failed auxiliary invariants

`and-invariants-audit.txt` records complete finite truth-table checks of two small examples. P4 can have both matching edges first created by one dirty AND, so first-creation injection is invalid. The 3-AND function h=ab, `(h OR c)d OR (h OR e)f`, has 7 maximal false assignments, refuting the unrestricted essential-nesting bound 3*2^(k-2). The latter function is not quadratic, so no quadratic-specific claim is settled.
