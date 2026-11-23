# Independent audit of L-meta-982 scratch work

The root stopped shard15 witness search after its structural lower bound compiled. The solver returned UNKNOWN after 263.7975581029996 seconds because it was intentionally terminated. This is not an UNSAT certificate. Complete logs remain in meta982-shard15-general-s10.log and .solver.log.

## Assigned shard15 statement

The final theorem `PEqualNP.Outside.L_meta_982_aux.shard15` in `Shard982Structural.lean` matches the posted conjunct at zero-based index15 exactly after removing whitespace and the qualification of `HasCircuitSize`. It quantifies every natural t and proves 11≤t for AND/OR/NOT circuits computing the seven-input edge function with edges 01,02,03,04,12,15,34,56. The structural chain uses an eight-gate bowtie bound, adds one gate in both restrictions at input6, and applies the two-gate elimination lemma to derive11. This is one conjunct, not the entire31-conjunct target.

The file imports only Mathlib and PEqualNP.Defs. Static source inspection found no sorry, native_decide, new axiom, unsafe declaration, or runtime evaluation tactic. The independent scratch copy with #print axioms compiled successfully (exit0). Its final theorem depends only on [propext, Classical.choice, Quot.sound]. It has no sorryAx or evaluation/compiler axiom. Complete output is audit-shard982-structural.log.

## Independent shard0 enumeration

The child implementation `merge_meta982_shard0_nosym_bfs.py` was independently reviewed line by line. It uses complete64-bit functions and no vertex symmetry. Every stage enumerates all distinct live-operand AND/OR pairs and all unary NOTs, with every retain/drop choice. Semantic aliases, constants, and original-input outputs can be removed from a minimum circuit. Thus fresh-gate normalization justifies the excluded outputs; it does not assume monotonicity of intermediate wires.

All six inputs are essential, as witnessed explicitly. A remaining r-gate continuation cannot combine more than r+1 live sources. If equality holds, every remaining step must be a binary gate dropping both operands, so the continuation is monotone in the current wires; oriented positive/negative separation is then necessary. With positive slack the implementation uses only undirected separation, allowing NOT. It checks all735 positive/negative pairs, not a monotonicity-only reduced set.

Budgets0–4 close from source count. Budgets5–9 each close with an empty complete frontier; no timeout or state cap occurred. Budget9 frontier counts are42,1627,5500,3706,769,137,6,0. Total runtime is2.197s. A10-gate monotone control and a13-gate De Morgan control with three NOT gates pass every state rule and all64 output assignments. The JSON summary shape and all complete closure flags were independently checked. This computational result is useful corroboration but is not itself a Lean proof.

Program SHA256: 2b3c67b050c43efb34f7512452e054bcca9ec113321e576284f4c15e4bf0569b
