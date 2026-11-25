# Dirty AND transformations

Checked generic source L_meta_3297.lean (approximately31KB) proves semantic preservation outside the OR closure and a one-gate live-size drop for factor substitution. Its assumptions require per-reader selection of an operand, frontier other-side implication to the omitted factor, coherent choices along OR paths, the output outside the closure, and the deleted gate live. L_meta_3453.lean (approximately8KB) supplies ordinarywire monotonicity/equality under source domination.

These do not automatically preserve the formal derivative obstruction. Boolean semantic equivalence can change derivatives (for example, x AND x versus x). Applying an arbitrary normal-form conversion would therefore be invalid for this gap.

## New checked simulation

results/orch/lemmas/Transform.lean (124lines) imports only PEqualNP.Defs. It defines ordinary ValueRules and formal DerivativeRules for generic fan-in-two AND/OR circuits and proves:

- substitution_monotone: if every substituted source has both ordinary value and formal derivative dominated by the original gate at the chosen basepoint, the entire rewired circuit preserves both dominations at every existing wire.
- active_factor: for an AND gate a AND b, if a is true at the chosen basepoint, b has the required ordinaryvalue and derivative domination into that AND gate.
- substitution_keeps_zero: consequently a zero output derivative stays zero after that factor substitution.

For the target, apply independently at singleton inputs0 and13. If the omitted factor is true on both singleton inputs, both zero derivatives survive. This is a concrete sufficient criterion, not an assertion that arbitrary dirtyAND elimination preserves the obstruction. The proof allows duplicate inputs after rewriting; to obtain another posted-model circuit one must additionally rule out collisions or account for their cleanup.

Compilation: lake env lean exited0 with no warnings; full log /tmp/oec/pequalnp-pilot-60/transform-build-2.log. Exact snapshot left unchanged for root review/push.

Remaining structural obligation: find a dirtyAND/factor substitution satisfying both the semantic frontier guards and the active-factor condition, with enough gate saving or no duplicated-input collisions. No such existence theorem has been established.

## Global rewiring extension

FactorElimination.lean now compiles (401lines,18022bytes; exit0 and no warnings). It proves full Booleanfunction preservation when each enlarged reader stays below the targetF, rather than requiring each reader itself to be semantically unchanged. It separately proves proper distinct earlier inputs under an explicit noncollision premise, and that no input of any rewired gate references the eliminated wire. Derivative witnesses are preserved unchanged if the selected source has the same value and derivative as the AND gate at the singleton base; zero_factor_equal derives both equalities from a kept operand with value=false and derivative=false, regardless of the omitted factor.

The source is frozen for review. Combining with derivative agent DeadGate.erase_eval/erase_witness will yield actual gate-count reduction; this last combination is in progress.

## Combined strict-size statement (compiled)

CombinedElimination.lean assembles the derivative agent dead-gate compactor and the checked global rewiring lemmas. Its final eliminate_factor proposition concludes an actual new proper circuit with exactly one fewer gate, the same Booleanfunction, and both zero formalderivative witnesses with their original input values. It explicitly assumes no collisions in rewritten input pairs. Its other local premises require each modifiedreader to stay belowF and every selectedoperand to have zero ordinaryvalue and derivative at both markedbases. No assumption is made that arbitrary semantic rewrites preserve derivatives.

After the root verifier stopped, the corrected DeadGate file and CombinedElimination both compiled successfully. CombinedElimination exited0 with no warnings; full log /tmp/oec/pequalnp-pilot-60/combined-elimination-build.log. The complete combined snapshot is frozen for independent review and push.


## 2026-11-25: checked constant propagation with padding

`ClampComplete.lean` proves `inactive_gate_smaller`: any gate false on all minimal incidence edges can be removed with exactly one fewer physical gate, preserving the full graph function, distinct earlier inputs, and both marked derivative-zero witnesses. The source is marked abstractly zero. OR copies use an earlier representative for ordinary reads while their retained physical gate becomes representative OR an unmarked input. If a later AND would have duplicate representatives, one of its original operands is an earlier OR alias; its retained padding slot supplies a distinct second input. The identity q AND (q OR z) = q preserves semantics, while z has zero value and derivative at both marked seeds, preserving the repeated-AND derivative.

All components and the final wrapper compile. `ClampMinimum.lean` additionally proves a minimum-size/all-active normalization using Nat.find, without using the open lower bound63.

The all-active condition alone does not imply clean ANDs or safe factor choice. The matching function xy OR zw has the seven-gate CNF circuit (x OR z) AND (y OR w) AND (x OR w) AND (z OR y), using four OR gates and three AND gates. Every gate accepts some minimal edge, but the intermediate rectangle conjunctions are dirty and both marked derivatives vanish. The plane size budget must therefore still be used.

Prospective strengthening: computing fresh derivative witnesses for the residual circuit should allow arbitrary source clamping with derivative domination, rather than requiring source-zero signatures to reuse the original witnesses. If established, minimum double-zero circuits could be assumed every gate essential on a minimal edge. This is not yet a checked theorem.
