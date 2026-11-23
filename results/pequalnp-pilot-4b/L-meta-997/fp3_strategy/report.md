# L-meta-997 status

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The complete posted inequality remains unproved and unrefuted. No repository file was changed by this agent. The general compensation/exchange step described below has not been established.

## Checked results

`RefundOutputsExtension.lean` contains the exact posted refund predicate, expressed using the root's `Window.value`. Its self-contained harness `RefundOutputs.lean` compiles with an empty log and was independently audited by formal_audit.

* `output_gate_bounds`: a line with at least two points has an actual gate output, not an input or out-of-range wire.
* `disjoint_output_refunded`: every such output for a line disjoint from y belongs to the exact refund, with both full signatures equal to that line.
* `large_heavy_refund_bound`: for k>=1, the number of disjoint lines of size greater than k is at most the refund cardinality. Pairwise intersections at most one make their output gates distinct.
* `bounded_heavy_size_finish`: the all-lines light bound, together with disjoint line sizes at most k+1, implies the desired weighted inequality.

`BoundedCaseExtension.lean` assembles an actual one-NOT special case using root `Windows.lean` and prior_routes `SparseCount.lean`. The combined `BoundedCase.lean` compiles cleanly and was independently audited. The theorem `RefundOutputs.bounded_heavy_size_one_not` proves the posted bound when y is nonempty and every disjoint line has size at most |y|+1. It uses the posted gate, NOT-location, exact-output, and below-weight hypotheses; it does not need the false-at-y hypothesis for this restricted conclusion.

The child proved the full |y|<=2 case in `fresh/SmallWindow.lean`, theorem `Small.small_one_not`, with the stronger bound weighted sum <= gates+m. It handles empty y, absent NOT, and out-of-range t, and does not require the below-weight hypothesis. Its compilation and axiom audit passed; see `fresh/README.md`.

`WeightedFrontier.lean` supplies the abstract counting lemma requested by prior_routes for the OR-only heavy bound. A good wire with support size at least two expands to good predecessors whose supports cover it; a free step has at most one predecessor and a paid step at most two. Reverse-index expansion proves support size <= number of paid wires +1, counting a shared paid wire only once. The file compiles with an empty log and was independently audited. prior_routes inlined it with their checked actual-circuit `HeavyOrCount.decompose` lemma.

## Exact remaining regime

After the checked reductions, a remaining instance has |y|>=3 and at least one disjoint line of size at least |y|+2. The ordinary light bound applies to every line, including disjoint lines, so their extra required heavy credits are only |S|-|y|. Their full output gates already supply one exact refund each.

## Why direct aggregation is insufficient

The usual light and heavy private-gate sets use support contained in a line and support cardinality at least two. Their intersection need not be contained in the posted refund, which requires equality with full line signatures. Explicit globally correct circuits exhibiting a proper light/heavy overlap are saved and checked by lean_setup and the child. These are counterexamples to that proof step, not to L-meta-997; their selector and source gates leave ample counting slack.

The heavy bound can count only OR gates: a globally sound AND has a sound child whose background-singleton support contains the parent's, whereas a sound OR has two sound children and unions their supports. Thus AND selectors are available to pay for switching between light and heavy signatures.

A light-window OR whose singleton signature equals one child's can be replaced by that child: all singleton signatures remain unchanged and all functions decrease, preserving exact outputs on the light window. This does not apply to arbitrary same-signature AND gates; repeated AND purification can be necessary to exclude small false inputs.

The promising but unproved exchange argument would route heavy OR trees through sound AND children. Shared clean OR regions aggregate zero-heavy-support switches or AND boundaries that change the light owner. A dirty AND parent containing two points of a clean light line cannot be owned by another light line, by the intersection hypothesis. However, charging such boundaries globally, with sharing and AND purification, has not yielded an injection or an amortized inequality. In particular, no proof shows that all proper overlaps are paid by unused gates or slack, leaving only the exact full-signature refund exceptions.
