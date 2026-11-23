Checkpoint provenance: this is the research audit recorded before the push-early checkpoint. Auxiliary paths below refer to the original scratch artifacts; those files are being preserved separately. No target proof file was changed.

# Independent audit of L-meta-997

The exact posted proposition elaborates in `Statement.lean`. The complete log is
`statement.log`; the proposition depends only on `propext`, `Classical.choice`,
and `Quot.sound`. This is a statement elaboration, not a proof of the proposition.

No counterexample or complete proof has been obtained. No repository file was
changed and no synthesis solver was launched for this gap.

## Semantics and boundary cases

Circuit gates append a value to the existing wire list. Reads of absent or future
wires at that time give false. Empty AND gives true, empty OR gives false, and
NOT ignores all but its first input, using false when there is no first input.
The posted fan-in condition permits empty, unary, and repeated inputs.

The distinguished wire is `n+t`. The hypothesis only says all NOT gates have
index `t`; it does not separately assert that such a gate exists or that `t` is
in range. When `|y|>0`, being true at the zero assignment and false at `y` forces
nonmonotonicity, so this omission is not an evident counterexample. An out-of-range
wire is always false and cannot satisfy the zero-assignment hypothesis.

For `|y|=0`, the sparse truth premise is vacuous and meeting-y terms vanish. For
`|y|=1`, a meeting-y line contributes at most the free one unit in the final `+m`.
These cases appear to reduce to monotone or restricted-monotone lower bounds;
they have not been formally proved here. Empty and singleton repeated target
sets do not expose an immediate issue because the pairwise intersection premise
allows those repetitions and the `+m` allowance covers their contribution.

## Exact refunds versus proper supports

For `k=|y|>=2`, the unique NOT source is false on every singleton and true at `y`.
Thus the light singleton profiles come from the NOT=1 cofactor, while the heavy
profiles at `y` plus a singleton come from the NOT=0 cofactor.

The standard sparse-support counting lemma counts gates whose singleton support
is any subset of a target line of size at least two. The posted refund is much
narrower: it requires the complete light support to equal one full target and
the complete heavy support to equal a full disjoint target. A gate charged in
both support counts therefore does not automatically belong to the refund.
One-NOT multiplexers can switch two unrelated proper support sets, so equality
of those profiles cannot be assumed.

This does not by itself refute the inequality. Selector and NOT-source gates may
pay for the overlaps. Also every exact output gate for a nontrivial disjoint
target belongs to the refund, potentially furnishing refunds that were not in
the proposed overlap set. A new amortized argument is needed to establish the
posted accounting.

The existing L-meta-1036 example gives a one-NOT advantage for general monotone
outputs. Its outputs are not a family of line ORs, so it supplies no direct
counterexample to L-meta-997.

## Reviewed helpers

`prior_routes/meta997/SparseCount.lean` was independently read in full. No flaw was
found in its fan-in-at-most-two cut argument, handling of future reads, or final
`card_assigned` lemma. That lemma assumes sparse rejection outside a target and
enough accepted singleton inputs; it correctly counts clean proper supports.
It does not establish the missing exact-refund overlap bound.

`meta997/Windows.lean` was independently read in full. No issue was found.
`freeze_eq` legitimately needs only equality propagation; the monotonicity
lemmas carry the required gate-basis hypotheses. `positive_window_not` derives
the distinguished index's validity from the zero assignment, proves its gate is
NOT, and proves it is false on all extensions of Y. Future reads and empty or
multi-input NOT gates respect the actual evaluator.

`fp3_strategy/meta997/RefundOutputsExtension.lean` was independently read in full.
Its refund matches the posted predicate. It proves an injection from distinct
nontrivial disjoint outputs into refund gates. Its final restricted conclusion
explicitly assumes every disjoint line has size at most `k+1` and an all-lines
light bound; no general conclusion is claimed.

`lean_setup/meta997/PartialOverlap.lean` was independently read in full. The
eight-gate fixture satisfies the actual circuit, unique-NOT, exact-output and
minimal-Y hypotheses. Gate 6 has proper light support `{2,3}` within target
`{0,2,3}`, and heavy support `{4,5}` equal to the other target. It is not refunded.
This disproves the naive inclusion of all partial-support overlaps in the exact
refund. It does not refute the posted inequality: its left side is only 4 while
the circuit already has 8 gates.

Appending repeated OR copies of its switched wire leaves the original outputs
unchanged and creates arbitrarily many additional partial-support overlap gates
without additional exact refunds. Thus a bound on the cardinality of the entire
raw overlap by the refund cardinality is also false. The desired theorem might
still select smaller charge sets or use the added gate-count slack.

`fp3_strategy/meta997/BoundedCaseExtension.lean` was independently read in full.
It correctly combines the audited helpers into the actual conclusion under the
extra restrictions `1 <= |y|` and every disjoint line having size at most
`|y|+1`. It legitimately omits the false-at-y assumption for that restricted
result. This is a checked special case, not the unrestricted posted theorem.

The complete frozen `prior_routes/meta997/HeavyOrCount.lean`, including the
inlined `WeightedFrontier`, was independently read in full. Its final
`card_le_or` is sound: global soundness for T and acceptance on every Y-plus-point
input give `|T| <= number of charged OR gates + 1`. A charged gate is false on
the maximal outside-T input and has at least two accepted background-singleton
points. Reverse-index expansion counts shared paid wires once. An AND gate
selects one fixed child false on that maximal outside input; the proof preserves
support coverage, not full circuit values. Future children are filtered with
their actual false-read semantics. The related disjointness and false-background
lemmas are valid. This stronger heavy bound still does not provide the missing
cross-window refund compensation.
