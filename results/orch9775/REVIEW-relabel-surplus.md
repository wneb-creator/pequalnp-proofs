# Independent review: RelabelSurplus

Verdict: PASS. The invariance result is generic in the DAG and permutation;
it does not require target correctness, a graph automorphism, or an
already-proved empty-surplus exclusion.

Reviewed source: 40 lines, 1,716 bytes, SHA-256
`ad47b24aca4cc10e9226f14ea55e8d6b1dba36b7d8a170fcd3c6d0330a646e5b`.
Both complete `relabel-surplus-checked` logs are present and empty;
the author reports checked compilation and export exit 0. No build was
rerun for this read-only review.

`relabel_support_surplus` uses the lifted primary-input permutation as
a bijection between the filtered non-output wire sets. Nonempty DAG
length supplies `n <= n + D.length - 1`, which is the necessary bound
for `tr_liftP_lt_iff`; this avoids losing a primary wire at the cutoff.
The existing `relabel_supp` theorem maps singleton support by the input
permutation, so support nonemptiness and its negation are both preserved.

The finite-sum bijection explicitly proves forward membership,
injectivity, surjectivity using the inverse lift, and equality of each
summand using `relabel_fanout`. Thus natural fanout surplus is transported
wire by wire, not inferred from total surplus alone. The `true` and
`false` specializations unfold exactly `Bplus` and `Bzero`.

I checked the referenced lift inverse/injectivity, cutoff, support, and
fanout theorem statements in the independently reviewed generic DAG
module. None requires graph correctness or a zero-surplus conclusion.
There is no circular use of `no_empty_surplus` or a specialized final
lower bound. The source has no `sorry`, new axiom, `native_decide`,
forbidden root marker, string literal, attribute, or option. Its scratch
import still needs the ordinary final assembly/checker treatment.
