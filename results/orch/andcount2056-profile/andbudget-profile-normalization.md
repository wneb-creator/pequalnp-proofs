# Cost-preserving positive-profile normalization

This proposal is separate from the frozen running K16 query. No full-plane
63-gate witness or general lower bound is claimed.

For each active AND record, consider its truth values on the52 minimal
true edge rows. If the profile is empty, set both operand memberships to
empty, making the record inactive. Later records can retain references
to this false wire. Every positive-row value at every later wire is
unchanged; all negative-row values can only decrease. The record had at
least2 memberships, so M decreases by at least2 while A decreases by1;
the bound M−A−1 decreases by at least1.

If the profile is exactly one incident edge(p,l), replace the record by
the direct AND of primary inputs p and13+l. This has the same positive
profile and is false on all704 maximal false rows. It uses exactly2
memberships, no more than the old active record. A is unchanged.
Induction through the remaining monotone network preserves all positive
values and cannot introduce negative acceptance. Applying the two rules
to records in order preserves any correct circuit and its K/cost cap.
Empty/inactive records need not be compacted for these two constraints.

The suggested first-active-AND incident-edge split anchor was withdrawn.
Accepting an edge does not imply its two endpoints appear in different
operands. For example, operand subsets{point0,point1} and{point0,point2}
produce(x0∨x1)∧(x0∨x2), whose positive profile is all four edges incident
to point0. No line appears in either operand, so input automorphism and
operand swapping cannot give a point/line split. The zero and singleton
rules leave this four-edge profile untouched.

A primary-dominance deletion removes this particular one-common-input
example, but does not settle the general membership-cost issue. For
example, both operands can share two point inputs: the idempotent record
(x0∨x1)∧(x0∨x1) has an eight-edge positive profile and represents shared
linear OR logic. Replacing its output with the two-input subset at each
of r consumers adds r memberships while deleting its four operand
memberships and one active record. For r≥4 this elementary substitution
can increase M−A−1. This is an obstruction to the proposed proof of cost
preservation, not a constructed correct63-gate circuit. A separate
normalization theorem would be needed to impose the anchor soundly.

The future source therefore adds only: active records have nonzero
positive profile; exact singleton profiles are direct primary edge ANDs.
No operand-disjointness or first-AND anchor is added.
