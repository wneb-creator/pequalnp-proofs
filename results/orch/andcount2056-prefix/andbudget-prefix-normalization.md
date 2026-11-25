# Active-prefix and one-input symmetry for the bounded-cost model

This is a separate future refinement of the approved profile-only source.
The live solver source remains unchanged. No target witness is claimed.

After zero-positive records are cleared, every active record has a true
positive row. Delete references to inactive false records, retain active
records in their original topological order, renumber their references,
and pad with empty inactive records at the end. Each active operand
remains nonempty: on a true positive row it has some true source, which
cannot have been an inactive false record. Drop inactive output selections
as well. M cannot increase; A is unchanged, so M−A−1 cannot increase.

The first active record now uses only primary inputs. Select an input v
from its left operand. For a point v, the Singer translation
p→p−v, l→l+v sends it to point0 and preserves the sum-incidence relation.
For a line v, first swap the point and line parts, then use the analogous
translation. This permutes input labels bijectively and preserves every
operand/output membership count. Restore point-left/line-right orientation
for each singleton-profile record by exchanging its two operands. If the
first record is singleton, its left primary was already a point, so the
chosen translation leaves its left endpoint0; otherwise its profile is
not singleton and this restoration does not affect the first record.

The resulting constraints are: active records form a prefix; selected
output records are active; the first record's left operand contains
primary0. No right-side unit or operand-disjointness rule is used.

The reviewed normalizer checks every one of756 boundary rows. Nested and
near63-gate models retain their exact cost63 with6 and3 misses respectively;
the latter exercises point/line duality. A rotated13-star control with
inactive gaps and false references compacts from accounting bound121 to64
and remains correct on all756 rows. These are normalization controls,
not63-gate witnesses.
