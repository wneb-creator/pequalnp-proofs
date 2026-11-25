# NOT-case route

- Initial L-meta-2592 cuts leave 1..4 NOTs after the checked binary floor15.
- L_meta_5236 internally has a free-NOT binary floor15 on Petersen-minus-vertex and floor16 for Petersen with a supplied nonedge OR. The reductions agent adapts this to ordinary circuits.
- New Lean-checked helper: the first normalized binary gate in an ordinary Petersen derivation must retain BOTH of its raw input operands. This uses a table of360 concrete row pairs, kernel-checked, and the existing Live row-difference invariant. For a given pair a,b and operation d, the two rows differ only in a, have equal gate output, and different target output. Thus a remains in the tail; swapping operands also retainsb.
- Checked self-contained file: /tmp/oec/pequalnp-pilot-95/not-cases/TwinBothLight.lean. Compiler exit0; logs TwinBothLight-v2.stdout and .stderr are empty.
- Mergeable fragment: /tmp/oec/pequalnp-pilot-95/not-cases/TwinBothFragment.lean. Namespace PEqualNP.Outside.L_meta_2592.Signed.Extended; no forbidden source forms.
- Proof-route agent is combining retained-input projection with nine-floor15 to establish ordinary binary floor17, excluding >=3 NOTs for total size19.
- Potential improvement: first AND or mixed-AND gate can be killed by a false input restriction, yielding both a retained constant input and constant first gate in the tail. Static mass2 plus spent firstgate suggests floor18 for these cases. First OR gives a duplicate variable signal rather than a second constant; duplicates alone do not justify an extra charge because fanout is free.

## OR-first follow-up

- Census:770 nine-input proof files inspected; no final theorem excludes16total gates or proves17size for Petersen-minus-vertex. Existing0/1/2NOT cases exclude15total.
- No complete supplied-adjacent-OR18gate bound located; checked10-input prefix claims are largely format/empty-suffix cases or3+NOT bound L5236.
- New kernel-checked OverlapFragment.lean: if two supplied roots are(a OR b),(a OR c), and b,c are nonadjacent Petersen vertices, every residual derivation must retain rawinput a.480 explicit rowpair witnesses checked. Lean OverlapLight.lean exit0, empty stdout/stderr.
- If b,c ARE adjacent, a can semantically be discarded: replace a by(a OR b)AND(a OR c)=a OR(b AND c). Any changedassignment already containsedge bc and forcesoutputtrue. Thus a blanket two-overlapping-OR retention statement is false.
- This gives a useful route toward binaryfloor18 in the nonadjacent-overlap case, by projecting a=false and charging two spentORgates plus one retainedconstant.
