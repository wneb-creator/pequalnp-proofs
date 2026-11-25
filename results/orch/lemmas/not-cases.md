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

### 2026-11-25T14:22:35.751181+00:00: centered OR prefix bounds

Kernel checks passed for TripleOrFragment.lean and all public prefix bounds in PrefixesCached.lean. Three centered ORs with distinct pairwise nonadjacent leaves, and the center adjacent to at least one leaf, force the center to remain live; restriction to false yields 16 remaining binary gates. Thus such a three-gate prefix needs at least 19 binary gates overall. CentralOrCircuitFragment.lean now supplies a direct arbitrary supplied-OR actual-circuit extraction and triple_or_binary. Its flattened light test CircuitPrefixesLight.lean passed (v2 logs), with nineFloor a theorem parameter to avoid recompiling the established certificate.
OrAndFragment.lean and PairOrAndFragment.lean passed separate kernel checks: after OR(a,b), AND(a,c), three distinct inputs force a to remain; when c=b, at least one endpoint remains. Their mass-two lower-bound assembly is in progress. SecondAndFragment.lean passed against the named module, proving 16 tail gates after OR(a,b) and a shared-positive-input signed AND.

### 2026-11-25T14:37:23.213472+00:00: common-t C6 opposite-bank bound checked

CycleBankFragment.lean and CycleBankBoundFragment.lean compile together against the stable named Seventeen module (CycleBankFull-v5 exit0). Theorem cycle_bank_floor proves at least seven additional binary gates for C6 even with all three opposite-pair ORs supplied and arbitrary free NOTs. Six finite row witnesses force all six raw cycle pins to remain live. Two live bank functions then force live-set cardinality at least eight. With at most one bank function, rebuilding it in one gate contradicts the existing Signed.low189 free-NOT lower bound of eight for C6; the relabeling is kernel checked.
CycleBankCircuitFragment.lean supplies the direct actual-circuit bound cycle_bank_binary: 7 + notCount C <= C.size for a FanInTwo circuit computing C6 from six raw inputs followed by the three opposite-pair OR inputs. Flattened CycleBankCircuitLight.lean passed, taking the separately checked cycle_bank_floor as an explicit parameter. Complete logs saved in scratch and submitted to independent reviewer for preservation. This rules out the common-t vector architecture with six fixed OR gates for A,B,C, total13 gates, and any NOT, but does not exclude arbitrary alternate implementations of A,B,C.

### 2026-11-25T14:39:31.550303+00:00: signed17 first-two-gate frontier; paused on lease410

No new unchecked source was produced in this follow-up. For a hypothetical <=19 circuit with2NOT, the signed binary budget is17. The first signed gate must OR (checked nonOR-first lower18). Checked exclusions after an OR(a,b): overlapping OR(a,c) when b,c are nonadjacent in Petersen gives18; raw shared-input AND(a,c) gives19 including c=b via orientation witnesses; dependent AND(OR(a,b),c) and NOT(OR(a,b)) AND c give18. A second independent raw nonOR gate should commute to first position, reducing to the existing18 bound; the interchange lemma is not yet formalized.
Genuine unresolved first-two-gate configurations: two disjoint raw ORs; overlapping ORs whose other endpoints form a Petersen edge; dependent OR of three raw variables; dependent (a OR b) AND NOT c. Redundant cases where a gate reproduces an existing pin also need formal shortening in a universal classification.
Two-variable restriction does not immediately strengthen the bound: in the checked signed9 labeling, low383=13 corresponds to deleting adjacent Petersen vertices9,7; low255=12 corresponds to deleting nonadjacent vertices9,8. These are also expected monotone minima (10edges+cover4-1=13 and9edges+cover4-1=12). Deleting one endpoint of each disjoint OR and charging two retained constants yields only17 or16 binary gates. Thus this route needs another charge; no stronger two-vertex bound was found.
Generic duplicate charging remains invalid, even on triangle-free graph functions: P5 edge function b(a OR c) OR d(c OR e) uses5 gates with c duplicated in a formula, but its distinct-input circuit minimum is also5. A projected duplicate of the first OR output cannot simply be charged as a gate removal.
