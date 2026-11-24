# Conditional checked bound from L-meta-1407

This addendum supplements the frozen NormalForms.md. It records an existing
repository theorem and distinguishes its hypothesis from the posted L-meta-1482
statement. It does not claim a proof of L-meta-1482.

The inspected source lean/PEqualNP/Outside/L_meta_1407.lean ends with theorem
PEqualNP.Outside.L_meta_1407 (line843 in the inspected checkout). For a finite
simple C4-free graph G and an AND/OR circuit of fan-in at most2 computing its
edge function, it assumes that EVERY AND-gate output is globally safe: whenever
that gate is true on any complete input assignment, the graph edge function is
true. It concludes the existence of a vertex cover T satisfying

    |E(G)| + |T| <= number of gates + 1.

The gate-safety hypothesis applies to AND outputs. OR gates and the operands of
AND gates may be globally unsafe. It is stronger than the hypotheses posted for
L-meta-1482, which do not require AND safety. Applying the theorem without proving
that additional hypothesis would be invalid.

The proof separates two resource inequalities. Let S(w) be the singleton support
of wire w. Classify an OR as wide when |S(w)|>1, and narrow when |S(w)|<=1.

* edge_finset_gate_bound (lines680-696) bounds |E(G)| by the number of AND gates
  plus the number of wide OR gates, under its explicit support-model hypotheses.
* cover_half (lines533-553) constructs a cover of size at most one plus the number
  of narrow OR gates, under its explicit DAG/edge-propagation hypotheses.
* total_from_model (lines795-837) obtains these support hypotheses from its model,
  proves the small-side consequence of C4-freeness, and combines the two bounds
  with gate_partition_count (lines479-515).
* The final theorem supplies the model from the actual circuit, including the
  global AND-safety assumption. These are proved declarations, unlike the
  statement-only StmtLift and similar propositions in EdgeFnPlan.

For the order-3 plane incidence graph there are52 edges. The13 diagonal incidences
u=t are disjoint edges, so every vertex cover has at least13 vertices; the point
side itself is a13-vertex cover. Thus the checked conditional theorem gives

    size >= 52 + 13 - 1 = 64

for the subclass with globally safe AND outputs. It gives no strict inequality
merely from the extra double-re-read condition.

Both known65-gate boundary circuits belong to this subclass. The first Shannon
circuit has only point-star AND gates and the final AND computing the whole
function; all are safe. In the second local-core circuit, every AND also computes
an edge disjunction. Some shared OR intermediates are unsafe (for example the OR
of a line singleton and an already mixed edge term), which is permitted by the
conditional theorem.

Their resource counts show why strictness cannot be assigned to only one of the
two inequalities. The counts below were independently computed directly from the
actual gate lists and singleton-support recurrences S(AND)=intersection and
S(OR)=union; they are a finite Python diagnostic, not a new Lean counting lemma.

| Circuit | AND | wide OR | narrow OR | Edge allowance | Cover allowance |
|---|---:|---:|---:|---:|---:|
| Shannon65 |13|40|12|53|13|
| Local-core65 |14|38|13|52|14|

The first circuit has one unit of slack in the edge inequality and a tight cover
allowance. The second has a tight edge allowance and one unit of slack in the
cover allowance. Both have the extra double-re-read behavior on an incidence.
An equality-rigidity proof would therefore need to exclude simultaneous equality
in both inequalities, not prove that one fixed inequality is always strict.

Even such a rigidity result for this subclass would leave arbitrary circuits
with an unsafe AND output unresolved. No normalization removing unsafe AND gates
while preserving the required gate budget and double-re-read property is proved
here.

Inspected artifacts:
- lean/PEqualNP/Outside/L_meta_1407.lean
- /tmp/oec/pequalnp-pilot-20/search/shannon65-full.json
- /tmp/oec/pequalnp-pilot-20/algebraic/shared-cover/local-types/calibration-core6-certificates.json
