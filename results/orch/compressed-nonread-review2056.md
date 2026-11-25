# A small non-read-one condition for the bounded AND-record model

This is a mathematical review of a necessary condition for the membership-budget synthesis model. It is not a proof of the posted 63-gate existence statement and does not apply from an AND-count bound alone.

An ordered record is the AND of two OR-subsets of primary inputs and earlier record outputs. The final output is an OR-subset of record outputs. Let M count all operand and final-output memberships, and let A count records with two nonempty operands. The model imposes M−A−1≤63. Its final output cannot be false when the full plane tests pass.

Use the literal binary expansion of this model. Propagate false records and remove their references; this cannot increase the expansion cost. Expand each remaining OR-subset independently, and retain every resulting binary AND, including AND(w,w). A record with operand sizes a,b contributes a+b−1 gates, and an output subset of size o contributes o−1. Thus the expansion has at most M−A−1 gates. It is an ordinary backward-reading binary AND/OR circuit computing the same function.

For a fixed incident pair (p,l), each active record output has no proof-count vector (1,0) or (0,1): its proof tree passes through a binary AND with two nonempty subtrees. Consequently an operand OR-subset has a singleton read-one vector only from a directly selected primary input, not through an earlier record. A final selected record has a joint vector (1,1) exactly when its two operand subsets directly contain p and l on opposite sides. The final OR has that vector exactly when at least one selected output record has such a crossing.

The compiled `PEqualNP.Outside.L_meta_2056_aux.SumPlaneReadOne.sum_read_one_lower` theorem gives size≥64 for a read-one circuit computing the full sum-incidence function. The literal expansion above has size≤63, so at least one of the 52 incident pairs must lack both direct crossings in every selected output record. With existential edge flags E(p,l), at least one required true, the constraints are simply

    not E(p,l) or not output_i or not left_i[p] or not right_i[l]
    not E(p,l) or not output_i or not left_i[l] or not right_i[p]

for every record i and every incident pair. These clauses have one common existential edge witness. They do not require a copy of all wire semantics for each edge.

The literal-expansion qualification matters. A cached optimizer may fold AND(w,w) to w, thereby creating singleton or joint read-one traces that were absent in the expanded syntax. Its actual read-one behavior must therefore be measured separately. The necessary condition above is justified by the bounded-size literal expansion, not by an assertion that every optimizing materializer preserves proof trees. A free-OR model with only an AND-count bound has no corresponding total-gate guarantee.

Both proof_route and status_review independently checked this distinction against `ReadK.readVectors` and `TopForm.IsAO2`: binary ANDs may have duplicate operands, and empty proof trees are absent from the chosen expansion. No active query was changed by this review.
