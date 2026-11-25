# Further equality deductions for p10 I0123, Bplus 14

These are mathematical proof sketches checked with algebraic_route, not new Lean theorems. They assume the exact eight-mask family shape from the separate Python parent/closure census and the actual-circuit count saturation. They do not imply that a circuit is a formula.

Let P be all seven line inputs, Y the four required triples plus one pair per triple, Lab the six lines other than 0, S the singleton-witness labels in equality_count_mask_family, X the chosen outside-pair image, and C the witness-cost image in sup_count.

The count chain is tight:

- The P-carrier flow is at most 18, from seven inputs and at most eleven supported surplus units.
- big ≥ 8 + |X|.
- sup_count gives 2(big + 4) + 2|S| + (6 − |S|) ≤ 36.
- Fiber counting gives 6 − |S| ≤ 2|X|.

Thus 2|X| + |S| = 6, big = 8 + |X|, and all intermediate capacities are exact.

Each selected outside pair's fiber has exactly two labels and is contained in that pair, hence equals it. Distinct fibers are disjoint, so X is a matching on lines 1–6. Any further occurring outside pair would give an additional distinct big mask, contradicting big = 8 + |X|. Thus all occurring outside pairs belong to X. This does not eliminate the 49 residual models: 37 have no outside pair among their unit masks, and 12 have exactly one.

No singleton-output P-carrier merge can remain. Every sup_Wit operand has projected-mask cardinality at most two. A singleton-mask witness loses its sole P label, so necessarily exits P. Every other witness cost must carry two distinct labels by the tight weighted-fiber count. At a singleton-output merge with output label t, two distinct lost labels f,g would require occurring outside pairs {t,f},{t,g} on opposite operands. The same operand cannot lose both labels while still outputting t because of that two-label operand bound; accepted sup_wit_same_pos supplies this fact. These two pairs contradict the matching. Tightness of the master cost partition then excludes unused singleton-output merges too.

Every big merge is the first and unique sup_big merge for its projected mask (not the unique wire carrying that mask): there are exactly as many big gates as occurring nontrivial masks Y ∪ X. An AND producing a mask of size at least two would equal one parent's mask, because distinct required triples intersect in at most one label and all other allowed nontrivial masks are pairs. This would repeat an already occurring big mask. Hence no big AND is possible.

Together, these facts imply that EVERY AND output has EMPTY projected line singleton support. Moreover, each big OR merges disjoint projected line masks: an output pair comes from distinct singletons; an output triple must use its unique contained pair plus the remaining singleton. Two distinct contained pairs cannot both occur inside one required triple. Unary line-carrier ORs with one empty-P input also have disjoint projected supports.

The remaining gap is that unary ORs may add point-supported or zero-singleton functions to a line carrier. Therefore line carriers need not compute plain line ORs. Protected-star deletion and preservation of eligible point labels are NOT established. The simple residual singleton model survives every proved finite constraint.

## Eligible-point residual masks

The separate stochastic-p10-fourunit-point-masks.json gives necessary possibilities for one eligible point's residual coordinate set in each of twelve canonical unit classes. The three-slot-full lemma applies when a neighboring line has residual cardinality at most one and at least two ineligible point neighbors. Nonempty-source co-label then forbids assigning an eligible point to such a full star; assigned_budget_extra bounds the remaining forced assignments.

Only the simplest class [1,2,32,64] forces all four assigned stars full and every eligible point's residual set empty. Three other classes force points 0 and 2 full and allow each eligible point only the empty set or one of three residual singletons. The other eight classes have no full star forced by this criterion. These are necessary per-point tests, not jointly realized full-support models.

Independent review status: algebraic_route agreed with the matching, absence of singleton merges, AND-output, and disjoint-input deductions. status_review found no flaw in the conditional sketch and emphasized the witness operand-cardinality bound and the distinction between unique big merges and repeated unary-OR wires. The argument remains unformalized.
