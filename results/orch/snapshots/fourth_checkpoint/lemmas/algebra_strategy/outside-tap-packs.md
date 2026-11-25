# Conditional outside-row tap packs

An exact29-gate k6_p3 core with a conditional OR of two lines belonging to an outside row suffices for the full63-gate target: append that row with four gates and the other six rows with five each. The tap only needs to equal Q when the core output is false. For monotone taps this is equivalent to Q<=T<=Q OR F_core.

k6_outside_pair_taps.json contains all19 pairs. They split into the special hub pair6,11 through original point9 and18 disjoint grid-line pairs through the other six outside points. The special case has91 care assignments, the others96. Every pack contains the complete76-test core basis, designated-line singletons, and all maximal core-negative assignments with the designated lines fixed false. This is complete for monotone tap correctness by monotonicity. All30-gate baseline circuits were checked against their packs.

For original point9, local6 and11 map to full13 and20. The remaining full neighbors are17 and18. The completion takes OR(tap,x17,x18), AND withx9, then OR with core output, costing four gates.

k6_outside_triple_tap.json contains representative outside point4, local lines13,14,16 (full22,23,25), with101 care assignments and37 tap-zero maxima. Target30 joint gates; verified baseline31. Its fourth neighbor is full18, so completion costs three gates and the remaining six rows cost30:30+3+30=63.

The pair generator initially wrote a duplicate one level above this folder. The canonical generator and artifacts now live in this algebra_strategy folder; the old duplicate was retained because a collaborating encoder was reading it.

No search process was started by these generators.
