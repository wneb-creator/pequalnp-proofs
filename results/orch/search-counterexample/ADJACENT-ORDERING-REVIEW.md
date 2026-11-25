# Independent adjacent-gate ordering review

Reviewed by algebraic_witness, 2026-11-25. This concerns the unrestricted canonical finite SAT model, not a Lean theorem or a fixed-position repair template.

Let the positive signature of OR gate i be U_i. After the fixed first OR, it is safe to require U_i <= U_(i+1), in the chosen total order on masks, unless at least one operand signature of gate i+1 is contained in U_i.

If neither later operand signature is contained in U_i, neither of its canonical conjunctions uses gate i. Swap an inverted adjacent pair. The moved earlier gate is unchanged. The moved later gate may now include the other output as an extra conjunction factor whenever its operand signature is contained in that output signature. This preserves its positive signature and can only reduce values on negative samples. All later canonical inclusion decisions depend on the unchanged positive signatures, so all later negative values likewise can only decrease.

The swap preserves the separator property, gate count, and initial fixed-gate symmetry representative. Each swap strictly decreases the finite lexicographic sequence of positive signatures. A minimal such sequence therefore satisfies the proposed adjacent ordering condition.

The argument does not establish a normal form within a template that pins positions or gate operands. Additional semantic cuts must separately remain necessary for the resulting circuit. In particular, the dirty-singleton cut remains necessary for a valid circuit with at most 50 OR gates, but a deliberately dirty 51-OR positive control is not a universal semantic condition at that larger budget.
