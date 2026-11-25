# Adjacent ordering normalization

This is an informal mathematical argument, independently reviewed by repo_audit and algebraic_witness. It is not a Lean proof.

Fix the52 required positive inputs and a canonical circuit representation: an OR operand with positive signature S is the conjunction of every earlier input/OR wire whose positive signature contains S. Let consecutive OR gates A,B have output-positive signatures U,V. Suppose neither operand signature of B is contained in U. Then B's canonical operands do not use A.

Move B before A. B sees the same usable earlier wires and remains unchanged. A may now include B in one or both canonical conjunctions. Every such new factor contains the corresponding positive signature, so A keeps its positive signature while its value on every input can only decrease. Later inclusion sets depend only on the unchanged positive signatures; induction through monotone gates shows that later values, including the final output, can only decrease. Thus all required positive and negative tests remain satisfied.

When U>V as unsigned positive masks, this swap strictly decreases the lexicographic sequence of output-positive masks. There are only finitely many permutations, so repeated independent inversion swaps terminate. The resulting circuit satisfies U_i≤U_{i+1} unless an operand signature of gate i+1 is contained in U_i.

The implementation starts with the adjacent pair at indices1,2, leaving gate0 fixed. Thus it preserves the separately imposed representative of the first-OR symmetry orbit. Operand incomparability and gate count are unchanged. Other semantic constraints, including the necessary dirty-singleton condition for at most50 gates and the cover cuts, remain justified by their independent necessary-condition arguments.

This existence argument concerns unrestricted circuits. It must not be used to exclude candidates in an arbitrary fixed-position template. Fixed control signatures are normalized before they are pinned.

The finite audit checks every swap on all546 prescribed samples for a valid51-OR control (207 swaps) and an invalid48-OR seed (179 swaps). Their error counts remain0 and378. A separate exhaustive512-case three-bit truth table validates the unsigned comparator/dependency clause. Neither finite check proves the posted51-OR lower bound.
