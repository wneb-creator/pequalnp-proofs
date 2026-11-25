# L-meta-2583 library review

## Exact meanings

- `PEqualNP.TopForm.IsAO2 n C` is AND/OR only, reads only earlier wires, and **exactly two** operands per gate. Repetition is allowed; there are no constant gates.
- `PEqualNP.ReadK.IsReadK n C 1` is **not** global read-once circuitry. For every prime implicant, it requires existence of a proof tree in which every implicant variable appears at most once. For the incidence function, prime implicants are the incident point/line pairs.
- The vector recursion is joint: one tree must bound both point and line counts simultaneously. Separate scalar minima are insufficient.
- The assignment is not open to reductions (`lease.terms.reductions_open=false`), despite its sketch requesting a cut. Only root may resolve desk flow.

## Checked reusable components

- `L_meta_7684.lean` (1126 lines): from an arbitrary bipartite edge set E and a vertex cover A,B, builds an IsAO2 circuit computing E, of size at most |E|+|A|+|B|-1, and read-1. Only Defs/Mathlib imports may be retained when copying its proof.
- `L_meta_6579.lean` (378 lines): a circuit whose AND operands come from pure point-OR and line-OR wire families is read-1. This is the read-1 component used for star constructions.
- `L_meta_4897.lean` (1961 lines): for C4-free bipartite E, any **already read-1** IsAO2 circuit computing E yields a cover with |E|+|A|+|B| ≤ size+1.
- `L_meta_7639.lean`: for C4-free bipartite E with a perfect matching, any **already read-1** IsAO2 circuit computing E has |E|+N ≤ size+1.
- `L_meta_6369.lean` (1397 lines), also L_meta_2237: corresponding read-1 lower bound for arbitrary C4-free graphs.
- `L_meta_7344.lean` (399 lines): any monotone fan-in-at-most-two circuit with only quadratic prime implicants can be repaired to read-1, but its bound is 3*(original size + number of bad implicants +1), not the required no-growth bound. It does not imply the assigned statement.
- `R_meta_4895_1`, `_215`, `_628` split the general C4-free bipartite normalization theorem into a general circuit/cover lower bound and star construction. Their lower-bound hypotheses omit read-1 and remain the relevant hard part; these reductions do not establish those hypotheses.

## Mathematical consequence and obstruction

For a projective plane incidence graph, star-cover construction has size N*(q+1)+N-1 = N*(q+2)-1. Read-1 lower bounds attain the same number because the regular bipartite incidence graph has a perfect matching. Therefore the assigned no-growth normalization would follow from the exact unrestricted monotone circuit lower bound N*(q+2)-1. Conversely any smaller IsAO2 circuit would refute it once the read-1 lower bound is instantiated. For q=2 this threshold is 27 gates on 14 inputs.

No checked no-growth normalization theorem was found among the 36 read-1-related proof/reduction files. Complete extracted theorem statements are saved in `/tmp/oec/pequalnp-pilot-118/readk-statements.txt`.
