# Scope of counterexamples and finite searches

None of the counterexamples below refutes the posted gap L-meta-5012. The missing ingredient in the geometric shortcuts is leastness or a global circuit resource argument.

## Kernel-checked circuit examples

- `../lemmas/antecedent_cycle_six.lean`: an eight-gate AO2 circuit for C6 with no junk. This is an upper bound, not a minimum-size theorem.
- `../lemmas/antecedent_cycle_six_two_junk.lean`: an eleven-gate circuit for C6 with exactly two junk gates and a clean same-side top accepting three disjoint edges. The file explicitly proves the circuit is not least using the eight-gate circuit. It excludes extending the four-clause matching bound to arbitrary same-side tops.
- `../lemmas/antecedent_star_dichotomy_counterexample.lean`: a six-gate circuit for P4 (edges02,03,12) built from g=(0 OR1) AND(0 OR2), h=(0 OR1) AND(2 OR3). It computes F, has exactly two junk gates, and both products guard every edge. Neither whole accepted-edge set is a star; g is not a disjoint flag. The file explicitly proves nonleastness using a four-gate circuit. Even deleting the middle edge02 leaves a two-edge matching. This rejects only the proposed star-or-two-flags geometric shortcut without leastness.

## Computational geometric counterexamples

The programs use all Boolean assignments of the stated finite graph. A pure-product pair is not, by itself, a complete least circuit.

- P5 disjoint-arm example: E02,04,12,13; g=(0 OR1) AND(2 OR3); h=(0 OR1 OR3) AND(2 OR4). Joint cleanliness holds, but neither complete accepted-edge set is the prescribed original-arm clean star and h is not a flag. Distinguished flag centers need not exhaust wmax: g has cleaners1,2,4. No circuit leastness claim is made.
- C6 triple-factor example: g=(0 OR1 OR3) AND(0 OR2), h=(1 OR2 OR4) AND(3 OR5), wmax sets{1,5}/{0,4}. Their conjunction is clean and shared edge23 avoids both cleaner sets, yet g AND either single h arm is dirty. These conjunctions need not compute the whole graph function.
- P5 guarded-matching example: E02,04,12,13; g=(0 OR1) AND(0 OR2), h=(1 OR4) AND(2 OR3 OR4). h accepts disjoint g-guarded edges04,12; Joint holds, but both triple factors are dirty. Removing edge13 leaves a graph-edge subset entirely g-guarded. That subset is not asserted to equal the actual Ustar of an exhibited circuit.
- Theta333 accepted-union example: edges02,23,31,04,45,51,06,67,71; g=(1 OR2) AND(0 OR1 OR3), h=(0 OR5) AND(2 OR3 OR4 OR6). Joint holds and shared edge02 is residual. The accepted union contains matching23,45,06,71. Edge06 is accepted only by h and is unguarded, so this does not refute a three-center cover for actual Ustar.

## Positive finite evidence and scope limits

The corrected admissible-edge set guard(g) union guard(h) union common(g,h) had no four-edge matching across all384 eligible C8 and3648 eligible theta333 pairs tested. Each product has wide incomparable arms, g has exactly one overlap vertex and one internal cleaner, r is outside both h arms, Joint holds on every assignment, and there is a common edge outside both guarded sets. These two finite graph tests do not establish a general cover theorem.

The five-independent-assignment certificate is different: its21 table entries and exhaustive512-matrix check were formalized and kernel-checked in `../lemmas/antecedent_five_independent.lean`. Its exact formal conclusion, not the search log, is authoritative.

## Solver outcomes

Completed critical-row C8/theta333 synthesis runs returned UNKNOWN at600seconds, and other finite UNSAT or timeout results are individually scoped in README. The later normalized20-minute C8/theta333 attempts were INTERRUPTED by the execution-environment restart, before any solver result. Their metadata-only logs do not support UNKNOWN, SAT, or UNSAT. No solver remains running.

## Remaining proof frontier

The checked helpers provide ordered two-junk normal forms, exact pure-product cleaner geometry, residual independence, star covers and OR-resource bounds, first-rung-preserving rewrites, and reused-star packaging. The unresolved step is a global assignment of every Ustar edge to guarded and mutual components with a single nonduplicated resource budget strong enough for the master surgery contradiction, including nested and guarded cases. No file in this search folder is a completed proof of L-meta-5012.
