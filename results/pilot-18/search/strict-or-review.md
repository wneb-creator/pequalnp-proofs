# Strict noncopy prefix OR: normalization and code review

Verdict: PASS. This restriction is on the eleven singleton and sixteen edge
rows, and applies only to noncopy OR gates in the clean prefix. ANDs and
syntactic OR copies remain exempt.

If OR(A,B) equals A on those rows, replace the gate by an alias of A and remove
it. Equality on singleton rows preserves the support and therefore all values
on independent inputs by the clean-prefix support lemma. Equality on the edge
rows preserves their values. Every later Boolean gate preserves equality on
these rows under the redirected references. Thus the output remains true on
all edges and false on all maximal independent sets, hence still computes the
exact monotone graph function. The symmetric replacement applies to B.

This does not require equality of the intermediate functions on other positive
inputs. Such equality must not be claimed in a formal proof of this reduction.

Every replacement deletes a noncopy core gate. Alias removal, duplicate removal,
productive-AND normalization, clean-wire dominance elimination, pruning and
re-sorting can be repeated together; every violation that needs a rewrite
decreases the number of core gates. After all core tests pass, append the
reviewed final OR-copy chain from the highest live core gate. Its gates are
exempt copies. This restores length 17 and liveness without disturbing strict
ORs, productivity, dominance, distinct descriptions, or lexicographic order.

Support-cost restrictions remain valid by their universal lower-bound theorem;
the normalization leaves the graph computation correct and the prefix clean.
No additional assumption about minimum-size circuits is used.

The source records the already-existing operand support and edge literals as
two 27-entry boundary vectors per prefix gate. For each gate, the same-source
flag is equivalent to equality of the two one-hot selector vectors. For each
coordinate, two directional witnesses imply respectively A=1,B=0 and B=1,A=0.
The clauses (AND OR same-source OR some A-only witness) and
(AND OR same-source OR some B-only witness) demand both differences exactly
for a noncopy OR. Reverse witness implications are unnecessary for existential
satisfiability.

There are 17 same-source flags and 17*54=918 directional witnesses: 935 new
variables. The selector equalities contribute 3*sum(13+g,g=0..16)=1071 clauses;
witnesses contribute 17*108=1836; final guards contribute 34. Total: 2941.

The JSON companion records the source hash, exact generated-clause audit,
finite gadget checks and integration with all seven cases. No solver or
repository mutation is part of this review. The normalization is mathematically
reviewed, not yet Lean-formalized.
