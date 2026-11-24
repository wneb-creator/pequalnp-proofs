# Continuation notes for L-meta-3451

The full statement remains unproved. No counterexample to it was found. The named file builds; the exact checker rejects it because its required theorem is absent.

## Strongest available route

Use a globally minimum equivalent monotone backward-reading circuit, then minimize the number of nonedge-dirty ANDs without increasing size. The checked `minimum_dirty_essential` result ensures every residual dirty AND is output-essential for two distinct incident edges. Global minimum size is compatible with this second minimization. The latest gate accepting any input rejected by the output has exactly one contributing AND root in the output OR frontier (`raMinimumReaderOne`). Factoring two such roots would save a gate; having no such roots allows rebuilding the tail without the gate.

The later checked `raAllTailAndRoots` theorem shows every suffix AND belongs to the frontier, and `raMinimumUniqueReader` strengthens the conclusion to exactly one syntactic gate reader of the latest globally unsafe gate. A globally unsafe gate may be an OR, or an AND accepting only a same-side pair; both are allowed by the posted conclusion. It is invalid to assume that eliminating all globally unsafe gates is the goal: a clean star circuit already needs the unsafe OR of its neighbors.

## Concrete missing work

A size-preserving normalization of a whole private cone, with explicit accounting for all shared intermediate wires, remains missing. The partial results do not extract all neighborhood ORs at unchanged cost. The forest theorem, conditional star cleanup, and arbitrary false-input restriction do not supply this extraction.

One promising unformalized scheduling step: a maximal globally unsafe partner V, independent of another maximal unsafe gate U, could be moved after U without changing the circuit size or function. Applying the unique-reader theorem after that rescheduling should give V exactly one contributing AND reader in its new output frontier. The newly checked syntactic-reader strengthening would then make V have exactly one syntactic gate reader as well. This still does not establish privacy of a larger cone or permit moving V past an unsafe descendant. This needs a proved circuit permutation/reindexing theorem and careful treatment of ancestor dependencies; it has not been established here.

A conditional Boolean identity for m nonempty branches is useful. If U = OR_i(A_i AND B_i), V = x OR y, and x implies every A_i while y implies every B_i, then U AND V = (x AND OR_i B_i) OR (y AND OR_i A_i). If both the U cone and V are private, retaining the shared operands costs 2m+1 gates on either side, and the two new ANDs imply the original product. With V shared, the identity U AND V = V AND (OR_i A_i) AND (OR_i B_i) gives a cost-neutral collapse of the m private branch products to one. The two Boolean identities are now checked as `ocFilterSplit` and `ocFilterCollapse`, including empty lists; the gate accounting remains a mathematical observation, not a checked circuit-construction theorem. Neither private-cone existence nor a uniform orientation of all branches follows from the present lemmas.

## Failed shortcuts

For the C4-free path edge function F = ab OR ay OR bx, let A = a OR x, B = b OR y, V = a OR b. Then A AND B AND V = F, but all three pairwise products are unsafe: A AND B accepts the nonedge xy, A AND V accepts singleton a, and B AND V accepts singleton b. Thus a pairwise-safe reassociation lemma is false even for a forest. A clean rewrite exists, so this does not refute the target.

The checked matching and star examples rule out arbitrary one-gate cleanup using only existing earlier wires while preserving the rest of a nonminimal circuit. They do not rule out normalization of a minimum circuit. The multioutput fanout probe likewise does not refute the single-output problem.

## Evidence boundary

Small-case solver outputs are external computational evidence, not Lean lower-bound certificates. All 3-by-3 classes match; 50 of 59 C4-free 4-by-4 classes have matching recorded bounds. Nine classes remain unknown, and all final theta/forced-dirty searches timed out. No timeout was treated as UNSAT.

A further unformalized local cleanup is now structurally justified: if the latest unsafe U is A AND B and its unique reader is U AND V, where V rejects all forbidden singleton/nonedge assignments, replace the two ANDs by A AND V and B AND (A AND V). The partner-order theorem puts V before U, and uniqueness ensures intermediate gates cannot read U. Both new ANDs inherit cleanliness from V, the final product is unchanged, and gate count is unchanged. A general two-gate simulation proof and the existence of such a clean partner remain to be supplied; this does not settle the case when V is itself dirty.
