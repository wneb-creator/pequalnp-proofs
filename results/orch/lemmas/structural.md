# Structural strategy for L-meta-2583

ReadK is per-prime proof-tree multiplicity, not total circuit reads. For a projective-plane incidence graph the candidate normal read-1 realization has E + N - 1 = N(q+2)-1 gates. The hard step is showing mixed dirty blocks of arbitrary monotone circuits cannot improve this budget; existing least-circuit normal form only excludes AND inputs already below the output function.

Existing nearby result L_meta_2581 proves an Omega(Nq) lower bound assuming read-3. Its proof-tree encoding is reusable but not imported by Defs.

Prepared Structural.lean in job scratch with pair_prime, prime_iff_pair, read_iff_pairs. These need compilation once Lean executable is resolved. They characterize exactly the prime implicants and reduce read-k to incident pairs without using plane axioms.

## Exact lower-bound bottleneck

For read-1 circuits, L_meta_4897 obtains a vertex cover with |E|+|cover|≤size+1; L_meta_7639 gives |E|+N≤size+1 with a perfect matching. L_meta_7684 gives the matching read-1 upper construction. Thus the conjectured normalization amounts to the exact unrestricted AO2 bound N(q+2)-1.

A possible counting route is to restrict to each line alone. The output is OR of q+1 point inputs and needs q effective OR merges, totaling Nq across lines. Pure-point merges can serve only one line by pair uniqueness. The unresolved issue is mixed gates whose surviving point sets vary with the line restriction: one OR may merge different point pairs at different lines. Any proof must account for this reuse rather than assert it impossible.

Prepared least_equivalent as an additional generic Nat.find lemma, reducing arbitrary circuits to minimum-size equivalent representatives.

## Normal form obstruction

A child strategy checked all16 assignments for the7-gate formula ((a OR y2) AND (b OR y1)) AND (a OR b) AND (y1 OR y2), computing the matching function a*y1 OR b*y2. Every proper gate is not below the output; yet each prime-pair proof repeats both endpoints. The3-gate canonical read-1 circuit is smaller. Thus the below-F lifting normal form alone does not imply read-1, and minimum-size must drive a global replacement. Child note is in job scratch structural/dirty-blocks.md.

## Lean validation

2026-11-25T15:04:48.692555+00:00: Structural.lean (131lines) and MatchingObstruction.lean (37lines) both compiled on first attempt under Lean4.36.0 with PEqualNP.Defs as sole import. Exit0, no warnings or diagnostics; complete logs are the corresponding .log files in scratch. No full proof or refutation of L-meta-2583 has been obtained.
