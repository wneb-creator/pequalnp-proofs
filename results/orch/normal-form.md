# Normal-form investigation: L-meta-2583

The target is not global read-once: ReadK requires every prime implicant to have one proof tree reading each variable once. For incidence, prime implicants are incident point-line pairs.

Existing checked components in the freshly fetched repository:

- `L_meta_4293`: a Lift preserves AO2, valid output, size, and function.
- `L_meta_4295`: Lift reaches the fixed point where an OR cannot mix one below-output operand with one non-below-output operand.
- `L_meta_7649`: for a C4-free bipartite incidence relation, if every non-below-output gate is an OR with non-below-output operands, extract stars covering all edges at total cost at most circuit size.
- `L_meta_2237`: any read-1 circuit for a C4-free graph gives a vertex cover T with |E|+|T| <= size+1.
- `L_meta_4915`: C4-free shared block cost can be converted to ordinary block cost without increase.
- `R_meta_3241_1` separates lift preservation, termination, and residual star-cover cost. First two are now checked above; third is still substantive.
- `R_meta_4297_284` separates fixed-point block extraction and product-block accounting.

The missing normalization step is removal of dirty AND blocks without increasing size. Lift termination by itself does not prove this: a circuit can have ANDs not below its output. Existing one-dirty-gate lemmas (`L_meta_4741` through `L_meta_4747`, `LowerPart`, `LowerPart2`) do not cover arbitrary-many dirty ANDs.

A useful exact route would prove the generic bipartite C4-free conversion, then instantiate plane incidence. But this is stronger than the assigned gap and presently not closed in the library. The plane symmetries/regularity might permit a direct N*(q+2)-1 lower bound, which plus the canonical star circuit would suffice.

Only `PEqualNP.Defs` is desk-authorized, so outside proofs cannot simply be added as dependencies; their needed lemmas must be copied into the one file, under its namespace, if used.

## Primary-source check, 2026-11-25

Read Stasys Jukna, *Disproving the Single Level Conjecture*, author PDF: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . The counterexample graphs in Theorem 2.1 are saturated extensions of bipartite Sylvester-type graphs: each side is made a clique (page 4). Consequently they do not refute our bipartite C4-free statement. Section 8, Problem 8.2 (page 17) asks for a superlinear monotone circuit lower bound for an explicit quadratic graph function. The paper's introduction explains why the standard approximation method does not give such a bound.

Inference: the assigned plane read-1 normalization plus the checked C4-free read-1 edge/cover lower bound would yield order N^(3/2) gates for this explicit incidence family. Thus a complete proof would resolve an open-strength structural obstacle, not merely connect routine library lemmas. Present-day unsolved status beyond the paper is UNVERIFIED; no claim of current impossibility is made.

Scratch `lemmas/normal_prereq.lean` contains self-contained no-input-below-output, valid-output, and gate-output lemmas for arbitrary bipartite incidence functions. Awaiting the shared cache before Lean validation.

Further repository check: L_meta_3679 is a checked refutation of arbitrary bipartite optimal-single-level normalization. Its explicit 39-input graph has a 4-cycle: right vertices 29 and 30 both meet left vertices 6 and 9. This counterexample therefore does not apply to plane incidence. L_meta_8725 (9396 lines) excludes exactly one dirty AND in a least AO2 circuit for any bipartite C4-free graph; it does not exclude two or more.

2026-11-25T15:01:10.434112+00:00 VALIDATED: `lake env lean ../results/orch/lemmas/normal_prereq.lean` exited 0, empty stdout and stderr. 107 lines.

## AND-count route, interrupted by lease loss

Root assigned a separate attempt to prove at least N AND gates for exact plane incidence. Work stopped on root instruction after the renewal failed; this route was not exhausted.

Checked repository evidence:

- L_meta_634 and L_meta_910 establish seven AND gates for the concrete Fano incidence graph, using the AND-count model with free OR gates.
- L_meta_1898 establishes thirteen AND gates for the concrete order-three plane, under incident-pair acceptance and a family of false-input rejections. Its proof is 7334 lines, including finite combinatorial search; no immediate arbitrary-q generalization was found.
- L_meta_217 and L_meta_2399 give the generic C4-free AND lower bound only through vertex-cover number five.
- L_meta_562–566 normalize AND-count circuits (nonempty sides, no singleton acceptance inside gates, live gates, and restriction/deletion accounting).
- The L_meta_1006 eleven-vertex boundary-correct counterexample is non-bipartite, as verified by a BFS coloring conflict from its published adjacency masks. Together with root's full-input check finding 39 incorrect inputs, it cannot refute an exact bipartite plane count bound.

Ideas examined:

1. Counting maximal false inputs gives only a logarithmic lower bound on the AND count. The naive bound is too weak already for Fano, and does not produce N.
2. Restriction to an induced matching provides only roughly q-sized witnesses in a plane; a perfect matching is not an induced subgraph and cannot be obtained by simple monotone variable restriction.
3. At the all-point and all-line assignments, every wire has one of four value types. Pure cross ANDs produce rectangular pair contributions; C4-freeness forces each valid such rectangle to be a star. The obstruction is mixed gates and later filters: assigning all accepted edges to their first AND is unsound, because a dirty AND can also accept nonedges that later gates reject.
4. Existing order-three proof uses donor/signature combinatorics across many maximal false inputs, consistent with this obstruction. No proof of the necessary arbitrary-q charging principle was found before interruption.

No new Lean file was generated for this count route. The previously validated 107-line normal_prereq.lean remains the only compiled contribution of this agent.
