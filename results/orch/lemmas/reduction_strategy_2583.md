# L-meta-2583 alternative strategy and normalization

Started 2026-11-25 14:42 UTC. Root alone holds and renews the new lease. No reduction is submitted because the desk has reductions_open=false.

## Definitions and missing theorem

IsReadK means that every prime implicant has some proof tree reading each variable at most k times; it does not require each input wire to have global fanout one. IsAO2 requires AND/OR only, exactly two operands per gate, and all reads from earlier wires. The incidence hypotheses and these definitions reveal no degenerate interpretation making the statement immediate.

The library agent found the canonical star-cover constructor L_meta_7684 and the READ1 lower bound L_meta_7639. Together they make the task equivalent to proving the unrestricted AO2 lower bound N(q+2)-1 on a plane. The exact missing work is the cost of blind AND gates, not the existence of a READ1 circuit.

## Completed checked normalization stage

Frozen scratch source:

- Blocks.reviewed.lean: 77,534 bytes, 1689 lines, SHA256 4e970ab329f1ea90a5a2d60799f21e0ca21510fdd03a44fb5b91dd0d80d96a5c. It contains the checked lift and generic block theorem.
- Blocks.lean: 80,511 bytes, 1749 lines, SHA256 b2e852164e257d645b2c95522167ed860a13ca53cb0c66b9755418166a247ec9. It adds the incidence-specific hypotheses discharge. Complete incidence-blocks.stdout and incidence-blocks.stderr are empty; lake env lean exited zero. Root was alerted immediately.

Both files live under /tmp/oec/pequalnp-pilot-99/gap2583/reduction_strategy and are frozen. Future changes must use new filenames to prevent review races. The first-version assembler is assemble_blocks.py; the appended source is IncidenceBlocks.append.

The source copies and renames three already-checked library components into the L_meta_2583 namespace, with only PEqualNP.Defs as the dependency:

- L_meta_4293: one lift preserves AO2, valid output, function, and size.
- L_meta_4295: lifting reaches a fixed point where an OR with one below-output operand has both operands below output.
- L_meta_7372: separate such a fixed point into a blind interior circuit D and product blocks B with D.size + 2*B.length <= C.size+1.

New liftClosure composes step correctness along the finite lift sequence. New blocksAfterLifts combines normalization and separation. New incidenceInputsNotBelow uses a singleton assignment to rule out an input below the incidence function; incidenceOutputValid uses a nonempty incidence edge and the all-true input to rule out an invalid output. New incidenceBlocks therefore applies directly to any nonempty bipartite incidence function and its computing AO2 circuit, with no plane axioms required: every interior gate accepts some negative input, the output is precisely the union of the product blocks, and the exact budget above holds.

This is a partial proof of the first stage of the desk sketch, not a proof of the posted statement.

## Remaining structural sources

- L_meta_7649 (42.5 KB) obtains a no-more-expensive star cover when every gate not below output is OR and has no below-output operand.
- L_meta_4742 / L_meta_4747 remove one exceptional blind AND under additional singleton-partner or empty-edge conditions. These do not eliminate arbitrary collections of blind ANDs.
- L_meta_7344 constructs a READ1 equivalent for arbitrary quadratic monotone functions, but its bound has a factor of three plus a penalty for deficient prime implicants, so it does not give the requested no-size-increase result.

The residual product-block cost statement is written explicitly in R_meta_4297_284. The already-proved separation hypothesis of that reduction is now composed with the lift stage above. The other hypothesis remains unproved: charge a star cover to D.size+2*B.length-1 when every gate of D is blind.

## Core-cover caution

Repository refutations L_meta_3446, L_meta_3444, and L_meta_2969 disprove nearby versions of the core inequalities. L3446 refutes the edge-plus-cover inequality when the cone-gate budget keeps only gates with no outside reader. It assumes a lift fixed point and all gates in the output cone, but not least size. Its witness has 17 gates for a graph with four edges and a six-gate star construction, so it does not refute a least-circuit variant. L2969 refutes the complementary budget using unfiltered whole cones. The U definition in any proposed pair of inequalities must be matched exactly; neither inequality can be transferred between filtered and unfiltered cones without proof.

## Further minimality and removal inventory

- L_meta_1485 (27.7 KB): in a least AO2 circuit for a nonempty graph, each non-output below-F gate has exactly one reader, and the reader is OR. Thus no below-F gate feeds an AND. This rules out the borrowed implicant-gate uses in the nonminimal core counterexamples.
- L_meta_1499: if a below-F AND lies in another AND cone, change to another least circuit at equal size with fewer andPairs and the same junk count.
- L_meta_1498: in TopForm, the unique OR reader of a below-F gate is also below F, and orT.card+1=tops.card.
- L_meta_3653 eliminates a sole junk AND that accepts a singleton, without increasing size.
- L_meta_3700 handles a sole junk AND in a least lift-fixed circuit when all AND gates reject singletons, producing no AND-in-AND cones at equal or smaller size.
- L_meta_5412 excludes exactly two junk ANDs in a least lift-fixed circuit when both have an explicit double-star rectangle form. Its copied source is about432 KB, so indiscriminate assembly would hit the per-file limit.

For the edge-invisible-gate removal assigned to sat_encoding, L_meta_4747 supplies the exact AO2 surgery. p40cf forces a gate false, p40_le and p40_eq_all compare evaluations, p40_find finds a later OR with a forcedfalse operand unless the output itself becomes false, and p40_ge plus p47_isAO2_erase bypass that OR with a strict size drop. The main_aux proof at2061--2156 is the template. This avoids introducing a free false constant into the strict AO2 result. The relevant path and declaration names were sent directly to sat_encoding.

## Sharper first-star induction obstruction

Root proposed removing one clean input edge or private clean star, paying for the removed incidences plus at most one unit of vertex-cover loss. The completed edge-visibility argument would force a first AND on two distinct original inputs to be a clean incidence edge; repeated inputs are removed separately by idempotence. For a first AND of larger pure-OR operands A and B, visibility only ensures an incident cross-pair. A dirty rectangle can still contain nonincidences or singleton terms from A intersect B. Boolean factoring can save a gate when its OR cones are private, but shared OR cones obstruct that local argument. No theorem making a first dirty rectangle clean was found.

A plane-specific possible source of slack is that every inclusion-minimal mixed vertex cover costs at least N+q, whereas an entire-side cover costsN. Lower_bound found a promising proof using the regular induced incidence graph obtained by removing a nonincident point-line pair and their neighborhoods. The missing bridge is still to charge arbitrary shared blind cores to such a mixed cover; no implication from the geometric bound alone is claimed.
