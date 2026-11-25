# Library route: L-meta-4675

- No current accepted Outside theorem directly establishes a bound from `TwoColour.tCount = 0`.
- Only exact `TwoColour.tCount` Outside occurrence is `L_meta_4791.lean` (1414 lines). It compiles any AO2 circuit vanishing on one-hot inputs into another with T=0, at cost D.size+4 <= 6*C.size. Thus the T=0 condition still includes a rich circuit class.
- `L_meta_2237.lean` and newer `L_meta_6369.lean` establish the desired general C4-free cover bound for `ReadK.IsReadK n C 1`. This additional condition is not implied by T=0 syntactically.
- `L_meta_4897.lean` gives the bipartite form with separate point/line covers, again under ReadK 1.
- `L_meta_7639.lean` gives |E|+n under a perfect matching, again ReadK 1.
- `L_meta_5785.lean` (461 lines) constructs an AO2 circuit of size <= |E|+|cover|-1 from a bipartite cover (upper bound, not lower).
- `R_meta_4297_284.lean` reduces a related bound to separating below-output gates and turning remaining products into star families; both pieces are hypotheses.
- `L_meta_4183.lean` gives top-form charge inequality |E| + tops_nonempty + 2*centreless + junk + (orN minus lam) <= C.size+Ustar+1 for least AO circuits. Remaining residual Ustar/cover charge is substantial.
- General lower bound in Helpers/EdgeFnFinal.lean handles sparse graph class T (girth >=7, degree>=3 vertices distance>=7), not all bipartite C4-free graphs.

Search outputs (temporary): library-c4-statements.txt summarizes final declarations of 128 C4 files; library-two-colour.txt isolates exact TwoColour occurrences. Broad tCount searches match notCount and are misleading.

## Input-buffer transformation

Parent proposed buffering every input xi by xi AND xi. This is sound: take n buffer gates, then map every original gate input and output by w ↦ n+w. Every OR input is then >=n, so every gate wire has empty orIn and T=0 under every colouring. Buffer gates evaluate to a second copy of the input, and the remaining gate evaluation is exactly the original evaluation shifted by n wires. Draft proof library-buffer.lean gives size=C.size+n, correctness, IsAO2, and T=0.

Stronger observation: buffering only one input colour class also suffices. Every direct input read by an OR then has the other colour. For bipartition p+l, this gives overhead min(p,l). Mapping when buffering points is i<p ↦ p+l+i; p≤i<p+l ↦ i; i≥p+l ↦ p+i. This variant is not yet formalized.

## Checked components (2026-11-25 UTC)

- library-colour.lean checked successfully; T=0 excludes IsTwoColour, hence two reached inputs at any OR gate have equal colour.
- library-buffer.lean checked successfully with no warnings; all-input buffers cost n gates, preserve AO2 and exact function, force T=0 for every colouring.
- library-onecolour.lean checked successfully with no warnings; buffers only p point inputs of a p+l circuit, costs exactly p gates and forces T=0 under the standard point/line colouring. Includes full-buffer base for standalone checking.

Build command uses lake env lean from lean/ with the parent-installed ELAN_HOME. Full stdout/stderr stored under task scratch with each basename plus -build.stdout/.stderr. These are proved helper results, NOT a proof of the posted lower bound.

Related linear-system helper discovered: accepted L_meta_6734.lean has BS.sum_good_le at590, BS.sum_T_le at613 (sum support sizes <=2*gatecount+#outputs), and main at714 (sum row sizes <=3*gatecount for nonzero degree>=3 and pairwise intersection<=1). Sent to algebraic_route agent.

## T0-preserving top-form normalization complete

At 2026-11-25 17:34 UTC, library-topform-final.lean compiled with exit0 and empty stdout/stderr. It combines the accepted L1501 surgery with T0-preserving redirection and a constrained minimum over AO2 circuits computing the same function with T0. The public endpoint Lift.exists_top_form_zero gives, for a nonempty graph edge function, an AO2 circuit D of no larger size computing the same function, still T0, in TopForm, and size-minimal among all AO2/T0 circuits computing that function. The last property lets semantic least_pair_active prove every gate of this SAME D accepts at least one target-edge pair.

The key invariant is that any wire below the singleton-free output function has empty OR-input reach. Redirecting to such a wire does not introduce colours. Redirecting an OR reader to one operand shrinks OR reach. The surgery's new output OR computes the singleton-free output function and therefore has empty OR-input reach. The final wrapper minimizes the count of ancestor-related AND pairs among the size-minimal T0 circuits; any top-form violation strictly decreases that count while preserving size and T0.

No full lower-bound claim is made here. Earliest dirty AND classification plus active gates and top form still leaves filtering of opposite-colour rectangles and singleton-active buffers as the unresolved quantitative obstacle.

## Contextual OR-branch essentiality

library-or-essential.lean compiled exit0 with empty stdout/stderr. It is the frozen top-form source plus a169line extension (1980 lines total). For a constrained minimum AO2/T0 circuit computing a nonempty graph edge function, redirecting any OR gate to either chosen operand loses at least one target-edge minterm. The stronger final lemma gives an edge input on which the discarded operand is true, the retained operand is false, and the modified whole circuit is false. Thus the edge-pair truth sets of the two operands of every OR gate are incomparable.

The proof deletes the OR via Lift.V1 (one fewer gate), preserves T0 by shrinking OR reach, and proves that the modified output only decreases. If no target edge pair were lost, monotonicity of the modified circuit would restore every positive input, while output decrease excludes new negative errors. This would contradict constrained minimum size. No C4-free assumption is needed for this helper.

## Checked buffer relocation and global charge

The frozen library-mask-merge.lean proves a concrete private two-buffer factoring move. For i<j<k with i=AND(a,a), j=AND(b,b), k=OR(i,j), no other readers of either buffer, and output outside the buffers, rewrite j as OR(a,b) and k as AND(j,j). The function and size are unchanged, T0 holds if the two raw supports are jointly monochromatic, and i becomes unused. Constrained minimality therefore forbids this pattern. library-mask-smaller.lean adds the corresponding existence of a strictly smaller circuit.

The stronger frozen library-mask-cut-flex.lean proves relocation across an arbitrary shared region: remove selected raw-input identity buffers B, unmask a region R whose original operand raw reaches lie in one colour class S, and insert masks at a boundary K intercepting all outgoing OR references. B and K may overlap. Exact semantics and T0 are preserved, with size(D)+|B|<=size(C)+|K|. AND exits need no extra masks. This is an actual circuit construction through SemanticFold, not a hypothesized cut inequality.

Combining that with the independently checked BufferBoundary construction gives library-buffer-charge.lean, namespace InputBufferCharge. For any input-buffer set B in a constrained minimum T0 circuit, |B|<=|orN\lam|. Colour-specific outside readers have an opposite-colour raw witness and a propagated singleton witness, so are semantically mixed and paid. T0 makes the two colour-specific paid sets disjoint. The theorem permits arbitrary shared OR DAGs; no C4-free assumption is needed beyond a proper graph colouring. All-true positivity is explicit. Build exit0, empty library-buffer-charge-build stdout/stderr. Unique wrapper67lines starts2895; its foundations are frozen separately.

## Checked singleton-profile pinning

library-pin-and.lean (frozen, exit0, empty logs) proves that a valid AND gate with a singleton witness a and target-edge profile equal to raw input a can be replaced at the SAME index by AND(a,a). This preserves exact graph function, AO2, T0, size, every other gate record, and every wire's OR reach. Cone inclusion and andPairs nonincrease are also checked. Structural agent owns the tertiary nonbuffer-count minimization and earliest-singleton application. Unique PinAnd namespace222lines starts1982. This does not normalize arbitrary nonlinear dirty ANDs.

## Final scoped saturation result and unresolved core

library-row-saturation.lean is frozen and checked with empty logs. `RowSaturation.saturated_wire` concerns an ACTUAL circuit wire, including hidden payload. If its raw OR support has at least two vertices in the star of owner y distinct from row centre z, and the test input turns on its raw-support non-neighbours of z, the wire is true both before and after any positive input toggle. C4-freeness supplies a raw backup vertex.

Important correction: canonical row-negative tests satisfy that hypothesis for point-side raw banks whose owner has the same colour as the row centre. Opposite-side line banks can remain raw-false while nonlinear hidden payload changes under a point-leaf toggle. No unconditional claim that differently owned lambda wires are saturated or unary is justified. Own-centre banks can also merge multiple payload sensitivities. These cases, plus shared selector choices across row traces, leave the global residual budget unproved.

library-id-buffer.lean is also frozen and checked with empty logs. `BufferFacts.identity_source_nonempty` proves a constrained-minimum idempotent AND buffer must have nonempty source OR reach: otherwise V1 deletes it with exact semantics/T0 and smaller size. Broader composite-buffer relocation was not attempted after the parent changed priorities.

All work in this note is partial. There is no proof or refutation of the exact L-meta-4675 statement and no accepted checker verdict for that statement. Sources explicitly reported as checked have complete saved stdout/stderr; the parent owns preservation, branch pushes, and lease release.
