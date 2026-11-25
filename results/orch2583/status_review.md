# Independent audit: L-meta-2583

## Statement and model

The assigned theorem asks for a no-larger READ-1 replacement for every exact-fan-in-two, backward-reading AND/OR circuit computing a projective-plane incidence function. READ-1 is the joint proof-tree notion: each prime implicant admits one proof tree in which both variables are read at most once. It is not input fanout one or the weaker per-variable scalar notion. IsAO2 requires exactly two operands, allows repeated operands, forbids constants and NOT gates, and requires earlier-wire reads.

The plane assumptions have no apparent vacuity or missing regularity loophole. Uniform line size q+1, unique line through each distinct point pair, and N=q²+q+1 imply every point lies on q+1 lines, by counting its other incident points. Thus the incidence graph is regular bipartite and has a perfect matching. q=2 gives the ordinary Fano instance.

## Status and format

The desk response assigns L-meta-2583 with no listed PRs. The local complete git history has no named L_meta_2583 file. GitHub all-state PR search for 2583 returned an empty JSON list; stdout and stderr are preserved in scratch. No proof/refutation of this exact gap was found. The current desk does not open reductions, despite its older sketch inviting decomposition. Only the assigned L_meta_2583 file can become a proof PR; copied helpers must stay in its own namespace, with only Defs and Mathlib imports.

The checked tool supports refute mode: the final theorem must prove the exact posted statement's negation. A short ordinary circuit alone would not suffice; a refutation must also exclude all no-larger READ-1 replacements.

## Reusable results and missing argument

- L_meta_2393 has an internal generic star construction, upper, using only N>0 and each line having q+1 points. It gives an AO2 READ-1 circuit of size N*(q+2)-1. This is the strongest direct construction found.
- L_meta_7639 proves the exact READ-1 lower bound |E|+N-1 for a C4-free bipartite graph with a perfect matching. Together with plane regularity, the assigned task is equivalent to the unrestricted monotone lower bound N*(q+2)-1.
- R_meta_4895_628 is a reduction for the broader C4-free normalization statement. It assumes the missing unrestricted matching-charge bound, and combines it with a checked star builder and a READ-1 argument. It does not settle the hard lower bound.
- L_meta_7653 proves the matching-charge bound only for a circuit whose gates are an OR prefix followed by an AND suffix. General arbitrary blocks remain outside that theorem.
- L_meta_2581, L_meta_1942 and related incidence bounds assume READ-3/READ-2 or include a double-reread error term, so they do not close the exact task.

A q=2 refutation would need an AO2 circuit of at most 26 gates against the READ-1 floor of 27. No such witness has been found in this review.

## StarUpper preservation review

Static audit PASS for results/orch2583/lemmas/StarUpper.lean at SHA256 70c33f4a7120af93dc238e85d357c2e9b27e2b79e737406b8f0096ec97690ce5, 636 lines, 27540 bytes. Its body is exactly the existing L2393 Own namespace from ofFn_getD through upper, with a new assigned namespace wrapper. The upper theorem has only N>0 and uniform line-cardinality assumptions. Each star uses q OR gates and one AND gate, and N stars use N-1 combining OR gates. The vector argument witnesses a selected incident pair with both entries at most one. No forbidden constructs, options, attributes, instance declarations, or new data types are present. Compilation is pending at the time of this static review; this is only a construction partial, not the posted replacement theorem.

The owning agent reports StarUpper compiled with exit 0; both starupper2 build logs were independently verified empty. Frozen source bytes are unchanged. Preservation audit PASS.


## StarReduction preservation review

PASS as a compiled conditional component. StarReduction.lean has 678 lines, 29834 bytes, SHA256 903226af0a38465a2cc1274016dbc1bef05b02a6a543a5b11ba5b60bdf26145a. It is exactly the reviewed StarUpper followed by StarReductionSuffix, ignoring blank lines. The 41-line suffix has SHA256 2f047c5dbdc103ee8ef2e06e0baa4fa63a08e8dc4289166d022697a1ac02de38.

replacement_of_lower_bound constructs the same incidence function and READ-1 witness using the explicit numerical premise N*(q+2) ≤ C.size+1. The cost identity of upper then gives D.size ≤ C.size. posted_of_lower_bound uses exactly the posted plane/model/computation hypotheses to invoke a universally assumed numerical lower bound; its conclusion matches the assigned statement. Positivity of N follows from N=q²+q+1. No lower bound is claimed without that explicit premise, and this is not a submitted reduction under the desk rules.

Both starreduction logs are empty, and the owner reports compilation exit 0. Namespace and source scans find no forbidden text, options, attributes, custom data types, or instance declarations. Preservation audit PASS; the full target remains open.


## PlaneGeometry and StarLower preservation review

PlaneGeometry.lean: PASS as a compiled partial, 155 lines, 7064 bytes, SHA256 ba2df371d6d92b69d37c3fc019e7e594b424e19c33cd6d3d5111397ef85d10b0. Double counting pairs (other point, incident line) gives (N-1)=q times the number of lines through a fixed point; q≥1 permits cancellation and proves degree q+1. Incidence summation gives edge count N(q+1). Unique incidence excludes rectangles. Counting incidences covered by point/line subsets yields cover cardinality at least N. A second incidence inclusion proves Hall's cardinality inequality. All hypotheses are explicit, with no graph-model assumptions hidden in counting. Both geometry logs are empty.

StarLower.lean: logical preservation audit PASS, 2151 lines, 107156 bytes, SHA256 5ed5c107872b871fa9ed544cdc73c7ce7a7b6e07a3e0a19b866a4ebbbe02b24c. Its base is exactly L_meta_4897 with assigned namespace/theorem renaming and removal of the unused Mathlib umbrella import, followed by the reviewed PlaneGeometry. Its full file is exactly that base plus StarLowerSuffix. The final 35-line specialization keeps READ-1 explicit, applies the C4-free cover bound, combines cover size≥N and edge count=N(q+1), and obtains N(q+2)≤C.size+1. It does not prove the unrestricted lower bound. The owner reports compilation exit 0; stderr is empty, stdout contains only inherited linter/deprecation warnings and is preserved in full.

No forbidden text, options, attributes, instance declarations, or custom data types were found in either file. One final-integration format caveat: the copied cover_bound helper currently stands fully qualified at top level, outside an explicit namespace block. It should be moved inside its assigned namespace before a proof PR. This does not undermine the compiled partial result or block preservation.


StarEquivalence.lean preservation audit PASS: 2850 lines, 137960 bytes, SHA256 2764b5cc74a33b57a5e6bda8e0d071259566d4d23c9d64a46d3798f071f4178f. It combines exactly the reviewed StarReduction, StarLower, and 20-line StarEquivalenceSuffix in that order, ignoring blank lines and duplicate import lines. Suffix SHA256 c21cfb348e97d5db4cb165da012488f1bdabf3570907957ea98eea8733cc5500. The forward implication applies the checked READ-1 lower bound to the replacement D, then uses D.size≤C.size. The converse is the reviewed star construction. Hence under the plane assumptions, existence of a no-larger READ-1 replacement is equivalent to N(q+2)≤C.size+1. C itself need not compute the function for this equivalence, since it appears only through its size; this is intentional and sound. The unrestricted numerical bound for computing C is still unproved. Owner reports build exit 0; stdout contains only inherited warnings and stderr is empty. The inherited top-level helper namespace caveat remains, with a separate cleaned version under preparation.


StarEquivalencePlain.lean delta audit PASS: 2853 lines, 137968 bytes, SHA256 2f43a4b3c1f8491a3c3eae664087a8e67ff83819eb1c04d74d5c80155e1c777f. The only change from the reviewed combined equivalence is wrapping cover_bound in the explicit ReadLower namespace and shortening its declaration name; its qualified name, statement, and proof are unchanged. All helpers now stand inside assigned namespace blocks; no open namespace or section remains, and no top-level helper declaration remains. No forbidden constructs were found. Build stdout contains inherited warnings without errors; stderr is empty. This is the preferred preserved component for later final integration, still without the unrestricted lower bound or final target theorem.


SemanticTripleBlock.lean preservation audit PASS: 75 lines, 3629 bytes, SHA256 2c5218282ca1b11e5c9cd65d1c344ead9ac7ff5662b2cfec60bdcccc93d440e8. For E=((P∩Wp)×L)∪(P×(L∩Wl)), the explicit no-rectangle premise is exactly the C4 exclusion for this pair relation. If either side has at most one element, that side covers E cheaply. Otherwise each selected intersection has at most one element, since two selected rows or columns would form a rectangle; those intersections cover E and the union-cardinality bound proves |E|+|U|+|V|≤|P|+|L|+|Wp|+|Wl|. No circuit-size or circuit-computation assertion is made. Sole Defs import, own namespace, no forbidden constructs; both build logs are empty, compilation exit 0 reported by owner.


## Rectangle and sparse single-reader components

RectangleCover.lean preservation audit PASS: 80 lines, 3794 bytes, SHA256 85a6f2c9c12e09c33d6426af3500eff94ddcd031f303b63373f17285d9df8593. A nonempty rectangle inside a C4-free incidence relation has a singleton side, providing a cover with edge-count plus cover-count at most the two side counts. Taking unions of the two covers and applying three union-cardinality inequalities gives the two-rectangle bound. The one-junk shape is a direct specialization, using intersection/union cardinality bounds. This is geometric accounting, with no claim that arbitrary circuit blocks admit the stated representation or gate budget. Both build logs are empty.

SingleOrSparse.lean preservation audit PASS: 98 lines, 4503 bytes, SHA256 f8e59cfc3e07433f4a5a49a37ac651c2988361d934784d87794510d457d5dc6d. The semantic cut and two monotonicity properties are explicit hypotheses. Acceptance of each incident pair propagates through the exposed true reader output; if the sibling accepts a false input without p, adjoining a line through p forces some other point to meet that line. Unique pair incidence and p's absence inject those lines into the other-point set, giving q+1 points. This does not assert that all circuit cuts already satisfy the semantic interface. Both build logs are empty.

For these two partials, official plain/import/namespace parser checks pass after adding only an in-memory parser sentinel theorem (not written or compiled); actual full-target theorem remains absent. A minor prose-format caveat was sent to SingleOrSparse's owner: indent its multi-line doc-comment continuation or convert it to line comments before final integration. This does not affect the logical audit or compiled preservation result.


SingleOrCertificates.lean preservation audit PASS: 153 lines, 7353 bytes, SHA256 9ce7830cac626b6c0fd3dcc34ffeac026282f89379c71b5b6dfbee3f891bb765. It is exactly the reviewed SingleOrSparse plus the 55-line suffix, SHA256 d704422ad660f90c35af0520687a8051f8cc44f3816aa70749d35c36e3486d6f. A false input stays false on a subset of its points, so an accepting certificate with at most q points contradicts the proved q+1 lower bound. A support of size at most q supplies such a certificate by intersection. All semantic cut and monotonicity hypotheses remain explicit; no unrestricted normalization claim is introduced. Both build logs are empty and source scan finds no forbidden constructs. It inherits the already noted minor comment-format caveat from its frozen base.


SemanticClauses.lean preservation audit PASS: 154 lines, 6889 bytes, SHA256 b55f36ab59b2c0fd5b97943959bb2fd8005fcad22e709973467508df7de3b9d6. Exact reviewed SemanticTripleBlock followed by the 78-line SemanticClauseSuffix, SHA256 1e5e24e54bb8e01f794b878a7845e510a1cb158024aeedf30d48920f14ab1d0d. If a conjunction of three nonempty mixed clauses implies an incidence edge, an all-points/no-lines test forces a pure-line clause, and the dual test forces a pure-point clause; nonemptiness makes them distinct. The explicit singleton pair test proves the stated edge-union identity. The below-incidence premise then transfers ambient C4-freeness to the pair core and applies the reviewed finite-set cover budget. No AO2-to-clause representation or gate-size estimate is asserted. Build stderr is empty and stdout contains only two simp suggestions; the owner reports exit 0. No forbidden constructs or format issues found.


SingleOrSparse comment-format cleanup audited: only two spaces were added before the continuation line; undoing those spaces reproduces the previously reviewed hash exactly. New Sparse SHA256 7904baedb11ec677463900bdcf4382d7ea6bb6c0b31a24f50e5983377b7b4f03, 4505 bytes. SingleOrCertificates remains at SHA256 9ce7830cac626b6c0fd3dcc34ffeac026282f89379c71b5b6dfbee3f891bb765 with the correctly indented continuation, and its latest recheck logs are empty. The comment-format caveat is resolved.


CommonFilterGeometry.lean preservation audit PASS: 89 lines, 4107 bytes, SHA256 869e6545c8c351987440efe7c42800555eda9cfed5e5107fd82c0b43e3710d53. The exact filtered-rectangle inclusion/exclusion count is correct. C4-freeness forces each selected side intersection to have size at most one when both original sides exceed one; all four resulting cardinality cases prove |Rect|+1≤|P|+|L|. Explicit nonempty-side premises handle the singleton cases and are necessary for this numerical form. For two rectangles, the fixed filter sets A,B cover the union; union cardinality plus the two individual bounds gives the stated +2 budget. The same cover-cardinality terms occur on both sides and no unproved optimal-cover claim is inserted. Build stderr is empty; stdout contains inherited or harmless tactic-linter warnings, with no errors. Source contains no forbidden constructs or format issues. This remains abstract geometric accounting, with no circuit-normalization claim.
