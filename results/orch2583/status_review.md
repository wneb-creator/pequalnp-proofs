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
