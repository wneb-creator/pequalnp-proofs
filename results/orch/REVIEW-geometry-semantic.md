# Independent review: geometry and semantic NOT elimination

Reviewed UTC: 2026-11-25T14:20:40.689486+00:00
Reviewer: lean_setup
Verdict: PASS for preservation of these checked partials; not a proof of the posted lower bound.

- Source: /tmp/oec/pequalnp-pilot-103/GeometryCheck.lean
  SHA256: 099f8f1893321c897ba640fd0ae5fbfd30308ebe3a3bf2fbd4c33b0320a4e8b6
  Lines: 187
- Source: /tmp/oec/pequalnp-pilot-103/NotElimination.lean
  SHA256: a31c344df9ad84b51921fb6087d313a745476a03f933ccd52e52f32c4102fe05
  Lines: 27

GeometryCheck review:

- All signal, row, observation, truth-table, and restriction definitions are ordinary functions over Mathlib BitVec/Fin/List. There are no axioms, dummy assumptions, invented instances, or replaced circuit semantics.
- Independently decoded every input/pin truth table and the target: pins are the stated coordinate functions, the 1024-bit target is the Petersen edge function, and graph is its nine-variable restriction.
- Independently verified all ten relabelings are graph automorphisms, bijections, and send the removed vertex to zero. Exhaustive enumeration verified every 512-row target projection, each pin projection, and every stored row witness.
- decide +kernel asks the Lean kernel to check finite propositions; it is not native_decide. These lemmas establish geometry, not the nine-variable lower bound or the target theorem.

NotElimination review:

- Both lemmas are valid Boolean identities under their explicit pointwise monotonicity and implication hypotheses. Independent truth-table checks passed for all Boolean values of h, G false, and G true.
- They do not construct a replacement circuit or prove a gate-count saving. Applying them to a circuit requires those additional structural arguments.

Format/evidence:

- Mathlib is the only import; declarations stay inside permitted module child namespaces. Only scoped maxRecDepth/maxHeartbeats limits occur. No forbidden commands, placeholders, extra axioms, root qualifier, strings, attributes, custom data types, or instances occur.
- Large hexadecimal tables are concrete data, and their semantics were checked independently above.
- All four supplied compilation logs are empty; authors report exit 0. This reviewer did not rerun Lean or the posted-statement checker.
- No apparent credential material occurs in either source. A combined file must be rebuilt, and final submission still requires the exact posted theorem and checker acceptance.
