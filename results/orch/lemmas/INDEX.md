# Existing checked lemmas and strategy outputs

Current checked source: lean/PEqualNP/Outside/L_meta_1342.lean.
Namespace PEqualNP.Outside.L_meta_1342: baselineCircuit, baseline_monotone,
baseline_size(22), baseline_spec(exacttargetallinputs).
Auxiliary namespace PEqualNP.Outside.L_meta_1342_aux:
- circuit_partial_edge_bound: clean actual binary circuits in C4-free ambient K,
  accepted target edges outside empty singleton support yield an edge/cover bound.
- target_c4, target_edge_count(16), target_min_cover(7), clean_target_size(22).
- circuit_support_partial_edge_bound: exact supportS and accepted residualedgesG
  admit a target coverT with |S|+|E(G)|+|T|<=gates+1, for clean binary circuits.
- no_common_neighbor_descendant: through productive clean AND/OR ancestry,
  support having no common neighbor persists and all proper descendants areOR.
- wiresFrom_mono and pos_mono already give monotonicity for AND/OR evaluation,
  including constants/unary/default-false reads.

Finite graph facts: 16edges;24maximal independent sets(22size4,2size3);
125independent inputs total;1923positive inputs;identity-only automorphism.
Maximal independent bit masks:
15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,
1066,1186,1288,1408,1546.

The40row boundary sufficiency criterion is now compiled and integrated in the
2069line named file, SHA 0e0620c89307cf34be010940037cb187797eea76c85fc8c8a89b9bd1cfc56e5c.
New helpers: boundary_cover_bool, target_negative_cover_check,
target_negative_cover, target_negative_independent, circuit_eval_mono,
and target_boundary_spec. The last theorem needs only Monotone2 and the40
boundary evaluations; no clean-AND premise. Named build exit0; S03proofreview
and S08integrationreview pass; axiom audit uses only standard permitted axioms.
The posted size21 existential remains unproved; local posted checker NOT RUN.
Earlier failed approaches are historical diagnostics, not current build status.

Each strategy writes its own Sxx report here and appends findings to NOTES.md.

Additional compiled helpers: targetBoundaryCheck_iff, target_edge_iff_posted,
target_spec_of_boundary_check, target_witness_of_boundary_check; suppliedgatebound
k is preserved. baseline_boundary_check/positive_control certify only22gates.
