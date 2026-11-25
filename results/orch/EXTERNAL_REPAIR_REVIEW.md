# Independent review: ExternalRepair

Verdict: PASS for partial-artifact checkpoint, with the explicit semantic assumptions retained.

Reviewed all source and supplied build2 log. The gatewise comparison lemma handles arbitrary forward references correctly: each gate is evaluated against its prefix, out-of-range reads remain false, and full gateVal is equal to that prefix-computed value. It requires monotonicity only for the comparison circuit whose unchanged gates propagate the implication. No hidden NOT context is permitted because Monotone2 is explicit.

The repair assumes C and D are monotone, have equal gate counts and output index, differ only at g,h,t, and g,h precede t. C has AND(g,h) at t while D has OR(g,h). New g and h must each imply the graph function on every input. Joint coverage must hold whenever either original g or original h is true on a graph-edge test, not merely when their original AND is true. Finally new t must imply the complete new output on every input; this is a semantic reachability assumption, not a proved existence of an OR-only path.

On graph-false inputs, the new three changed gates are false by cleanliness, giving downward output comparison. On graph-edge inputs with an active old branch, coverage and output reachability make the new output true. If both old branches are false, all changed old gates are false, so reverse comparison preserves the old true output. The graph sandwich then proves exact equality. External readers are allowed and accounted for by the wirewise comparison.

The lemma does not construct D, establish cleanliness/coverage/reachability for a minimum circuit, or prove global star-profile existence. Equal size follows from the supplied length equality. Namespace and raw-format scans are clean; two permitted maxHeartbeats800000 options immediately precede lemmas. No axioms or unsafe evaluators are declared. Retain the usual merged-key axiom audit before publication. Source unchanged.

SHA256: fbfb285f4c4d31bed788d9c428b33738c96a0d985f5ef0edf1eb6dd0429fa7c7
Review UTC: 2026-11-25T08:01:42.897079+00:00
