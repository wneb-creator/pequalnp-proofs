
Root: target is exact desk-poll-003.json statement. No reductions permitted on this lease. Core definition requires NOT both operands implicant, not both non-implicant. Lift applies only in output cone, while maximal cores include dead gates. Existing partial results from L2583 may help with sharing but do not prove arbitrary normalization.

2026-11-25T15:44:23.247376+00:00 semantic_proof
SemanticCore.lean compiled exit0. Generic IsAO2 wire_all_true, no raw input below graphF, core_is_and, and core_has_nonimplicant_operand. These hold for dead and live cores without fixedpoint/minimality. A core only excludes BOTH implicant operands: one may already be implicant, so a proof assuming both inputs non-implicant would be invalid. No constant/forward-input loophole: exact2 and ReadsBack rule them out. Complete logs semantic2962-core.stdout/.stderr; only simp/deprecation suggestions.

## Structural route — 2026-11-25T15:45:09.184712+00:00

`StructuralCones.lean` compiled with exit 0; complete logs are `/tmp/oec/pequalnp-pilot-104/2962-structural-cones2.stdout` and `.stderr` (both empty). Namespace `PEqualNP.Outside.L_meta_2962.Structural`.

New checked components: maximal cores form an InCone antichain; a maximal core lies in another maximal core cone iff equal; every core lies in some maximal core cone; the union of all core cones equals the union of maximal-core cones. Thus maximal cores lose no gates relative to taking all cores. The fixed-point wrapper states that a live OR gate with an implicant operand must itself be below the graph function. These facts do not require minimality or all gates to be live. Support cone recursion/transitivity is copied from accepted L_meta_3700 (Defs-only extraction, no custom instance).

Source census: L4183/L7077/L6240 require `IsLeastAO`, absent here. R4895_628 leaves the general matching-charge inequality as a hypothesis. L3657's stronger fixed-point characterization additionally requires all gates live and no sound operands at AND gates, also absent. L3446 refutes a stricter filtered-U bound, while L2969 refutes the companion outside-core count; neither directly refutes this unfiltered-U statement. Actual `Core.IsCore` asks NOT both operands implicant, not both operands non-implicant. The lift restriction only touches live OR gates; dead core DAGs remain eligible.

The abandoned `StructuralCores.lean` draft duplicates SemanticCore work and is NOT compiled; do not treat it as a result.
