
Root: target is exact desk-poll-003.json statement. No reductions permitted on this lease. Core definition requires NOT both operands implicant, not both non-implicant. Lift applies only in output cone, while maximal cores include dead gates. Existing partial results from L2583 may help with sharing but do not prove arbitrary normalization.

2026-11-25T15:44:23.247376+00:00 semantic_proof
SemanticCore.lean compiled exit0. Generic IsAO2 wire_all_true, no raw input below graphF, core_is_and, and core_has_nonimplicant_operand. These hold for dead and live cores without fixedpoint/minimality. A core only excludes BOTH implicant operands: one may already be implicant, so a proof assuming both inputs non-implicant would be invalid. No constant/forward-input loophole: exact2 and ReadsBack rule them out. Complete logs semantic2962-core.stdout/.stderr; only simp/deprecation suggestions.

## Structural route — 2026-11-25T15:45:09.184712+00:00

`StructuralCones.lean` compiled with exit 0; complete logs are `/tmp/oec/pequalnp-pilot-104/2962-structural-cones2.stdout` and `.stderr` (both empty). Namespace `PEqualNP.Outside.L_meta_2962.Structural`.

New checked components: maximal cores form an InCone antichain; a maximal core lies in another maximal core cone iff equal; every core lies in some maximal core cone; the union of all core cones equals the union of maximal-core cones. Thus maximal cores lose no gates relative to taking all cores. The fixed-point wrapper states that a live OR gate with an implicant operand must itself be below the graph function. These facts do not require minimality or all gates to be live. Support cone recursion/transitivity is copied from accepted L_meta_3700 (Defs-only extraction, no custom instance).

Source census: L4183/L7077/L6240 require `IsLeastAO`, absent here. R4895_628 leaves the general matching-charge inequality as a hypothesis. L3657's stronger fixed-point characterization additionally requires all gates live and no sound operands at AND gates, also absent. L3446 refutes a stricter filtered-U bound, while L2969 refutes the companion outside-core count; neither directly refutes this unfiltered-U statement. Actual `Core.IsCore` asks NOT both operands implicant, not both operands non-implicant. The lift restriction only touches live OR gates; dead core DAGs remain eligible.

The abandoned `StructuralCores.lean` draft duplicates SemanticCore work and is NOT compiled; do not treat it as a result.

2026-11-25T15:47:01.262335+00:00 semantic_proof
SemanticNested.lean compiled exit0 on first full build. New core_has_nested_and: any core of any IsAO2 circuit has another AND gate strictly in its cone. No fixedpoint/bipartite/no4cycle assumptions needed. Proof: if strict cone has only OR gates, trace each accepted-pair operand to one endpoint and a unit ReadK vector; belowF prevents both choosing same endpoint; adding distinct vectors gives READ1, contradicting core. Includes checked SemanticCore and StructuralCones plus exact L6579 vector toolkit. Complete logs semantic2962-nested.stdout/.stderr; warnings only.

### Input-port budget — 2026-11-25T15:47:13.079517+00:00

`StructuralPorts.lean` (frozen SHA256 `53345c0df7eff215701b184cddb71bcdc5b8e90c1c76ed02b21b745977ba4e68`) compiled exit 0; complete `2962-structural-ports2.stdout/.stderr` are empty. This is the frozen StructuralCones bundle plus StructuralPortsSuffix.

Define primary-input ports as operand slots `(gate, b)` with gate in U and `opnd gate b < n`. The checked `core_input_ports` theorem bounds their count by `U.card + maximalCores.card`. Every nonmaximal gate of U has a reader in U; mapping internal operand slots to their source gate covers U minus maximal cores. Since AO2 supplies exactly two operand slots per gate, the count follows. Multiplicity matters: repeated source variables in different slots count separately.

This separates a syntactic budget from the unresolved semantic charge. Either `|D| + tau(G) - tau(G-D) ≤ ports(U)` or the stronger `|D| + tau(D) ≤ ports(U)` would suffice for the posted result after the cover-extension bridge. Neither semantic charge is proved here. Counterexample agent is finite-testing both; the best known C6 case has D=4, tau(D)=2, ports=6 (equality), while the posted bound has one unit of slack.

### Correction to the proposed semantic port charge — 2026-11-25T15:47:55.929234+00:00

Root found a general obstruction: clone every input by `x AND x`, then compute the graph's star circuits using only these clones. All primary-input ports are confined to the clone gates, so there are only `2n` such ports. The star outputs now reread their accepted edges and are cores. A projective-plane incidence graph of order at least three has `|E| + tau(G) > 2n`, contradicting the proposed semantic lower bound. This does not contradict `core_input_ports` (an upper bound) or the posted cone-size inequality, since U still counts every clone and internal gate. The semantic port-charge strategy therefore requires substantial extra normalization and should not be pursued as a general lemma.

Root warning: a semantic lower bound on primary-input ports alone is false without normalization. Clone each input using AND(x,x); all later star gates read these clones. Every edge then rereads both endpoints, while primary-input slots stay 2n. For an incidence plane with q>=3, m+tau>2n. The original gate-union budget still counts clone and internal gates, so this does not refute L2962.
