
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

2026-11-25T15:48:15.524985+00:00 semantic_proof
SemanticActiveNested.lean compiled exit0. Strengthens nested witness: for each accepted pair at a belowF AND where ReadTwiceAt holds, there is an AND strictly in its cone that is true on the same pair. The pure-OR tracing closure is only needed on pair-active wires, allowing inactive nested AND gates. Exposes active_nested_and and core_has_active_nested_and. No fixedpoint/bipartite/C4 assumptions. Frozen independent artifact, full logs semantic2962-active.stdout/.stderr.

## Counterexample search, 2026-11-25 15:49 UTC

The exact evaluator uses full Boolean truth tables, exact singleton/pair READ1 flags, dependency cones, and exact minimum vertex-cover recursion. It restricts every gate to valid backward binary AND/OR. All searched gates can be made dead by appending an independent live star-cover circuit; this preserves maximal-core data and ensures the live lift-fixed-point condition. The evaluator passed independent logic review and reproduced accepted examples L2969 and L3762.

C6: more than3million mutations, no violation; minimum posted margin1. K4 incidence:2,435,282 mutations, no violation; minimum posted margin1 and stronger D-cover margin0. Fano search is running for90 seconds. These are heuristic searches, not exhaustive certificates.

A posted equality example exists on the path x-y-z-w: dead gates a=x AND y; b=a OR z; c=y OR w; d=b AND c. The last gate is a core because the accepted edge xy must reread y. With an independent live path circuit appended, D is all3 edges, minimum cover2, union-cone size4, one maximal core, and residual cover0. Thus5=5. This is not a refutation.

Primary-input port inequalities are diagnostic only: the input-cloning construction supplied by root/few_nots disproves that stronger route at sufficient graph density.

2026-11-25T15:53:26.027352+00:00 semantic_proof: global weighted charge investigation
Sufficient target for matching M is |D|+|M intersect D|<=|U|+mc. The exact topology budget is primary-input operand occurrences P plus internal fanout surplus R. Here R is the sum over non-sink gates of operand-occurrence outdegree minus1; the maximal cores are the sinks. Fan-in2 gives U+mc=P+R. Repeated operands must count twice. This corrects the false primary-port-only bound and survives input-AND cloning. StructuralBudget independently checks the equivalent internal-edge formula.
Precise obstruction: graph-edge support is not a bounded potential on an intermediate junk gate. For a Fano incidence graph, H=(OR of7 point inputs) AND (OR of7 line inputs) uses13 gates but accepts all21 graph edges and all7 edges of a perfect matching, giving weighted28. It also accepts nonedges, so H is not BelowF. Only downstream context removes those nonedges. Any inductive charge that ignores nonedge acceptance or context therefore fails even on a simple rectangle.
The checked active nested-AND witness is not an injection: one shared junk AND can be true on many edges and lie in many maximal-core cones. C4 exclusion can constrain a family of immediate pure-OR filters of one rectangle to a double-star, but a general core may have intervening ORs and multiple junk ANDs. Fixedpoint cannot normalize dead cones, because its definition only sees the original output cone. This is the precise gap in extending the one-junk/double-star argument globally.
A plausible structural route is to charge weighted edge surplus beyond distinct incident variables to repeated primary occurrences and internal reconvergence. Equivalently, with all used primary variables V, undirected circuit cycle rank r and component count c, U+mc=|V|+r+mc-c. P4 equality has4 used variables and one reconvergence cycle, paying exactly3 edges+2 matching tokens. Turning this identity into a semantic lower bound needs a cycle-elimination or nonedge-context lemma; no complete argument has been found.

### Shared P4 family bound — 2026-11-25T15:55:19.020028+00:00

`StructuralP4.lean` compiled exit 0, complete logs `2962-structural-p4.stdout/.stderr` (only an unused-section-variable warning). Namespace `PEqualNP.Outside.L_meta_2962.SharedP4`.

For each index t let a=xy, b=a OR z, c=y OR w, d=b AND c. Define distinct gate keys A={unordered(x,y)}, B={(A,z)}, C={unordered(y,w)}, and O={(B,C)}. The outputs represent the three-edge path xy OR yz OR zw by Boolean absorption. The theorem `shared_family_cover` constructs a cover S of the union D of all path edges and proves `D.card + S.card ≤ A.card + B.card + C.card + 2*O.card`. Thus arbitrary sharing among these P4 blocks satisfies the desired numerical bound when U consists of those deduplicated gates and O is its core set. The abstract theorem is about these finite gate keys and edge families; no general circuit-normalization theorem is claimed.

The proof needs only a coloring with color(x)=color(z) and color(y) different. A shared B determines y uniquely: swapping the two endpoints of A would violate the colors. A shared output O then also determines w. Thus xy edges charge to A, yz edges to B, and zw edges to O. The endpoints of all C keys cover D using at most twice as many vertices as C keys; every C is used by an O, so C.card≤O.card. This is the required accounting. C4-freeness is unnecessary for this block class.

The preceding computational check exhaustively glued two oriented P4 blocks (47 valid canonical bipartite/C4-free unions), and randomly sampled larger families; no negative posted margin occurred. Complete script and numerical results are SharedP4Search.py and SharedP4Search.json. The checked theorem now covers all such shared families, beyond those finite samples.

## Final counterexample-search preservation, 2026-11-25 15:58 UTC

All search processes are stopped. Five completed phases examined exactly10,058,361 circuit mutations: C6 4,240,047; K4 incidence2,435,282; Fano601,577; stronger-objective Fano598,774; carryover K4 incidence2,182,681. One OR-sharing phase was interrupted for disk pressure after at least152,018 mutations; its final in-memory count is unknown. No posted counterexample and no exhaustive UNSAT result. Minimum random posted margin1, stronger D-cover margin0. The explicit P4 equality case was kernel-checked separately in CountingTight.lean.

Final code and all38 complete log/data files are in search/counterexample/, with exact counts and SHA256 hashes in VALIDATION.txt. Source SHA256:45b7397a730d1e3e7bed04c2a153cba1b109ed2604297862bdeebd503238bf35. All26 JSON files parsed successfully after the disk interruption.

### Sharper P4 AND/OR split — 2026-11-25T15:58:45.840715+00:00

`StructuralP4Sharp.lean` compiled exit 0, complete `2962-structural-p4-sharp.stdout/.stderr` contain only unused-section-variable warnings. It appends StructuralP4SharpSuffix to frozen StructuralP4.

New `and_cover` gives a cover of D of cardinality at most A.card+O.card: choose one endpoint from every A edge and the middle vertex z for each O. New `or_edge_bound` gives D.card≤B.card+C.card+O.card under the earlier color orientation plus the condition that a shared C key determines z. `common_center_of_no_four` derives that condition from NoFourCycle and distinct endpoints y,w adjacent to z. Thus, for arbitrary shared P4 families, OR gates plus maximal outputs pay for the edges, while AND gates pay for the cover. The residual zw edges not already among yz edges inject into C keys: if a shared C reverses its endpoints, that zw edge is already a yz edge. `path_identity` also checks the Boolean absorption identity for each block.

This is a proved finite-family accounting theorem with explicit gate keys; connecting arbitrary circuits to this block class remains outside its scope. No new searches were started after the disk-pressure pause.
