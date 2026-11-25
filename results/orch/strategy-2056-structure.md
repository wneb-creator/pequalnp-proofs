# L-meta-2056 structural construction route

The requested positive and two-sided closure tests are complete for the exact order-three projective-plane incidence function. Enumeration of all 715 four-point sets found off-cardinalities 0 (13 cases), 2 (468), and 3 (234). Thus every independent point-line pair has at least one side of cardinality at most three, and monotonicity plus the requested closure tests rejects every false input.

A k-point patch of at most 5k-2 gates extends to a 63-gate full circuit by appending one four-neighbor point star at a time. Each append uses three ORs for the four line variables, one AND with the point, and one OR with the prior output. The generic Lean draft is lemmas/StarExtension2056.lean, compiled and independently reviewed. It proves exact gate count and evaluation, assuming the old output wire is valid. RelabelStarExtension2056.lean adds arbitrary input maps and the full 63-gate budget, also compiled and independently reviewed.

Patch geometry and all positive/closure rows were enumerated in /tmp/oec/pequalnp-pilot-121/patch-2056-geometry.json. The quadrangle [0,1,2,5] has four private line variables and subdivided-K4 core. Checked L_meta_723 proves that core needs at least 15 gates. Each essential zero restriction saves at least one gate, so this full patch needs at least 19 gates, ruling out the hoped-for 18. The three-collinear-plus-one patch [0,1,2,3] has seven private line variables and an eight-input theta(3,3,3) core. Reviewer identified checked L_meta_723 theta_lower1969 with t=4, proving the core needs at least 12; again the full patch needs at least 19. These consequences currently use the standard essential-input restriction theorem mathematically; no new local Lean wrapper was built.

Both search agents have been warned to skip these impossible four-point patches. Six-point leafless patch [0,1,2,3,6,7] remains a candidate: 24 incidence edges, 17 inputs, target 28 gates. Its line variables consist of two triple lines and nine pair lines, and the graph is a subdivided K3,3 with a hub joined to each triple.

The six-point patch is exactly the matrix hypothesis already present in R_meta_3785_17. Its point variables a_i,b_j (i,j=1,2,3), common hub lines u,v, and nine pair lines z_ij give the function sum_i a_i(u or row_i) or sum_j b_j(v or col_j). Baseline size is 29. Factoring either common hub out of its three point stars costs one extra gate, so simple factoring cannot reach 28. No checked lower bound for this 17-input function was found in the repository theorem census.

A potentially relevant multilevel identity is g_ij=(u or x_i) and (u or x_j)=u or (x_i and x_j). Computing all six pair outputs on four x variables jointly costs ten gates versus twelve separately. However, if u is a primary input and every pair x_i,x_j is a nonedge of the target graph, each g_ij has the same positive-edge profile as u and dominates u globally. Replacing g_ij by u preserves every minimal-true row and decreases every wire value, so correctness is preserved; this mechanism cannot create a saving in a size-minimal circuit without pairs that are themselves graph edges. This is a mathematical observation, not a newly checked circuit surgery theorem.

For the six-point graph, all 72 permutations from (S3 times S3) semidirect C2 were generated and checked against the full edge set. They partition the 136 unordered input pairs into ten orbits; data are in patch2056/six-symmetry.json. In the local input numbering, the point triples are [0,1,3] and [2,4,5], and the hubs are 6 and 11. OR-pair representatives are (0,1),(0,2),(0,6),(0,7),(0,8),(0,11),(6,7),(6,11),(7,8),(7,9); direct edge ANDs have representatives (0,6),(0,7).

Structured slack seeds in patch2056/six-cover-seeds.json add one or two line centers to the six point centers and partition each selected line's incident edges to its line star. Single-center representatives [6],[7] give 30 gates; two-center representatives [6,11],[6,7],[7,8],[7,9] give 31 gates. Every seed passes all 76 complete critical rows, and its exactness also follows from the explicit edge partition. These seeds introduce point-point OR wires that the 29-gate point-star baseline lacks and may support nontrivial window rewrites. Toolchain agent received the data.

Additional verified repository exclusions: status_review found L_meta_5187 core5_lb (line2008), an unconditional 18-gate lower bound for the eleven-vertex fourteen-edge core of the five-point two-triple patch [0,1,2,3,4]. Its six private line inputs therefore force at least24 gates. I found L_meta_9730 red13/final theorem, an unconditional 23-gate bound for Heawood minus a line. Toolchain and reviewer independently matched this to the non-leaf core of the six-point patch [0,1,2,3,4,5]; six private lines then force at least29 gates. Exact isomorphism data are in patch2056/six-orbit-a-L9730-isomorphism.json. These consequences use the essential-input restriction lemma and were not newly formalized here.

Six-point census classes (not asserted as a formal orbit classification) are saved in patch2056/six-census.json. Their counts total1716. Besides the excluded Heawood case, the non-leaf core sizes are (14vertices,19edges,target23), (15vertices,21edges,target25), and the current leafless (17vertices,24edges,target28).

A proposed branch-demand relaxation for the leafless six-point graph was exhaustively checked by gate_elimination: all1979 vertex covers S with size6..12 satisfy |S| plus an auxiliary minimum clique multicover cost at least13. This could match the strict-DAG surplus budget12 at28 gates. HOWEVER the circuit bridge is unproved: later AND filters can separate variables that shared a branch, so pointwise branch sharing need not imply the chosen terminal sets have intersection at least2. L5187 proves a related fact only under a tight one-extra-branch budget. A general uncrossing/accounting theorem is still needed. Do not report this finite relaxation as a circuit lower bound.

## 16:35 UTC: nonlinear double-star seeds and geometric cover bound

The adjacent double-star identity is

    b*A OR b*c OR c*D = (b OR D) AND (c OR A) AND (b OR c).

It costs one more gate than the ordinary two-star factorization, keeping the same subcircuits for A and D. Starting with all point centers and one extra line center costs one extra gate over the point-star baseline; applying this identity therefore gives genuine nonlinear seeds at baseline + 2. The paired nonadjacent-star CNF construction had baseline + 4. These are seeds above the requested budgets, not witnesses to L-meta-2056.

Generated frozen files under patch2056:

- six-double-star-seeds.json: 24 seeds, 31 gates; SHA256 f040f5cf4d7e05b98dbeca16a73e9086b5ea402eabda8af76c1f0430cd542240.
- collinear6-double-star-seeds.json: 19 seeds, 31 gates; SHA256 822ebd6a3b16fe6522d902d929d16614b92084474a2491c4c26836fa4d18fad8.
- eight-double-star-seeds.json: 32 seeds, 41 gates; SHA256 1cdba486ad3d0f9a60d913a9c0abac247785cdf6f4608dee34e6595f871ef7ce.
- full-double-star-seeds.json: 52 seeds, 66 gates; SHA256 a324f90d0c4e88480f279ebe8b00c2f0a21ac11f70cb4350393c741ff615d459.

Independent review checked every assignment for the three smaller collections and all 756 complete boundary rows for every full-plane seed. Each has no clean-wire normalization violation or earlier-wire directed dominance. The accepted-edge read-one deficits are 5–7 edges for patches and exactly 7 for the full plane. Generators and full audit reports are in scratch/proof-route and scratch/full-double-star-audit.json.

The 8192-subset cover census is in patch2056/full-plane-cover-census.json. Inclusion-minimal covers have size counts {13:2,16:26,18:156,19:468,20:52}. A cover whose point and line parts are both proper has size at least16, with equality types (4,12) and (12,4). The qualification matters: a redundant mixed cover containing all13 points and one line has size14 and gives a65-gate star realization.

A short analytic proof is now kernel checked in lemmas/FullPlaneCover2056.lean, 135 lines, SHA256 1363bf8bd5ecc4593edf34daaf433f9d59033ebbff6da518562ec056a351d414. For nonincident nonempty point/line sets of sizes k,l, row/intersection counts and finite-sum Cauchy give kl+3(k+l)≤39. Hence k+l≤10, and equality forces (k,l)=(1,9) or (9,1). Complementation proves the proper-cover bound. This is a geometry theorem, not an unrestricted circuit lower bound. Compile exit0; only harmless simp warnings; independent static review approved exact final bytes.

A related local restriction was mathematically reviewed but is not Lean formalized: in a least-size circuit minimizing dirty OR gates, an exclusive primary-leaf OR cone with at most two OR gates feeding a dirty AND can only have the three-cross-edge P4 profile. Nested/identical supports absorb; overlapping pairs rewrite to a OR bc; literal times OR3 cleans to a substar; zero/one/two accepted cross edges have a clean realization in at most three gates. The zero-profile case uses deletion/constant propagation. Thus any other first nonlinear source needs a larger cone or actual sharing outside the cone. This does not give a global gate bound.

Fresh upstream e125f04d census: all456 new Lean files inspected by filename and relevant bounded helper scans;392 final L statements extracted. None provides a projective-plane or relevant larger-core shortcut. Most are seven-input one-NOT elimination and eight/nine-input circuit bounds. Full census JSON remains in scratch/proof-route/new-theorems-1616.json.

Primary sources read on 2026-11-25:

- Tarjan, Stanford report STAN-CS-76-553, Theorems7–8: https://ftpmirror.your.org/pub/misc/bitsavers/pdf/stanford/Stanford_CS_TR_Collection_2025-12-12/OCR/CS-TR-76-553-ocr.pdf . The exact projective-plane multioutput linear-sum bound rules out saving a gate solely in the neighborhood-sum stage.
- Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, Remark10: https://arxiv.org/pdf/1406.3065 . Read directly; its restricted-model bounds must not be transferred to unrestricted single-output Boolean circuits.
- Jukna, Disproving the Single Level Conjecture: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf . Its verified single-output constructions use saturated graphs and do not directly embed into these incidence graphs.
- Krapivin–Przybocki–Subercaseaux, Near-Optimal Encodings of Cardinality Constraints, AppendixA.2: https://arxiv.org/html/2603.28954v2 . Its threshold construction is verified at source, but no C4-free incidence adaptation was found.

No 63-gate witness, full refutation, or full checker acceptance resulted from this work.

## 16:50 UTC: complete posted tests and auxiliary OR search

The extended FullPlaneCover2056.lean now compiles at SHA256 36a295bcdc1049470b895bb62cf99b2089d8fccf42f75c2df91a4b3d8344c76e. It derives that every nonincident pair of point/line sets has a side of size at most3, then proves generic circuit monotonicity and the exact posted_tests_determine bridge: every Monotone2 circuit passing the posted positive and small-side closure tests computes the full incidence function on all assignments. Complete compiler logs are scratch/proof-route/full-plane-complete-3.stdout and .stderr; exit0, warnings only. Gate agent independently approved the final-byte delta. This bridge contains no small-circuit existence claim.

The inverse-hoisting identity p*R OR G = R*(p OR G), valid when G implies R, produces exact seeds at baseline+1. Frozen inverse-hoist collections contain 24x30,19x30,32x40,52x65 gates for the same four geometries; the full collection SHA256 is 3ed3c987ff1674771b7c332080a64c50bc29922f42e0715e2ef02002c8795b12. Independent review checked complete boundaries, full truth tables for the three smaller families, zero earlier-wire dominance, and exactly one intentional mixed-OR normalization violation per seed. They belong only in the unconstrained exact-state portfolio, not in SAT queries assuming mixed-OR normalization.

An exact triangle-merge identity was found: for F=aR OR bS OR cT, define H_ab=(a OR b)*(R OR S) OR cT and cyclic versions. Then F=H_ab AND H_bc AND H_ca, because any false assignment has a same-valued pair among a,b,c, making that merged function false. An odd cycle of pair merges works for the same reason. The naive implementation has too much overhead and is not a saving.

Parent requested a finite OR-basis search for the current70-row SAT sample. Its18 negative rows leave only five extra point-line pairs legal: (0,12),(1,11),(4,11),(6,9),(8,3). Thus each of five point outputs may choose its original4-neighbor set or its allowed5-neighbor set, yielding32 output families. Encoder or-basis2056/or_basis.py chooses from198 non-singleton supports, allows every union of two strict submasks including overlaps, and bounds the shared OR basis by38. Thirteen point ANDs and12 final ORs would then yield a sample-valid63-gate circuit. The fixed39-OR baseline control is SAT, all clauses and full756 boundary rows verified; fixed39-support control under budget38 is UNSAT. These are encoder controls, not yet a target-search verdict. Any UNSAT result would concern only this restricted OR-preprocessing architecture.

Final OR-basis encoder SHA256 b13933cd293bbce6eb92320d8a1b31e9b94bc85485543311d2e946d36324c6b4 was independently approved, including all20949 clauses of the39-OR control model and its reconstructed64-gate full-boundary circuit. The only target probe ran10 seconds and returned UNKNOWN, not UNSAT. Complete control/probe summaries and stdout/stderr are preserved under or-basis2056; CNFs/models/mappings remain in scratch/proof-route/or-basis2056. No long OR-basis search was launched. A fully correct63-gate circuit in this architecture would contradict the existing checked read-one lower bound, so its purpose is sample candidate generation for later unrestricted repair.

The OR-basis route is now closed by a short mathematical restricted-model argument, independently audited by gate_elimination. Every pair of original4-neighborhoods intersects in exactly1 line. Every pair of allowed enlarged neighborhoods intersects in at most2 lines (21 pairs have intersection2,57 have intersection1); consequently the19 shared nonsingleton supports are all pairs. Cut all pair-support OR gates B. Every remaining support-at-least3 gate can reach at most one output, so these output-private cones are disjoint. If the private cone of output p contains g_p gates, its distinct boundary supports (singletons/pairs) number at most g_p+1 by connected fanin-two DAG counting. To cover its four required original neighbors, 4≤g_p+1+t_p, where t_p counts boundary pairs wholly contained in that original neighborhood. Each pair belongs to at most one original neighborhood, so sum(t_p)≤number(B). Summing gives at least39 OR gates. Duplicate, singleton, and unused gates cannot weaken the bound. This is not Lean formalized and says nothing about unrestricted AND/OR circuits; the10-second SAT probe itself remained UNKNOWN.

## 17:00 UTC: shared dirty-AND seeds

A new identity creates a dirty nonlinear value reused in two filtered branches:

    D = (a OR b) AND (c OR d)
    F = ((D OR T) AND b) OR ((D OR S) AND c)
      = bc OR bd OR bT OR ac OR cS.

Here b,c are adjacent centers, a is another neighbor of c, d another neighbor of b, and S,T contain the remaining assigned leaves. C4-freeness makes ad a nonedge, so D is dirty. Its unwanted ad term is removed differently in the two branches. Empty S/T omit the corresponding OR. Both nonempty contexts combine dirty operands; the final branch ANDs are clean stars. This costs two gates above the ordinary double-star region and three above the pure point-star baseline. It is an exact seed identity, not a saving or a lower-bound theorem; its algebraic reducibility to stars remains expected.

Generator patch2056/reused_dirty_seeds.py produced frozen families:

- six-reused-dirty-seeds.json:90 circuits of32 gates; SHA256 c44050e5b209d514d6733a949cc7dc96a10f6c5cba437acc166cdebc28cf09ca.
- collinear6-reused-dirty-seeds.json:90 circuits of32 gates; SHA256 9b41f3ad6440d7ff9670ce740c84b66082e3c68feafd0ff7819cd1716c782f52.
- eight-reused-dirty-seeds.json:168 circuits of42 gates; SHA256 d0217a6716076c4c005ad6b530e13709f9a8adbfcd3faf539adfad72f2e19564.
- full-reused-dirty-seeds.json:468 circuits of67 gates; SHA256 5bcd8b8e9930f065a141e01d89a4ed57b938ce3e046514d5d3513c3d1d05a5c6.

Status reviewer independently checked every boundary row and every assignment for all smaller circuits; every full circuit passed all756 complete boundary rows. All have zero clean-wire normalization violations, zero earlier-wire directed dominance, and exactly3 accepted edges without a read-one proof. The marked dirty AND has exactly two actual uses and two distinct next-AND consumers, verified independently. Audit report: scratch/reused-dirty-audit.json. The full family is intended for the parent's next70-slot exact-state portfolio; it contains no63-gate witness.
