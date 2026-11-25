# L-meta-2373 orchestration notes

Lease acquired 2026-11-25T12:53:05.140Z. Only root holds and renews lease.
Target: two incomparable subfunctions of the Petersen edge function, computed jointly in 18 gates, cannot cover it. Adding their OR would produce a 19-gate circuit.
Allowed project module: PEqualNP.Defs. Reductions enabled but all three slots occupied.

Agents: status_review (independent mathematics), proof_structure (direct lower bound), counterexample (finite search), library_route (reusable proof source), lean_setup (toolchain/cache).

Each agent may append uniquely named findings. Do not overwrite other sections.

## status_review: mathematical assessment (2026-11-25)

L-meta-2373 is exactly the essential final-OR case of a 19-gate Petersen circuit. If its existential conclusion fails, the two selected wires OR to Petersen on all 1024 rows; incomparability means neither final OR input can be discarded. The three existing reductions are already live: R_meta_2373_1 splits the tail budget 16/17; R_meta_2373_267 normalizes first-gate type and selected wires to Fin18; R_meta_2373_71 uses vertex restrictions (zero bound15, one bound10). The latter zero lower bound is now proved in main by L_meta_670 (directSplit at line6178, final theorem6863), but its source is large and outside imports are forbidden here.

No counterexample or simple contradiction found. The soundness hypotheses alone imply selected wire indices are at least10, incomparability makes them distinct and gives indices below28. A naive fanout counting argument is invalid: in a star-factor circuit a center input can occur once while its three-neighbor OR costs two internal gates. Full proof likely needs the existing restriction/certificate machinery.

## library_route — 2026-11-25T12:56:02.394275+00:00

The target is hOr of R_meta_651_2. Three checked reductions already exist: R_meta_2373_1 splits tail size <=16 versus =17; R_meta_2373_267 normalizes the first gate into distinct-input AND, Fin11-input OR, or Fin11-input NOT and proves both relevant output wires lie in [10,28); R_meta_2373_71 reduces to two 9-input cofactor lower bounds plus a difficult restriction theorem. No fourth reduction slot is free according to desk reductions_live=3.

L_meta_670 (6864 lines, 523341 bytes) proves Petersen-minus-one-vertex has no <=15 gate AND/OR/NOT circuit. This is exactly R_meta_2373_71 hzero. It uses certified live-wire exhaustive search with pruning by separating rows and cofactor lower bounds: BitVec512 truth tables, directSplit at line6178, monoRoot at6852 and signedRoot at6857. Signed mode grants free wire complementation but bounds binary gates by14; mono mode bounds gates by15. Large packed Nat certificates are checked by decide +kernel. New 10-input target requires 1024-bit tables and new certificates. Reusing whole source leaves947 bytes under512KiB before namespace-length changes; comment stripping/dead-code pruning needed.

Existing general EdgeFnPlan lower-bound route only assumes girth>=7 and distinct degree>=3 vertices at distance>=7. Petersen violates both assumptions. LratEncoding root covers AND/OR only, so direct application cannot handle NOT. Current library search found no complete full-Petersen size19 exclusion, only conditional cases (e.g. L_meta_5238 excludes >=5 NOTs after free nonedge OR).

## counterexample — 2026-11-25T12:57:02.861224+00:00

No semantic loophole: the two circuit stages concatenate exactly; out-of-range reads are false. Enumerated all 1024 vertex subsets: minimum vertex cover is6, with5 covers; a star factoring circuit has20 gates. A 19-gate stochastic search currently reaches weighted error6 but no exact witness. Source and complete log: /tmp/oec/pequalnp-pilot-87/counterexample/search.cpp and search-log.txt.

SAT synthesis implementation synth.py uses one-hot AND/OR/NOT selectors, legal earlier-source selectors, free false input (empty AND represented by NOT false), and final OR. Initial91 truth rows are all independent sets plus all weight<=2 assignments. A fixed20-gate reference circuit was SAT-validated on all1024 rows. CaDiCaL search now running for first gate AND(0,1), with all gates live and heuristic sorting of consecutive independent gates. Any SAT witness is checked on all1024 rows; heuristic UNSAT alone is not a theorem. Solver binary is bundled Lean cadical.

## finite_invariants: two disjoint five-cycles

Petersen vertex-cover lower bound6 follows from two disjoint C5s, not an exhaustive search. Any nonnegative integer weights covering each edge have outer-cycle sum≥3 and inner-cycle sum≥3. Both arithmetic lemmas passed Lean4.36.0 (`Core.lean`, exit0) and were inserted as helpers in target file. Python independently enumerated all1024 subsets: minimum cover6, exactly5 minimum covers, 76 total covers. A minimum cover is {1,3,4,5,6,7}. Finset/cardinality bridge being checked. This proves star-cover cost≥20 but alone does not lower-bound arbitrary circuits.

## proof_structure — direct combinatorial route

The standard monotone star formula has20 gates: Petersen has15 edges and vertex cover number6, giving15+6−1. A full unrestricted proof cannot simply assert all inputs have fanout at least2; cover-center inputs may be read once.

The substantial generic route in L_meta_1549 (322455 bytes) proves a 15-gate theta-graph lower bound. Its branching_budget (line6605) gives size≥n+number_of_branch_wires+NOTcount−1 for a least clean circuit. Its class-twin bridge (lines6723–6971) reduces branch count to iterative maximal twin-class deletion in the graph. A Python exact dynamic program over1024 subsets confirms Petersen needs6 such deletions (an optimal sequence is {0},{1},{3},{7},{8},{4,6}). This yields only size≥15+NOTcount, settling≥5 NOTs, consistent with L_meta_5238. It does not settle0–4 NOTs. A stronger weighted fanout invariant would be needed; no such invariant established.

Other genuine lower-bound templates: L_meta_1543 and1547 cover C7 plus3 pendant edges, giving14 gates. These are large gate-elimination developments, not a short reusable full Petersen theorem.

## status_review: independent partial review

Reviewed the initial upper-bound partial and finite_invariants additions before first push. Its15edge terms match the desk statement exactly; independent Python evaluation checked all1024assignments of the20-gate circuit, including all fan-in and earlier-wire index conditions. The two arithmetic lemmas are sound: summing a5-cycle cover inequalities gives2*sum>=5 and hence sum>=3 over Nat; disjoint outer and inner5-cycles give total>=6. Added source uses only omega and prior helper, with no added axioms or forbidden format tokens. This remains PARTIAL: the named target theorem is absent and no checked lower bound is claimed. Reviewed notes and timeline contain no credentials. Lean build is checked separately by root.

Finite helper progress 2026-11-25T12:59:57.427951+00:00: `Finite.lean` passes Lean with no output. It bridges exact Petersen Boolean edge expression to `petersenEdges : Finset (Fin10 × Fin10)`, proves every vertex cover has≥6 vertices, supplies a6-vertex cover, proves every independent set has≤4 vertices, and proves every false input has≤4 true coordinates. A further common-neighbor certificate and biclique-is-star theorem are in progress. Root has the two basic cycle-weight lemmas already.

## lean_setup: kernel certificates — 2026-11-25T13:00:20.215514+00:00

Official Lean v4.36.0 and all 9117 pinned Mathlib cache files are installed under scratch; launcher /tmp/oec/pequalnp-pilot-87/lean-env.sh handles environment. Initial kit warm-cache claim did not match actual environment. No Mathlib theorem sources were built.

Do not use bv_decide: pinned Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean invokes nativeEqTrue at line40 and the tactic adds a compiled-check axiom. Project Library/LRAT/Checker.lean (26553bytes) is an alternative designed for kernel evaluation; checkW_sound F keys width packedWords (by decide +kernel) proves FormulaSat F is false. It stores each clause as a Nat bitmask and each certificate block as at most1024 fixed-width fields inside a Nat under a sentinel top bit. checkFirst/checkSeg/checkLast permit memory-bounded segmented replay.

A general NOT-capable encoding bridge already exists in Library/LRAT/LinkN.lean (55210bytes), with valid_ofCirc covering arbitrary FanInTwo circuits including out-of-range false, and LinkN2.lean supplies the normalized enc2_sat bridge. These are not authorized imports for this gap, so definitions and proofs must be inlined, with Model/Valid/NF structures replaced by existing product types if automatic merge is required. L_meta_5531 (427428bytes) demonstrates an inlined checker using Mathlib BinaryTree and packed proof data. SAT proof size remains the likely obstacle.

L_meta_670 already packs its finite-search data: removing line comments and blank lines only shrinks523341to522639bytes. Indentation totals another14049bytes, so trivial text compression will not buy much. PR12203 has empty body and only the one proof file, with no generator link; it timed out repeatedly and closed after another proof merged. No generator found in current tools/Library filename scan.

2026-11-25T13:02:49.279368+00:00: `Biclique.lean` and `BicliqueFast.lean` both Lean-checked. The former is preserved as results/orch/lemmas/FiniteInvariants.lean. New facts: every distinct pair has at most one common neighbor; hence every complete bipartite subgraph of Petersen has one side of cardinality≤1. This is the biclique-is-star step needed for a monotone lower bound. Generic biclique-cover number≥6 proof is being checked next.

## status_review: second partial review

Reviewed changes after501d6e75 adding petersenEdges, vertex_cover_size, minimum_vertex_cover, independent_set_size, edge_eq_false_iff, and false_input_support_size. The Finset contains exactly the posted15edges. Cover bound6 follows the two disjoint odd5-cycles; explicit witness {1,3,4,5,6,7} covers every edge. Complement reasoning correctly bounds independent sets by4, and the Boolean bridge gives false-input support size<=4. No forbidden source tokens or new axioms; no change to theorem objective. PASS as additional PARTIAL results, subject to root Lean build.
