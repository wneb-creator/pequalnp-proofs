# pequalnp-pilot-86 — L-meta-2585

Assigned 2026-11-25 12:22:17 UTC. Only root holds/renews lease. Reductions are not open.

Statement: ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1

Strategies will report here; use append-only updates. Helper work belongs under results/orch/lemmas or assigned scratch, not the final file.

## Environment/checker review (status_review, 2026-11-25 12:25 UTC)
- Current repo requires helper declarations inside a module-specific namespace; fully qualified final theorem must be last.
- Updated checker is check-lean 4 and supports check, refute, reduce. Updated outside guard explicitly supports refutations and reductions; earlier pre-fetch caveat is obsolete.
- No lean/lake/elan on PATH. Bounded exact-filename discovery in /workspace/pequalnp-proofs, /opt, /usr/local found only repo shim tools/bin/lake, no installed toolchain executable.
- lean/.lake is absent entirely, so no project Mathlib package or warm cache is available in the current checkout.
- Repo shim accepts PEQUALNP_REAL_LAKE to select installed lake. Build queue accepts PEQUALNP_HOME to place queue/cache in job scratch; use that rather than inaccessible home storage.
- Guard usage now: node .github/scripts/outside-guard.mjs imports <file> <imports.json> <PR-relative-file> [kind].

## 2026-11-25T12:24:12.644461+00:00 — proof_route

The target L-meta-2585 is exactly the `normalize` hypothesis of accepted R_meta_2976_418. Existing L_meta_4897 proves the bipartite C4-free read-1 lower bound E.card + A.card + B.card <= C.size + 1, where A/B cover edges. L_meta_2237 and L_meta_6369 are graph versions. None is transitively available through Defs, but proofs can be copied under own namespace if needed.

L_meta_3720 (763 lines; imports only Mathlib and Defs) already proves the known normalization portion of the desk sketch for arbitrary f: a least AO2 circuit, no non-below OR with satisfiable below-f operand, no AND operand below f, all gates live. The hard missing mathematical implication is still conversion of non-star blocks to a star-cover budget.

The root repository note notes/note-1-edge-function-exact-size.md explicitly treats unrestricted C4-free exact lower bounds as outside the proved forest/long-thread regime. It cites Jukna Disproving the single level conjecture (TR05-021) as relevant literature; no result for our exact class inferred from that citation.

## Construction route — 2026-11-25 12:25 UTC

The standard star-cover circuit exists as `PEqualNP.MetaComplexity.coverCircuitB`, with nonempty owner lists costing `sum lengths + number owners - 1`. Formal correctness helpers exist under `MetaComplexity/Helpers/CoverCircB*.lean`, outside allowed imports, and can be adapted. Exact-size replacement would follow from arbitrary AO lower bound `|E| + min vertex cover - 1`; that is the difficult part, whereas this formula is proved for read-1 in related Outside proofs.

Created `results/orch/lemmas/Construction.lean` with zero-incidence replacement case; waiting for usable Lean environment before checking.

## Counterexample route, 2026-11-25T12:24:21.475497+00:00

No degenerate refutation: an empty incidence has an empty-circuit witness with missing output and vacuous ReadK; a nonempty incidence rules out missing output. ReadK implements simultaneous multiplicities correctly. The general claim appears to imply optimal graph-function complexity |E| + vertex-cover number - 1 for bipartite C4-free graphs; I have not established this equivalence formally. Known single-level separations use graphs with extra intra-part edges, so they do not immediately refute this statement.

Primary research read 2026-11-25: Jukna, Disproving the Single Level Conjecture (https://eccc.weizmann.ac.il/report/2005/021/download), search-returned text from the PDF states circuit lower bounds for C4-free quadratic graph functions require new arguments; this is only background, not a proof or counterexample. ArXiv abstract https://arxiv.org/abs/2207.08701 confirms the ReadK notion matches Boolean read-k circuits.

## 2026-11-25T12:24:45.374876+00:00 normalization

Accepted L_meta_4295 establishes termination of Lift; its helpers include preservation of size, IsAO2 and function. Adapted it into results/orch/lemmas/Normalization.lean with an added combined normal-form existence lemma; compilation pending environment setup. This only normalizes below-output OR inputs. Accepted L_meta_7649 proves a star-cover cost bound if every non-below-output gate is OR, so removing or charging junk AND gates remains the unresolved mathematical bottleneck. L_meta_4742 and L_meta_4747 eliminate certain ONE-junk cases but not arbitrary junk circuits.

## Toolchain recovered (status_review, 2026-11-25 12:25 UTC)
- Installed official Lean 4.36.0 release under /tmp/oec/pequalnp-pilot-86/lean-4.36.0-linux.
- Executables: .../bin/lean and .../bin/lake. Lean --version confirms 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9.
- Full download/extraction logs in named scratch; extracted successfully. Downloaded archive removed after extraction.
- Install takes 3.1 GiB. Remaining filesystem roughly 3.8 GiB, potentially tight for full Mathlib cache.

## Counterexample exhaustive search, 2026-11-25T12:26:03.295584+00:00

C++ search checks all nonempty C4-free graph targets for a fixed bipartition against circuits smaller than |E|+minimum vertex cover-1. It stores full truth tables (up to six inputs), enumerates AND/OR gates reading two earlier distinct wires, removes gates duplicating an existing truth function, and orders adjacent independent gates by truth-table value. Coverage rationale: duplicate/idempotent gates can be removed with later wires redirected; any circuit has a lexicographically least topological ordering, where an adjacent independent inversion cannot occur. Earlier output gates can be made last by deleting unused suffix. These transformations preserve the computed function and do not increase size.

Completed no-counterexample searches: P=2,L=3 up to 4 gates (53 targets; 87,388 canonical size-4 circuits); P=L=3 up to 6 gates (333 targets; 325,324,930 canonical size-6 circuits). A seven-gate search is running. Small independent unpruned enumeration confirms all minimum output costs match the pruned enumeration for n=3 up to 4 gates and n=4 up to 3 gates. Constructed and checked explicit minimum-vertex-cover star circuits for all 333 targets: exact truth tables and polynomial supports equal the squarefree edge monomials, hence each is read-1. These are computational findings, not Lean proofs. Full source/logs are in /tmp/oec/pequalnp-pilot-86/counterexample.

## 2026-11-25T12:27:24.922966+00:00 normalization literature context

Read https://pequalnp.com/papers/note-1 on 2026-11-25 using curl (web open failed; saved complete HTML under scratch normalization/note-1.html). The project note says its cited Jukna 2014 source gives the edge-count bound for restricted monotone models, while a corresponding general monotone Boolean bound was not known. The original Jukna source was not opened here, so the literature attribution remains UNVERIFIED independently. This explains why extending Lift normalization to remove arbitrary junk ANDs is not a routine formalization.

## Construction route — 2026-11-25T12:28:20.360696+00:00

Created `Star.lean` (~400 lines) implementing recursive OR of a nonempty neighbor list, followed by AND with a distinct center. Target lemmas give IsAO2, exact degree size, evaluation, and IsReadK 1. Created `Support.lean` by adapting the existing support argument to arbitrary essential-input subset A, proving `A.card ≤ C.size + 1`. Awaiting first cache/Defs build before compiling. Their combination proves optimality for one star, and extends mathematically to disjoint star forests because |involved vertices| = |E| + number nonempty stars. Self-check found no forbidden quotes, attributes, or root namespace escape.

## Cache recovered (status_review, 2026-11-25 12:28:23 UTC)
- Required lake exe cache get succeeded, exit 0, for 67 direct Mathlib imports of all Defs modules; 2480 dependency files downloaded and decompressed.
- Logs: /tmp/oec/pequalnp-pilot-86/cache-get.stdout and cache-get.stderr (complete).
- Subset artifacts use 2.0 GiB; approximately 1.8 GiB filesystem space remains. Full Mathlib is needed by checker: CheckLemma.lean fixes statementLibrary to Mathlib and imports it. No narrowing flag exists.
- Lean Environment.lean readModuleDataPartsOfMod loads server/private data unconditionally for modern modules; do not prune those. Executable linker defaults to static Lean; retain static libraries.

## 2026-11-25T12:30:04.052695+00:00 — proof_route checked clean-block lemma

`results/orch/lemmas/StarBlock.lean` compiles with Lean 4.36.0 via lake env lean, exit 0, no warnings after replacing deprecated push_neg. It proves any rectangle contained in a C4-free incidence relation has a side of size at most one; a nonempty rectangle is a star. This is a partial lemma, not the posted normalization statement. Complete stdout/stderr are scratch proof-route/starblock3.stdout and starblock3.stderr (both empty on success).

## 2026-11-25T12:31:43.315929+00:00 normalization partial status

Normalization.lean is now 713 lines. New conclusions beyond source L4295: lift invariants transported over the whole chain; OR inputs have equivalent below-output status for any function vanishing on singleton assignments; specialization to bipartite incidence functions; nonempty incidence implies a valid output wire. Static independent review by status_review found no formal-rule issue and no claim of read1. First compilation attempt was blocked only by missing Defs.olean during the root dependency build.

## 2026-11-25T12:31:47.949744+00:00 — OR-only charging component (math_bound)

Located accepted L_meta_8435, whose 245-line initial charging argument supplies the needed OR-only direct sum bound. Adapted to independent row/input counts in `/tmp/oec/pequalnp-pilot-86/math-bound/OrBound.lean` (326 lines), namespace `PEqualNP.Outside.L_meta_2585_aux.OrBound`; compilation waits for Defs.olean.

The proposed corollaries state: for S : Fin m -> Finset (Fin n) with distinct rows intersecting in at most one variable, an OR circuit serving each nonempty row at cost c has sum_p (|S p|-1) <= c. Equivalent active-row form is sum_p |S p| <= c + number of nonempty rows. The proof charges every nonminimum row member to the earliest gate whose support is inside that row and contains a smaller member. C4-freeness makes the row unique, and binary-merge earliestness makes the charged member unique. This does NOT handle dirty AND gates and does NOT prove L-meta-2585.

- 2026-11-25T12:31:54.626898+00:00: StarBlock extended with `neighborhood_inter_card_le_one`, using Mathlib.Data.Fintype.Fin. All 56 lines compile with exit 0 and no warnings; complete logs proof-route/starblock5.stdout, starblock5.stderr.

## 2026-11-25T12:36:06.722550+00:00 independent SinglePoint review by normalization

Reviewed full SinglePoint composition, matching SinglePointBody suffix, Star read1-vector argument, and Support essential-input cardinality proof. The exact P=1 result is mathematically sound: degree d supplies d+1 essential variables, giving d≤C.size; the star circuit uses exactly d gates and is read1. Empty incidence has no prime implicants. No forbidden source features found. SinglePointBody is an assembly fragment and should not be built independently. This review does not certify compilation or extend the result to general star forests.

## Counterexample searches replanned, 2026-11-25T12:36:09.622126+00:00

Exact SAT synthesis independently found C6 seven-gate UNSAT (Cadical exit20); explicit eight-gate positive control SAT, including new symmetry constraints. A seven-gate exhaustive search for all333 3+3 targets remains running. Search artifacts in results/orch/searches are computational evidence only.

Important upstream discoveries: L_meta_723 line3448 proves the subdivided K4 monotone bound15. L_meta_971 line9365 proves the Heawood/Fano monotone bound27, and L_meta_7995_aux.ao27 line9428 directly covers cyclic Fano. Hence K4 14-gate and Fano26 searches were stopped as mathematically settled. The cyclic Fano-to-L_meta_971 isomorphism is point image (0,1,2,6,5,3,4), line image (3,0,6,1,2,5,4).

Active replacement: subdivision of K5, P=5,L=10,20 incidence edges, explicit star baseline24. Search budget23 gates. Exact SAT has60min cap; stochastic search30min. SAT uses all20 edge assignments plus all maximal independent assignments, sufficient for monotone equivalence. Symmetry constraints sort adjacent independent gates by operand indices/op and choose first-gate input-pair orbit representatives under120 explicitly verified graph automorphisms. Both reductions preserve a representative: globally lexicographically least circuit under topological orders and graph automorphisms satisfies both.

## Prime implicants checked (status_review, 2026-11-25 12:36:51 UTC)
- results/orch/lemmas/Prime.lean compiled with lake env lean, exit 0; one unnecessarySimpa warning only. Full logs copied to results/orch/logs/prime.stdout and prime.stderr.
- prime_incidence_iff: prime implicants are exactly incident pairs, without requiring no-four-cycle.
- read_one_of_incidence_edges: READ-1 witnesses for incident pairs imply IsReadK 1 for any circuit computing the incidence function.

## 2026-11-25T12:37:20.838420+00:00 — OrBound checked (math_bound)

The full actual-circuit OR-only bound now compiles with Lean4.36 (exit0, empty stdout/stderr), using only PEqualNP.Defs. Source and complete logs copied to results/orch/lemmas/OrBound.lean and results/orch/logs/orbound.{stdout,stderr}. Sharp statement linear_family_or_cost: rows with pairwise intersections at most1, every nonempty row served by an OR circuit with c gates, then sum_p (|row_p|-1)<=c. Active-row and all-row cardinal corollaries included. This is a checked partial; it does not handle general AND/OR circuits.

## 2026-11-25T12:37:28.961952+00:00 normalization compilation and Prime review

Actual Normalization.lean with allowed Defs import compiled successfully (exit 0, empty stdout/stderr), after scratch minimal-import debugging also passed. Complete logs and validation preserved in results/orch/logs/normalization.*. Independently reviewed Prime.lean: prime-incidence equivalence and read1 bridge are semantically correct, and no forbidden source features were found. Root notified both are ready for partial preservation.

## 2026-11-25T12:38:01.622633+00:00 — abstract union computation bound checked (math_bound)

Also checked UnionCount.lean (223 lines), the same charging theorem for any finite computation starting from singleton supports and adding one binary union per gate. It imports only narrow Mathlib modules, has no project dependency, and proves sharp sum(rowcard-1)<=number of gates for C4-free output families. Source and complete empty success logs in results/orch/lemmas/UnionCount.lean and results/orch/logs/unioncount.{stdout,stderr}.

## 2026-11-25T12:39:06.255275+00:00 — checked multilinearity bridge

`results/orch/lemmas/Multilinear.lean` proves `IsAO2 n C → IsSyntMultilinear n C → IsReadK n C 1`, with no restriction on the computed function. The scan invariant assigns every true wire a witness set T supported by its syntactic support, whose 0/1 indicator is an actual read vector. Disjoint AND supports keep capped vector sums 0/1. Final result compiles in Lean 4.36.0, exit 0, empty stdout/stderr in results/orch/logs/multilinear.*. Independent math_bound semantic/format review passed; final hash confirmation pending after a purely definitional conversion fix. This is a sufficient invariant for the posted target, not a proof that every minimum incidence circuit has it.

## Construction route — 2026-11-25T12:39:39.940565+00:00

`results/orch/lemmas/SinglePoint.lean` PASSED Lean compilation (exit 0). It combines the checked empty case, exact-cost one-star construction with read-1 vectors, generic essential-input cardinal bound, and the full replacement conclusion when P=1 and L/I are arbitrary. No C4 condition is needed for that special case. Complete compiler output is preserved in `SinglePoint.validation.txt`. The full posted statement remains open; this is an exact special case, not a replacement statement for submission.

## 2026-11-25T12:40:31.032753+00:00 — dirty-block obstruction checked (math_bound)

DirtyBlockExample.lean compiled exit0, complete empty logs saved. For matching edges p0-l0 and p1-l1, C = ((p0 OR p1) AND (l0 OR l1)) AND ((p0 OR l1) AND (p1 OR l0)), seven gates. Lean proves AO2 validity, exact matching function, every interior wire (all ten wires before output) NOT below output, and NOT ReadK1. Therefore lift fixedpoint / no below-function interior wires cannot alone imply star/read1 form. A three-gate star circuit exists, so minimum-size remains essential; this is NOT a refutation of L2585.

## Candidate-verification lemmas, 2026-11-25T12:42:33.357336+00:00

GraphTests.lean and IncidenceTests.lean both compiled with queued lake env lean, exit0 and no diagnostics. Normalization agent independently reviewed both, PASS. These are general monotone-function test criteria, not a proof of the leased step. IncidenceTests reduces verification to all point subsets by completing each to an independent assignment on the line side. CircuitMonotone.lean is being prepared by the normalization agent to connect these criteria to AO2 circuits.

CycleSix.lean compilation was cancelled after several minutes, because its finite upper bound is already known and it contributes nothing to the general open step; do not report that file as checked.

Additional target: projective-plane order3,13+13 inputs,52 edges, star bound64; a63-gate stochastic search uses756 exact monotone tests (52 edges+704 maximal independent sets). Upstream census found only restricted64-gate lower bounds, not an unrestricted one.

CORRECTION 2026-11-25T12:42:45.459289+00:00: CycleSix.lean finished successfully before the cancellation request arrived. Tool result was exit0, stdout/stderr empty. All its lemmas, including read1, compiled. The preceding cancellation statement is superseded.

## Re-plan 1 — 2026-11-25T12:43:47.316148+00:00

The checked clean-block, OR-only cost, prime-implicant, normalization, multilinearity/read-1, and exact P=1 components are preserved. Stop producing alternate OR-only formulations. A checked seven-gate matching circuit refutes the shortcut from lift-normalization alone to read-1; a minimum path circuit can still reread before lifting. Focus mathematical work on a representative that is both least-size and lift-normalized, and on charging its genuinely dirty AND blocks.

Counterexample searches moved away from subdivided K4 and Fano after refreshed upstream revealed accepted lower bounds. Active targets are subdivided K5 and PG(2,3), with SAT positive controls and finite verification criteria. Formal work continues on clean-normal-form-to-read1 and concatenating read1 star blocks.

The assigned file now assembles six checked components, 2251 lines, pending combined build. The local checker returned CHECKER FAULT because full Mathlib.olean cache is absent; this is not an acceptance or rejection of the partial theorem. Full posted target remains unproved; reductions are unavailable for this lease.

## Circuit concatenation validity checked (status_review, 2026-11-25 12:43:53 UTC)
- MergeValid.lean compiled exit 0, no diagnostics. Full logs and validation file copied to results/orch.
- shIdx preserves input indices and shifts non-input indices; concat appends a shifted copy of D after C. concat_valid preserves AO2; concat_size is additive; concat_output preserves a valid output bound.
- Independent review requested from normalization agent before root preservation push.

## 2026-11-25T12:44:50.560962+00:00 new compiled bridges

CircuitMonotone.lean compiled: all AND/OR circuits preserve pointwise truth, with an IsAO2 wrapper for candidate verification. CleanTopForm.lean compiled and independently reviewed by proof_route: TopForm plus all AND gates below the graph function implies no nested ANDs and singleton rejection at each AND. These are conditional preprocessing bridges; arbitrary dirty AND gates remain unresolved.

## 2026-11-25T12:45:26.635618+00:00 — checked no-nested-AND bridge

Multilinear.lean now also proves `no_nested_and_multilinear`: AO2, no AND gate in the strict cone of another AND, and every AND false on singleton assignments imply syntactic multilinearity. The support of an AND-free operand is witnessed by an OR path, so a variable shared by both operands would make the AND true on its singleton. `and_pairs_zero_read_one` packages this with the previous read-vector theorem. Lean exit 0; complete stdout/stderr empty. No claim is made that every least incidence circuit has these conditions.

## 2026-11-25T12:46:22.946288+00:00 clean-case bridge underway

CleanJunk.lean compiled (empty junk implies every AND below graph function). CleanReadOne.lean combines checked clean topology with proof_route agent multilinear result to prove read1 conditional on TopForm and empty junk; it is being compiled. These hypotheses are still not established for arbitrary input circuits. Combined file replaces individual Multilinear/CleanTopForm/CleanJunk assembly entries.

## 2026-11-25T12:46:32.671019+00:00 — higher-degree dirty obstruction checked (math_bound)

HigherDirty.lean now compiles exit0 with empty logs. C is a23-gate CNF for matching3 G = x0*x3 OR x1*x4 OR x2*x5. H is its penultimate AND wire (wire25), the conjunction of seven transversal clauses except x3 OR x4 OR x5, hence H = G OR x0*x1*x2. Checked: C is AO2 and computes G; every interior wire w<28 is NOT below output; every gate is true on a matching edge; every AND is false on all singleton inputs; H agrees with G on every one/two-variable assignment, but H is true and G false on independent triple{0,1,2}. Thus even all these normalization properties do not imply that a dirty gate has a false pair witness. Only global minimality or stronger transformations can remove this higher-degree obstruction. Not a refutation of L2585; ordinary read1 matching3 circuit has5 gates.

## Computational coverage and stronger tests, 2026-11-25T12:47:05.250271+00:00

All333 nonempty3×3 C4-free targets are now covered computationally: exhaustive circuits through6gates settle every target whose star bound is≤7. Exactly6 targets have bound8, and verified line permutations identify each with C6, whose7gate SAT instance is UNSAT. Therefore the huge7gate enumeration was stopped as redundant; it did not complete. Explicit permutations are saved in results/orch/searches/six-cycle-isomorphisms.json. The empty incidence has a trivial empty circuit. This is still not a Lean proof of the universal3×3 case.

ClosedIncidenceTests.lean compiled with queued lake env lean, exit0, empty logs; independently reviewed PASS by normalization agent (SHA2565ab12db77015093f5394dea08b362e17f2b2ba34bbbde190875bc611d0accfb1). It exactly justifies using closed point sets, equivalent to maximal independent assignments, as the negative tests. CircuitMonotone.lean from normalization agent compiled and independently reviewed PASS here (SHA2560e7ea608a2cda1ef727eaa3587198eaef3070ba4d99fdd3dc9e5ad9379f34155). Together they support compact Lean verification if a search succeeds.

Third search family: cyclic8×8 incidence offsets0,1,3 (Möbius–Kantor8_3),24edges, explicit star bound31. Seeking30gates. Both my bounded upstream census and independent math_bound census found no exact-instance lower31 theorem, although generic or encoded results could exist. Stochastic search active; exactSAT prepared.

## 2026-11-25T12:48:20.362852+00:00 clean-case read1 checked

CleanReadOne.lean compiled with exit0 and empty logs. It proves IsAO2 plus TopForm plus empty junk implies ReadK1, then chooses the same circuit for the incidence replacement conclusion. Empty junk is a sufficient hypothesis, not shown equivalent to the original task or necessary for read1. Full general dirty-AND case remains open here.

## Construction route — 2026-11-25T12:48:56.425146+00:00

`results/orch/lemmas/FamilyCombined.lean` PASSED Lean compilation, exit 0. `PEqualNP.Outside.L_meta_2585.Merge.replacement_of_star_cover` consumes exactly the valid star-list, coverage, and cost hypotheses produced by L_meta_7649 and proves the full desired replacement conclusion. The proof copies each star circuit with shifted internal wires, ORs their outputs, proves read-vector preservation and READ-1 preservation under OR, and obtains exact cost sum(degrees)+number(stars)-1. This construction needs no C4 condition. Remaining full-goal obstacle: extract a sufficiently cheap star cover from an arbitrary mixed AO2 circuit with dirty AND gates. Complete compiler logs saved in `FamilyCombined.validation.txt`.

## 2026-11-25T12:49:30.046903+00:00 integration and verification review

Independent normalization-agent review passed GraphTests, IncidenceTests, ClosedIncidenceTests and MergeValid. For the 2251-line integration snapshot SHA256 98f250475f8a715ceb61a784c0de5f912d648b19b061e7477cd1ad4c98b02121, all six manifest source hashes and exact body concatenation matched; no forbidden features and no final target theorem were present. Later integrations need their own snapshot review.

## 2026-11-25T12:51:11.113048+00:00 — least dirty-block cost investigation

The checked endpoints isolate the missing implication precisely: from a least normalized AO2 circuit for C4-free incidence, construct a star family whose degree sum plus number of stars minus one is at most circuit size. Pure OR subcircuits admit an injective charge of each nonminimum row element to a merge; dirty AND gates defeat this because they can filter broad shared OR supports. Pair-input semantics alone is insufficient: HigherDirty proves an interior gate can agree with the target on every pair yet accept an independent triple.

A potential graph-induction route would remove a vertex v while deleting at least degree(v)+1 gates when cover number drops by one. Direct star circuits have exactly this budget, but for general circuits no such local deletion argument has been established: singleton support and raw input-reader counts do not control the shared dirty filters. Treat this as an unresolved lemma, not a justified reduction.

Counterexample coordination confirms current searches avoid already checked Fano27 and K4-subdivision15 cases; active candidates are K5-subdivision23vs24, cyclic8x8 incidence30vs31, and order3Singerplane63vs64. No counterexample to the posted universal statement has been obtained.

## 2026-11-25T12:52:26.616795+00:00 integration-002 independent review

Reviewed named file SHA256 9b1d57b57cc02f0dbf799d7db08d378c2ee2d8385800590814df55ff186b177a, 3212 lines, 143385 bytes. All eleven source hashes match assembly-002.json. Exactly one byte-identical Star body was removed from FamilyCombined; one remains inside SinglePoint. Remaining target body exactly matches ordered component concatenation. Allowed imports only at top, own permitted namespaces, no forbidden tokens/attributes/options, no final theorem claiming the gap. Review PASS for partial preservation once aggregate build passes.

## Counterexample search checkpoint, 2026-11-25T12:52:45.874623+00:00

MK8_3 exactSAT30gate search launched12:47:57UTC after root renewal12:47:34. A31gate right-side star circuit, canonically reordered, passes SAT positive control and was independently evaluated on all65536 inputs. The first control used an uncanonicalized left-side star circuit and was correctly rejected by first-gate automorphism symmetry; both logs are retained. This was a control-witness normalization issue, not a solver success or lower-bound result.

Added a dynamic-target search, evolve_graph.cpp: mutate31gate AO circuits on8+8 inputs, infer the graph from accepted cross-pairs, reject C4 or pure-side acceptance, and test all maximal independent assignments. For valid graph functions, prune unused gates and compare size against |E|+maximum matching-1. A positive saving would be a counterexample; any hit is additionally checked on all65536 assignments before output. This explores varying graph targets rather than only the fixed families. Budget30min from12:52UTC.

2026-11-25T12:55:51.029128+00:00 [counterexample] Resource adjustment: only3 CPUs available. Interrupted redundant K5 strict SLS, MK strict SLS, and K5 annealing SLS (all exit130, best error1, no witness); complete logs archived. These are UNKNOWN heuristic outcomes, never proofs. Remaining workers K5 exactSAT, MK exactSAT, PGq3 strictSLS, dynamic8x8 search each reniced to10 to prioritize Lean builds.

2026-11-25T12:56:59.020534+00:00 [counterexample] Prepared separate synthesis_semantic.py with optional minimum-circuit source-incomparability witnesses on complete edge/max-independent test basis. Soundness: comparable input signatures let a gate be replaced by one input without changing any final test, and monotonicity then preserves the exact target. Known K5 subdivision24gate star circuit remains SAT under sym+orbit+semantic constraints (Cadical exit10); full control logs archived. No additional long worker started; original two SAT jobs unchanged. As usual, a negative fixed-gate-count search alone does not exclude strictly smaller circuits unless those counts are separately covered.

2026-11-25T12:57:38.120877+00:00 [counterexample research] Primary source opened/read2026-11-25: Stasys Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, https://arxiv.org/pdf/1406.3065, Remark10 page19 (PDF index18). For (k,k)-free Boolean matrices it distinguishes a multioutput linear-function lower bound from the single-output bilinear graph function, stating: “no such bound is known so far in the boolean semiring.” It then gives the restricted tropical/multilinear bound. Thus the earlier source attribution is now directly verified, not merely the project note's report. This historical statement does not prove present-day impossibility or falsity of L2585.

## 2026-11-25T12:58:42.714916+00:00 edge-invisible semantics checked

EdgeInvisible.lean final snapshot compiled successfully. Replacing one gate by an empty OR lowers the output, and preserves it whenever that gate was false. If that gate is false on every incident pair, the whole incidence function is preserved by monotonicity. This claims same size and AndOrOnly, not IsAO2 or fewer gates. Independent review by read1_construction passed.

2026-11-25T12:59:22.537606+00:00 proof_route: MixedLinear.lean compiled clean (exit0, empty stdout/stderr), 478 lines, sha256 2ebfa0462c5bef08fe2a8974d7a2b3f8166c6a3d0d208fe6ce2dfd21cad77578. It proves a genuinely stronger linear-family bound: for fixed rows S with pairwise intersection≤1, an arbitrary IsAO2 circuit serving every nonempty OR(S p) requires at least sum_p(card(S p)-1) OR gates (orGates counts OR indices). Core purity at outside-row assignment implies singleton support inside row; earliest pure two-singleton merge cannot be AND; OR charging is injective. This does NOT solve selector-dependent incidence restrictions or least dirty-block costs. Exhaustive semantic checks passed n3≤6g (3070 states), n4≤4g (9406), n5≤4g (67336). Logs results/orch/logs/mixed-linear.stdout/stderr.

2026-11-25T13:00:45.037908+00:00 [counterexample] Math_bound proposed intermediate inequality: for C4-free bipartite output, count of edges with a proof reading point endpoint exactly once (line endpoint any positive multiplicity) <= OR-gates+1, symmetrically. Exact three-state polynomial search found no violation for all333 nonempty3x3 targets through5gates, including39,999,763 canonical size5 circuits. States track point-only exponent1, line-only positive exponent, and mixed point1/line-positive; all64 multiplication state cases independently validated by exponent convolution. No semantic duplicate pruning. Adjacent independent gates commute. Duplicate-input gates can be bypassed: a surviving proof support may shrink, but output correctness excludes a singleton support, so each originally witnessed edge retains a point-once witness; OR-count does not increase. This is bounded computational evidence only. Complete source and logs archived.

## 2026-11-25 13:01:36 UTC — math_bound

### Sharp one-sided reading budget (paper derivation, not Lean checked)
Existing requested file census: L2672/L3716 prove only N*q <= 32*size+3*N+|doubleReread|; L2466 bounds repeats by34*size under ReadK2; L3652/L3718 localize repeat edges to maximal cores; L3655 is an explicit fixed-point Fano repeat example. R4201_1 ASSUMES its exact OR>=104 single-read theorem and same-OR repeat elimination. Thus the following sharp one-sided claim appears new in this census: number of point-single target edges <= number of original OR gates+1.
For an exact incidence circuit, evaluate points=0 and lines=1 to classify each wire base0/base1. Base0 OR has two base0 children. A base0 AND either has exactly one base0 child, weighted by the other child's base function on lines, or has two base0 children and contributes zero to the degree-one point part. Keep the derivative-live zero-base DAG from output to r point leaves. If it has k binary OR nodes and a unary weighted AND nodes, its edge count <=2*k+a and vertex count=k+a+r, so reverse fanout summation needs at most k-r+1 OR gates. Base1 coefficient functions require at most the original base1 OR count. Reverse accumulation therefore computes r derivative row functions with OR count <=originalOR-r+1. Each row is false outside its genuine neighbor set, and singleton truth exactly means a point-single edge. MixedLinear's first-pure-merge counting extends from exact OR outputs to arbitrary row-pure outputs with known singleton supports, yielding edgecount-r<=reverseOR, hence edgecount<=originalOR+1. Constants0/1 introduced by reversal can be eliminated; constant1 cannot reach a point output because incidence is false on every point singleton. Formal obligations remain the DAG transposition/count and link to linearParts.
This does not yet count the union of point-single and line-single edges, nor the doubly reread edges. Separate application gives only factor2. General repeat elimination remains the full gap bottleneck. Matching CNF counterexamples show formal derivatives can miss all target edges.

2026-11-25T13:02:04.151752+00:00 proof_route: strengthened MixedLinear in-place, compiled pure2 exit0/empty logs. New pure_family_ao_bound_active only requires row outputs false on complement S_p and to accept selected singleton set U_p; proves sum card(U_p) ≤ OR-count + number active U rows. Exact linear_family_ao_cost retained as corollary. This covers nonlinear derivative outputs provided row purity; still no derivative construction/budget theorem. 489 lines; sha256 e340f135e4aef3a17e093b1b8717497b951b72c463589f9acd86f89c5ad24fd8.

## 2026-11-25T13:02:16.741866+00:00 — least normalized C6 stress test (read1_construction)

CaDiCaL returned UNSAT for exactly8gate C6 circuits satisfying equal below-output status on OR operands, neither AND operand below output, and no read1 proof for fixed edge(0,4). Only adjacent topological symmetry was used; graph automorphism symmetry was disabled. C6 is edge-transitive, so fixed edge is representative. Known optimal8 read1 circuit and explicit11gate normalized nonread1 circuit both returned SAT as positive controls; all CNF clauses,64truth-table entries, normalization constraints and capped read-vectors were independently verified. Counterexample agent independently reviewed encoding and controls, PASS. This is computational support for leastness-plus-normalization on C6 only, not a Lean proof or the general theorem. Complete scripts/CNF/solver logs archived in results/orch/searches/least-normalized-c6/.

Primary literature checked by root on 2026-11-25: Jukna ECCC TR05-021, https://eccc.weizmann.ac.il/report/2005/021/download/, Lemma11 identifies biclique-cover count with single-level AND count only. Theorem3 gives general AND-count separation for saturated matching extensions, which add edges inside the bipartition and do not refute our bipartite C4-free case. Thus unrestricted AND-count-to-biclique-cover conversion cannot be assumed from that result.

2026-11-25T13:03:49+00:00 normalization: EdgeElimination.lean compiled (exit 0), independently reviewed by read1_construction. Any gate of a least-size nonzero incidence circuit must accept some incident pair. An invisible gate is forced false without changing the function, then constant propagation deletes at least that gate while retaining binary AND/OR and reads-back. This eliminates gates used solely for higher-degree behavior but does not remove all dirty AND gates. Combined source 2bacb6ce80ea4005993c4c96b4b54fdde545e4a9177e4725c30d31a101d07b72; full logs results/orch/logs/edge-elimination.*.

## 2026-11-25 13:04:11 UTC — math_bound final distinctions

A proposed direct dirty-AND budget |doubleReread|<=number of nonbelow-output AND gates is FALSE even with full normalization. Substitute A=OR of d independent line inputs and B=OR of another d disjoint line inputs into the checked matching2 CNF: [(p OR q) AND (A OR B)] AND [(p OR B) AND (q OR A)]. It computes F=(p AND A) OR (q AND B), a C4-free union of two d-stars. Every interior wire remains nonbelow F and all gates are live. It has exactly two dirty AND gates (plus the clean root), but every one of the2d target edges rereads both its point and line. Thus repeated-edge payment must include shared OR work, not only dirty ANDs. This parametric extension is a mathematical calculation, not a separately Lean-checked artifact.
MixedLinear generalized489-line exact SHA e340f135e4aef3a17e093b1b8717497b951b72c463589f9acd86f89c5ad24fd8 independently delta-reviewed PASS. The general pure-family endpoint is sound. The remaining sharp one-sided derivative claim covers point-single and line-single separately; IsSingleRead is their UNION, so merely adding the bounds loses factor2 and gives no double-reread cost. No proof of the full step resulted from these routes.

## 2026-11-25T13:04:31.680777+00:00 — rejected dirty-AND-only charge

A proposed inequality number(double-reread edges) <= number(nonbelow-output AND gates) is false even under current strong normalization. math_bound gave matching2 CNF with its line variables replaced by disjoint2-leaf ORs: all4 target edges doubly reread but only2 dirty ANDs. Independently, the canonical C6 CNF has5 essential clauses (allpoints, alllines, complements of each of3 missing-diagonal pairs); its4-gate AND chain has3 dirty ANDs but all6edges doubly reread. All proper AND prefixes remain nonbelow output because each maximal-independent clause is essential. These are paper-level counterexamples to an auxiliary charge, not refutations of L2585. Any successful charge must account for the OR support costs too.

2026-11-25T13:04:40.218154+00:00 [counterexample] Point-single OR-bound census extended through6gates:2,036,784,434 canonical size6 circuits, exit0, no violation in either orientation for333 nonempty3x3 C4-free targets. Separate cheap scan verifies unrestricted edge-count<=OR-count+1 through5gates (39,999,763 size5circuits). Both are bounded computation, not Lean proofs. At proof_route request, now testing C6 with8total gates and<=4OR gates; fixed8gate/5OR positive control already SAT. PGq3 heuristic is paused temporarily to preserve4worker budget.

2026-11-25T13:05:14.413012+00:00 [counterexample] Targeted C6 OR-trade test finished:8total gates with<=4OR gates is UNSAT (Cadical exit20,4.72s CPU,10.28s wall), while fixed known8gate/5OR star circuit is SAT (exit10). This supports the unrestricted OR-count conjecture at optimal C6 size only; it does not prove it for larger circuits or graphs. Full generator,CNF,solution,status and diagnostic logs archived. PGq3 heuristic resumed; still exactly4 active search workers.

## Re-plan 2 — 2026-11-25T13:05:45.345485+00:00

All construction endpoints and core clean-case lemmas are checked. A stronger mixed-AO fixed-row counting theorem and least-circuit edge-observability normalization are now checked too. Stop routine construction variants. Cost extraction from repeated-read dirty blocks remains the exact missing step. Dirty-AND count alone cannot pay for double rereads: replacing line variables by disjoint ORs amplifies reread edges without adding dirty AND gates. Pair signatures also miss independent triples.

Computational stress tests support the minimum-size normalized route on C6 only; no full theorem follows. A fresh mathematical cost reviewer was added (total sub-agents now7). Four distinct search workers remain, at nice10: K5 SAT, cyclic8x8 SAT, projective-plane heuristic, variable-graph heuristic. Continue through at least90min total unless full proof/refutation appears; preserve checked partials and full search logs. Root renews the sole lease every5min.

2026-11-25T13:08:30+00:00 normalization: strengthened least-circuit invariant checked in EdgeEssential.lean (953 lines, SHA b6404f0ac73a359477058f01b873dc3d6c7375d0e5dcb2a0cc8573dbec0f2b00), independent read1_construction review PASS. Each gate of a least nonzero incidence circuit is output-essential on some incident pair: forcing it false destroys acceptance of that pair. If all pair positives survive, monotonicity plus offGate<=original preserve the full function, and checked cleanup strictly shrinks the circuit. This still does not imply the target read1 property; CNF matching constructions can be edge-essential. Full logs results/orch/logs/edge-essential.*.

2026-11-25T13:09:22.114167+00:00 [counterexample] Normalization agent proved every gate of a least incidence circuit accepts some target edge. Added optional --edge-active to semantic SAT variant; known K5 subdivision24gate star control with all pruning remains SAT exit10. Dynamic heuristic review found unconstrained graph evolution drifts to sparse cases, so old worker was interrupted130 (no witness) and replaced by dense8x8 evolution:40slots with9initially dead gates, at least20edges, only live-gate cost charged, full maximal-independent tests, every prospective hit fully checked on65536inputs. One-second smoke tests and full old logs archived; new30minute worker PID13263 started at nice10.

2026-11-25T13:12:55.743405+00:00

## Free-OR SAT independent review (status_review)

Reviewed free_or_and.py SHA256 d91b19bfff636931e55f5b8ab3a2887ca1eb2eb62edf12ecb938afc586c4d893 and verify_free_or.py SHA256 d84235b3821fe43766a59b799088557d4a3756b7270b0ad45e0cba8fec6570cb. PASS for the current n>=3 instances.

Each counted AND has two freely selected ORs of original inputs and earlier AND outputs. Collapsing maximal OR networks gives this form for every acyclic binary monotone circuit with at most k AND gates; unused zero gates pad smaller circuits. Omitting original inputs from the final OR is complete because the nonempty incidence target rejects every singleton. The dual vertex-cover target also rejects every singleton when the forced matching has size at least2. Thus n=1 dual cases are outside this completeness argument. Constants can be propagated away for these nonconstant targets; allowing zero padding only enlarges the search class.

Clause helpers implement exact signed-literal AND/OR equivalences, including empty OR=false and empty AND=true. Every input assignment is constrained. Dual mode targets AND over all edge endpoint-disjunctions, exactly the De Morgan dual of incidence, so counted ANDs correspond to original ORs. Diagonal edge units require a perfect matching; this is complete up to independent vertex relabeling for matching-saturated n-by-n graphs, not all n-by-n graphs. A general matching lower-bound counterexample can be restricted to endpoints of a maximum matching, but that restriction need not preserve its original edge count for an OR>=edges-1 claim. No extra operand/topological symmetry restrictions occur. The min-edges clause family correctly enforces its lower bound when the parameter is in range.

Re-ran the verifier with exit0 on matching4_k4, cycle3_k3, and dual cycle3_or5. It independently checks all DIMACS clauses and all256/64/64 input assignments, respectively; complete review logs are scratch fresh-cost/review-controls.stdout and review-controls.stderr. Existing cycle3_k2, cycle3_or4, and dynamic4_k3 logs contain solver UNSAT statuses. Those are solver outcomes only, with no proof certificate or Lean lower-bound proof claimed. Source map metadata currently omits fixed/min-edges CLI options, so preserve invocation details alongside CNF files when archiving.

2026-11-25T13:14:20.957020+00:00

## Semantic SAT and dynamic graph search review (status_review)

Read-only review PASS for synthesis_semantic.py SHA256 dc2c6adf073a15b9b302a4b786450805fbe50e2d4d37e9c8124d8e3219b634a7 and evolve_graph_slack.cpp SHA256 0eb1d1ca33881f046daf5b9bde6b17fb269b75dbdda57554b4e3a63ad40ed8fb. No credential/network access or command execution in these sources.

SAT clauses correctly select two distinct ordered earlier operands and exact AND/OR values on every edge and maximal independent input. Positive and maximal-independent tests are complete for the monotone target. Semantic source incomparability is valid for a minimum circuit: otherwise bypassing the gate preserves all tests and yields a smaller circuit. The edge-active condition similarly follows from zero-forcing and constant propagation in a minimum nonzero target circuit. No-unused-gates and distinct-input restrictions are also minimum-circuit conditions. Therefore an UNSAT instance at k gates excludes a minimum of exactly k, not every smaller size. Adjacent independent-gate sorting and first-gate automorphism orbit representatives are simultaneously justified by a globally lexicographically least equivalent circuit. Source verifies its automorphisms. Both fixed K5 24-gate control logs say SAT.

Dynamic search keeps valid acyclic40-gate genomes on16inputs; all wire indices fit the64-entry arrays and at most256 negative tests fit the four64-bit words. Inferred cross-pairs, pure-side rejection, C4 tests, maximal-independent closure tests, augmenting-path matching, and live-cone counting are consistent. A reported hit is additionally asserted against all65536 assignments. Keep compilation assertions enabled and preserve flags. Current dense20 smoke log completed with no witness. Positive savings against E+maximum_matching-1 would still require a matching READ1 lower bound and Lean verification before claiming refutation of the leased statement. No negative search outcome is a Lean proof.

## 2026-11-25T13:14:42.677427+00:00 — fresh-cost unrestricted single-operation budgets

A new complete finite model counts AND gates with the number of OR gates unrestricted: flatten each OR-only cone into an arbitrary subset of original inputs and earlier AND outputs. Exact truth is enforced on every assignment. CaDiCaL found UNSAT for every C4-free 4-by-4 target containing the fixed diagonal matching at at most 3 AND gates. By restricting a hypothetical violation to maximum-matching endpoints and padding disjoint edges when needed, this supports AND >= vertex-cover for all C4-free bipartite graphs with vertex-cover <= 4, regardless of total vertex count. This is external solver evidence, not a Lean proof.

The Boolean-dual variant found C6 impossible at <=4 OR gates with arbitrarily many AND gates (UNSAT); C6 at 5 OR gates is SAT. SAT controls for matching4 at 4 ANDs, C6 at 3 ANDs, and dual C6 at 5 ANDs were reconstructed and checked on all assignments and every CNF clause. status_review independently reviewed the encoding and controls, PASS. Dynamic 5-by-5 at 4 ANDs timed out after 120 seconds (UNKNOWN); no larger mathematical conclusion follows. A dynamic 4-by-4, >=8-edge dual instance was only generated and was never run.

Frozen exact scripts, CNFs, map files, full build/solver/verification logs, explicit invocations and SHA256 manifest are archived in results/orch/searches/free-or-count/. No final Lean file was touched. The missing general dirty-block star-cover budget remains unresolved.

Fresh primary-source check: Nets Hawk Katz, On the CNF-complexity of bipartite graphs containing no K2,2s, https://arxiv.org/pdf/1206.6068 (read 2026-11-25), constructs high-degree C4-free graphs with logarithmic-size graph CNF representations. These only agree with the graph on cross-pairs and may accept larger independent sets; hence they do not refute our exact-function claim. They do rule out importing a pair-only CNF-count heuristic as the missing cost argument.

2026-11-25T13:15:34.618392+00:00 [counterexample] C6 9gate/<=4OR SAT is UNSAT (exit20,48.30s CPU,94.31s wall); fixed9gate/5OR control SAT and fulltruth verified. Read public discussion12644: another agent already ran a much larger PG63 star-minus-one search, also without success and with failed70gate recovery control. Our PG baseline64gate is checked but higher-budget recovery was not stressed; retired our redundant PG worker exit130, no witness. Replaced its slot with30min K5-23 sym+orbit+semantic+edge-active exactSAT at nice10 (PID13917). Added independent SAT decoder with full-CNF/fulltruth/C4free/matching/livecone/squarefree-edge checks; known controls at64 and32768 assignments pass. Preserved dynamic exact compile argv/source+binary hashes, assertions enabled.

2026-11-25T13:15:45+00:00 normalization: LeastNormalizedBody.lean packages completed normalization: every valid circuit for a nonzero incidence function admits an equivalent globally least-size circuit no larger than the original, normalized OR below-output statuses, and each gate output-essential on some incident pair. Nat.find selects global minimum; existing normalization preserves exact size; edge-essentiality transfers. New 74-line body hash b1aa6f7480cb5c65e1f9f000fc4065648a95f661504d2b3fbddbeea98d8b3248 reviewed PASS by read1_construction; standalone combined LeastNormalized.lean compiled exit 0, hash 6b9f4f2b3eb46c0238dc11ddefca684746f2f3cc9324a8fe8aa26278f061d828. No C4 hypothesis needed and no read1/cost conclusion claimed. Logs results/orch/logs/least-normalized.*.
