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
