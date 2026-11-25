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
