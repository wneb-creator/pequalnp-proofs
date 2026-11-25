# L-meta-2582 orchestration notes

Assigned by the HTTP410 recovery request at2026-11-25T18:31:31.195Z. Previous L-meta-4675 checkedpartials preserved in fork commit285d44b399c3bc41ecdf1c8514332b8739081571. This new step has no tCount condition and asks for size-nonincreasing read-2 normalization on projectiveplanes. Reductions are not open.

∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2

### lemma_search — canonical construction checked

`lemmas/Canonical.lean` compiled exit0 (1176lines), importing only PEqualNP.Defs. Full diagnostics `canonical2582-001.stdout/.stderr` in task scratch; only inherited source linter/deprecation warnings. No forbidden-format matches. Source frozen.

Namespace `PEqualNP.Outside.L_meta_2582_aux`. `canonical_cover` copies the checked L_meta_7684 construction/read1 certification into own namespace. `incidence_card` copies/adapts the edge-count proof from L_meta_2058. New final theorem `canonical_plane_read_one q N I hL` returns D with IsAO2, exact incidence function, size<=N*(q+2)-1, and IsReadK(N+N)D1. It needs only the posted per-line cardinality hL. Thus after the algebraic agent's READ1-to-READ2 bridge, the original normalization is proved whenever the supplied C has at least N*(q+2)-1 gates; the remaining case is strictly smaller circuits.

### Counterexample agent: finite READ2 search

The exact joint recurrence is encoded by nine bits for count pairs0..2, dropping larger counts that cannot decrease. A separate validator uses the literal cap3 recurrence from ReadK.lean and checks equality of retained vectors at every wire plus the full Boolean truth table. Fixed P4 sanity [(1,3,AND),(0,4,OR),(2,3,OR),(5,6,AND),(6,7,AND)] computes edges{(0,2),(0,3),(1,3)} with five gates and is not READ2 on(1,3): its only capped pair is(1,3). This only illustrates that D=C is not valid for every source; a smaller four-gate READ2 realization already exists. C6 eight-gate nonREAD2 query running120s, with no color constraints. No claim of a plane counterexample.

### Algebraic agent — generic READ monotonicity checked

`lemmas/ReadMono.lean` is frozen after Lean exit 0; its 183 lines import only `PEqualNP.Defs`. Full diagnostics `read-mono-002.stdout` and `read-mono-002.stderr` in task scratch are empty. The theorem `L_meta_2582_aux.ReadMono.isReadK_mono C n hkl h` proves `IsReadK n C k → IsReadK n C l` for `k ≤ l`, without assumptions on gate kinds, topology, or the function. It lifts every lower-cap vector to a higher-cap vector whose entrywise cap is the original. A successful lower-cap vector therefore remains successful at the larger threshold. This completes the READ1-to-READ2 adapter for the canonical star construction, not the missing comparison with a smaller source circuit.

A local minimality idea remains incomplete: if a clean block `U ∧ V` accepts only edge pairs incident with point `a`, and `U` accepts singleton `a`, replacing `U` by input `a` decreases the block on every input and preserves its accepted edge pairs. This can preserve the full graph function. Further cofactor simplification of `V` would remove repeated reads of `a`, but altering a shared `V` may damage other blocks; copying it may increase size. No global budget or normalization theorem follows yet.

C6 eight-gate nonREAD2 numerical search timed out after120.048s. No model, no infeasibility or minimality conclusion.

### Algebraic agent — clean-case normalization checked

`lemmas/CleanNormalize.lean` compiled exit 0 with only inherited source warnings; complete logs are `clean-normalize-003.stdout` and `.stderr`. It concatenates `CleanReuse.lean`, the existing `Canonical.lean` and `ReadMono.lean`, and `CleanNormalizeWrapper.txt`. All components are frozen. `CleanReuse.lean` is byte-identical to the old checked Reuse source after changing its namespace to `L_meta_2582_aux.CleanReuse`.

The new `split_vertex_cover` splits a finite set of point/line inputs into point and line covers with exactly the same total cardinality. `clean_read_two_normalize` then proves the full same-size READ2 conclusion for an arbitrary C4-free bipartite graph, assuming IsAO2, exact graph-function computation, and the explicit extra condition that every AND gate implies the final output function on every input. It combines the checked clean lower bound with the canonical cover construction and READ monotonicity. Projective-plane regularity is unnecessary for this conditional result. Dirty AND gates remain the unresolved case.

## Structural local rewriting (18:40 UTC, structural agent)

LocalRewrite.lean and LocalRewriteExplicit.lean both compiled exit0, Defs-only import. The explicit version is 465 lines, frozen, and is the preferred archival artifact. Stdout has only inherited if_pos/if_neg deprecation warnings; stderr empty. Generic wire-transfer and V1/V2 machinery was extracted from the already checked L_meta_2393 first493lines; no Outside import. Namespace PEqualNP.Outside.L_meta_2582.Rewrite.

erase_equivalent_gate removes a gate semantically equal to an earlier wire, preserving IsAO2 and the full function with size exactly one smaller. erase_repeated_input_gate specializes this to either AND or OR with input list[b,b]. hoist_clean_or_input gives direct properties of V2: delete the OR reader, redirect it to its other operand, reindex remaining gates, append OR(oldoutput,cleanwire), preserve total size and function, expose output/root OR and IsRedirect. Explicit output-validity and backward-read premises are present; nothing assumes a global normal form.

Global block extraction is already checked in L_meta_4543:1148: any nonempty graph AO2 circuit has a no-larger IsLeastAO+TopForm replacement, even minimizing Ustar among such circuits. L_meta_2393:3287 proves each nonoutput clean gate in least+TopForm has one OR reader which is clean. Thus the known OR-of-blocks part is reusable; a new proof of that global normalizer is unnecessary. Shared dirty wires inside multiple blocks remain uncontrolled. A per-block lower bound cannot simply be summed when dirty cones are shared.

ReadK2 only needs proof trees with each endpoint appearing≤2. The desk star-cover replacement route would give ReadK1 and is stronger than posted. An alternative would normalize blocks to products of at most two read1 factors, but no nonincreasing normalization theorem of this kind has been established. Existing L_meta_7344 has a factor3-plus-bad-prime-pair cost, and L_meta_7653 handles all ORs before all ANDs; neither closes the statement.

### Counterexample agent: checked local-normalization obstruction

ReadTwoLocalObstruction.lean compiled. Let U=a∨b, V=x∨y, W=a∨y, T=a∨V, K=U∧T, L=V∧W, output=K∧L. Seven gates compute ax∨ay∨by; the pair by has only capped proof counts(1,3), so the source is not READ2. All11 wire functions are pairwise distinct, hence no gate duplicates any wire or either of its inputs semantically. A four-gate READ2 equivalent is checked, so the source is not a minimizer. This refutes a local semantic-deduplication-only strategy; it is not a plane counterexample or refutation of L-meta-2582.

### Counterexample agent: final finite handoff

P4 seven-gate no-bypass query returned SAT2.842s. Circuit [(1,3,AND),(2,4,OR),(0,4,OR),(5,6,AND),(3,7,OR),(0,7,OR),(8,9,AND)] has no output-preserving operand bypass and is notREAD2 on(1,3), with exact cap3 vectors{(2,3),(3,3)}. It contains a semantic duplicate (wire9 equalswire6), so it does not combine distinctness with no-bypass. Structural agent’s matching19 CNF construction combines both, and numerical validation showed all285 gate-to-any-earlier-wire replacements changeoutput. Its exact19gates, all64truthinputs, jointcap3vectors, all25wirefunctions distinct, and explicit285bypass witnesses are reproducible with MatchingCNFValidation.py. Structural agent formalizing it. Neither graph is a projective plane; no global-optimality or2582refutation claim. No searches remain active, and no further queries planned.

## Matching CNF obstruction to local cleanup (structural/counterexample, 18:46 UTC)

MatchingLocalObstruction.lean compiled exit0 in about72seconds; stdout/stderr empty. It constructs a19gate monotone CNF for the three-edge matching on6inputs, proves the exact function on all64assignments, proves one prime pair has no READ2 proof, checks all25wire functions distinct, and checks all38 choices of replacing a gate by one of its own operands change the function. The replacement is represented by an AND[b,b] at the same index, so all later indices stay fixed. A5gate equivalent READ1 circuit is checked. This demonstrates that absence of duplicate wire functions and absence of local operand bypasses does not imply READ2. It does not refute L-meta-2582: matching is not a projective plane and a smaller READ1 circuit exists.

Counterexample agent additionally numerically verified all285 substitutions of any gate by any earlier wire change the function. MatchingAllBypasses.lean adds that stronger finite assertion; its compile is pending as of18:46. Original checked file remains frozen.
