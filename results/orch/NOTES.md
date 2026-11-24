Orchestration notes for L-meta-3787

Lease acquired 2026-11-24T17:58:44.932Z; only root operates desk.
Initial expiry 2026-11-24T18:18:44.932Z; renew every ten minutes.
Upstream base e55b260. Allowed project module PEqualNP.Defs.
Goal: embed a 21-input monotone circuit into 26 inputs, append 20 gates for four degree-4 point stars and OR with old output.
Proof artifacts must end in the single assigned file. Helpers use module namespace.

Assigned statement:

∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (21 : ℕ) + x1.size →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x4 ∧           x4.size ≤ x1.size + (20 : ℕ) ∧             have x5 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];             have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);             have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x4.eval (List.ofFn (x6 x8 x9)) = Bool.true ↔ x1.eval (List.map (x6 x8 x9) x5) = Bool.true ∨ ∃ x10 ∈ x8, ↑x10 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x11 ∈ x9, x7 x10 x11

Embedding strategy: adapted generic relational-fold input reindexing from checked L_meta_574 lines 1043–1113. Source ready at lemmas/Embedding.lean, awaiting toolchain. Namespace PEqualNP.Outside.L_meta_3787.Embedding. Main interface embed, embed_size, embed_monotone, embed_valid, embed_eval with selection list.

Reviewer 2026-11-24: current own-namespace rule requires helpers in the file namespace or its subnamespace, with the fully qualified theorem top-level and last. Offline format check: node .github/scripts/outside-guard.mjs imports <file> <imports.json> lean/PEqualNP/Outside/L_meta_3787.lean check. The imports JSON is ["PEqualNP.Defs"]. Embedding relabel math reviewed: its relation covers all Nat wire indices, including forward and out-of-range refs returning false, and does not assume wellformed gates. Appending must preserve an old output known valid before suffix gates are added.

Finite semantics: stars p=0->[13,14,16,22], p=1->[13,15,21,25], p=3->[13,19,23,24], p=9->[13,17,18,20]. Draft written results/orch/lemmas/FiniteSemantics.lean; awaiting Lean cache.

AppendStars strategy: 5-gate block per point (three OR gates for four neighbor lines, one AND point, one OR accumulated output). Neighbor wires: 0:[13,14,16,22], 1:[13,15,21,25], 3:[13,19,23,24], 9:[13,17,18,20]. Draft helpers in results/orch/lemmas/AppendStars.lean. Final interface addStars_size, addStars_monotone, addStars_eval with RHS old eval || starExpr. Draft pending Lean toolchain/cache.

Embedding diagnostic: 2000 random 21-to-26 input remappings passed, including empty/unary/binary monotone gates, forward references, and out-of-range outputs (seed 3787). Full Lean verification still pending cache. Original valid-output hypothesis is only required to ensure suffix append preserves old output.

2026-11-24T18:06:58.841650+00:00 FiniteSemantics Mathlib-only scratch compile passed (exit 0, empty diagnostics). Full source differs only additional import PEqualNP.Defs. fsMembership and fsSemantics proven; explicit change resolves Fin.ofNat cast simplification.

2026-11-24T18:07:04.381297+00:00 Embedding.lean COMPILED successfully with Lean 4.36.0, exit 0 and no diagnostics. All 136 lines accepted. Interfaces embed_size/embed_monotone/embed_valid/embed_eval ready to integrate.
