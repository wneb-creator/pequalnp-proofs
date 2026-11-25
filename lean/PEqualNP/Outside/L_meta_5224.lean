import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5224

open PEqualNP.CircuitLowerBounds

private def reads (gs : List Gate) : List Nat :=
  gs.flatMap fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2)

private lemma reads_short (gs : List Gate)
    (h : ¬ ∃ g : Gate, gs[1]? = some g) : (reads gs).length ≤ 2 := by
  cases gs with
  | nil => decide
  | cons g tail =>
    cases tail with
    | nil =>
      simp only [reads, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_take]
      cases g.op.eval [false] <;> exact (Nat.min_le_left _ _).trans (by decide)
    | cons g' rest => exact False.elim (h ⟨g', rfl⟩)

theorem incompatible (C : Circuit)
    (cover : ∀ k < 10 + C.size, k ≠ C.output → k ∈ reads C.gates)
    (short : ¬ ∃ g : Gate, C.gates[1]? = some g) : False := by
  have inside : Finset.range 4 ⊆ insert C.output (reads C.gates).toFinset := by
    intro k hk
    have small : k < 4 := Finset.mem_range.mp hk
    by_cases hout : k = C.output
    · exact hout ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (cover k (by omega) hout))
  have lower := Finset.card_le_card inside
  rw [Finset.card_range] at lower
  have upper := Finset.card_insert_le C.output (reads C.gates).toFinset
  have distinct := List.toFinset_card_le (reads C.gates)
  have bound := reads_short C.gates short
  omega

end PEqualNP.Outside.L_meta_5224

theorem PEqualNP.Outside.L_meta_5224 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) →       (have x5 : List ℕ := List.flatMap (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs) x2.gates;         (∀ x6 < (10 : ℕ) + x2.size, x6 ≠ x2.output → x6 ∈ x5) ∧ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x2.gates).length + (x5.length - x5.toFinset.card) ≤ (5 : ℕ)) →         (∀ (x6 : Fin (9 : ℕ)) (x7 : Fin (10 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) → x6 ≠ (2 : Fin (9 : ℕ)) → x6.castSucc ≠ x7 → ∀ x11 ∈ x2.gates, x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11.inputs = [↑x6, ↑x7] ∨ x11.inputs = [↑x7, ↑x6] → (2 : ℕ) ≤ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x6) x2.gates).length) → (¬∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[(1 : ℕ)]? = Option.some x7) → (15 : ℕ) ≤ x2.size := by
  dsimp only
  intro C _ _ coverage _ noSecond
  exact (PEqualNP.Outside.L_meta_5224.incompatible C coverage.1 noSecond).elim
