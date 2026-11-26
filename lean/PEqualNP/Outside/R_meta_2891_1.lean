import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2891_1
    (normalize : ∀ C : Circuit, FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output < 10 + D.size ∧
        (∀ (j : Nat) (g : Gate), D.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j) ∧
        ∀ x : List Bool, x.length = 9 → D.eval (x ++ [false]) = C.eval x)
    (finiteBound : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 12 ∧ D.output < 10 + D.size ∧
      (∀ (j : Nat) (g : Gate), D.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j) ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x ++ [!x 1, false]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
         x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (1 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  rintro ⟨C, hFan, hSize, hEval⟩
  obtain ⟨D, hDFan, hDSize, hOut, hWires, hDEval⟩ := normalize C hFan
  apply finiteBound
  refine ⟨D, hDFan, hDSize.trans_le hSize, hOut, hWires, ?_⟩
  intro x
  have hLen : (List.ofFn x ++ [!x 1]).length = 9 := by simp
  simpa only [List.append_assoc, List.singleton_append] using (hDEval _ hLen).trans (hEval x)
