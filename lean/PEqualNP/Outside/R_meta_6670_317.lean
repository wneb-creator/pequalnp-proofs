import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6670_317
    (h1 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ ((∀ x2 : Fin 14 → Bool, x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ∀ a b : Fin 7, b ≠ 1 → (a = b ∨ a = b + 1 ∨ a = b + 3) → x1.eval (List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 a ∨ i = Fin.natAdd 7 b))) = true))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C → ∀ x y : Fin 14 → Bool, (∀ i, x i = true → y i = true) → C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true) : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), (x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ((∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x4 ≠ (1 : Fin (7 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → x1.eval (List.ofFn x2) = Bool.true) := by
  obtain ⟨C, size, ao, nd, lo, hi, sound, tests⟩ := h1
  refine ⟨C, size, ao, nd, lo, hi, fun x => ⟨sound x, ?_⟩⟩
  rintro ⟨a, b, hb, edge, ha', hb'⟩
  apply h2 C ao _ x _ (tests a b hb edge)
  intro i h
  change decide (_ ∨ _) = true at h
  rcases of_decide_eq_true h with h | h
  · exact h ▸ ha'
  · exact h ▸ hb'
