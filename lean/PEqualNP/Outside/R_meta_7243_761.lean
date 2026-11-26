import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7243_761
    (cert : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (p l : Fin 7), (p = l ∨ p = l + 1 ∨ p = l + 3) → x1.eval (List.ofFn (fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) = true) ∧
    ∀ (a : Fin 7 → Bool), x1.eval (List.ofFn (Fin.addCases a (fun l : Fin 7 => decide (∀ p : Fin 7, a p = true → ¬ (p = l ∨ p = l + 1 ∨ p = l + 3))))) = false)
    (mono : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) → ∀ (u v : Fin 14 → Bool), (∀ i, u i = true → v i = true) → x1.eval (List.ofFn u) = true → x1.eval (List.ofFn v) = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) := by
  obtain ⟨C, size, gates, pos, neg⟩ := cert
  refine ⟨C, size, gates, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro on
    by_contra h
    let a := fun p : Fin 7 => x (Fin.castAdd 7 p)
    apply Bool.noConfusion ((neg a).symm.trans (mono C gates x _ (fun i => ?_) on))
    refine Fin.addCases (m := 7) (n := 7) (motive := fun j => x j = true → Fin.addCases a (fun l : Fin 7 => decide (∀ p : Fin 7, a p = true → ¬ (p = l ∨ p = l + 1 ∨ p = l + 3))) j = true) ?_ ?_ i
    · intro p hp
      simpa [a] using hp
    · intro l hl
      simp only [Fin.addCases_right, decide_eq_true_eq]
      intro p hp he
      exact h ⟨p, l, he, hp, hl⟩
  · rintro ⟨p, l, he, hp, hl⟩
    apply mono C gates _ x _ (pos p l he)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hp
    · exact hl
