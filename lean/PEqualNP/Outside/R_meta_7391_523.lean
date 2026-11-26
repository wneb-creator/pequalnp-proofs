import PEqualNP.Defs

-- Normalize: a fan-in-two circuit for the Petersen edge function (edge ab written as 10a+b) can be
-- rewritten, without growing and without losing a NOT gate unless it shrinks, into a strict
-- circuit with the output last, no dead gate, no NOT reading a NOT and no two equal gates.
-- The bound is then needed only for such circuits.
theorem PEqualNP.Outside.R_meta_7391_523
    (normalize :
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
      let tidy := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
        PEqualNP.MinimumComplex.Strict 10 D ∧ D.output + 1 = 10 + D.size ∧
          (∀ j < D.size - 1, ∃ g ∈ D.gates, 10 + j ∈ g.inputs) ∧
          (∀ k (hk : k < D.gates.length), D.gates[k].op = .not →
            ∀ g ∈ D.gates, g.op = .not → 10 + k ∉ g.inputs) ∧
          D.gates.Pairwise fun g h => g.op = h.op → ¬ g.inputs.Perm h.inputs
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, tidy D ∧ D.size ≤ C.size ∧
          ((∃ g ∈ C.gates, g.op = .not) → (∃ g ∈ D.gates, g.op = .not) ∨ D.size < C.size) ∧
          ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x)
    (bound :
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10))
      let tidy := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
        PEqualNP.MinimumComplex.Strict 10 D ∧ D.output + 1 = 10 + D.size ∧
          (∀ j < D.size - 1, ∃ g ∈ D.gates, 10 + j ∈ g.inputs) ∧
          (∀ k (hk : k < D.gates.length), D.gates[k].op = .not →
            ∀ g ∈ D.gates, g.op = .not → 10 + k ∉ g.inputs) ∧
          D.gates.Pairwise fun g h => g.op = h.op → ¬ g.inputs.Perm h.inputs
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, tidy D → D.size ≤ 19 →
        (D.size < 19 ∨ ∃ g ∈ D.gates, g.op = .not) →
        ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (10 : ℕ)) && x2 (1 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (2 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (3 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (4 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (0 : Fin (10 : ℕ)) || x2 (0 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (5 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (7 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (9 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (6 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (8 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x3 : ℕ),     have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.getD x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };     (∀ x5 ∈ x4.inputs, x5 < (10 : ℕ) + x3) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length ≤ (1 : ℕ)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (19 : ℕ) → x3.output + (1 : ℕ) = (10 : ℕ) + x3.size → x2 x3 → (x3.size < (19 : ℕ) ∨ ∃ x8 ∈ x3.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬x1 x3) := by
  intro x1 x2 C fan small _ _ budget correct
  have same : ∀ x : Fin 10 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) =
      [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10)) := by
    intro x
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have correct' : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any
        fun n => x (Fin.ofNat 10 (n / 10)) && x (Fin.ofNat 10 (n % 10)) :=
    fun x => (correct x).trans (same x)
  obtain ⟨D, tidyD, shrink, keepNot, correctD⟩ := normalize C fan correct'
  refine bound D tidyD (shrink.trans small) ?_ correctD
  rcases budget with lt | hasNot
  · exact Or.inl (lt_of_le_of_lt shrink lt)
  · rcases keepNot hasNot with dNot | dLt
    · exact Or.inr dNot
    · exact Or.inl (lt_of_lt_of_le dLt small)
