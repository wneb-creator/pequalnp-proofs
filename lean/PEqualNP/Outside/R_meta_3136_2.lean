import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3136_2
    (seedUnused : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      a ≤ 24 → b ≤ 24 →
      ((∀ g ∈ gs, 9 ∉ g.inputs) ∧ a ≠ 9 ∧ b ≠ 9) →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5))
    (seedUsed : ∀ (gs : List Gate) (a b : ℕ),
      gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      a ≤ 24 → b ≤ 24 →
      ((∃ g ∈ gs, 9 ∈ g.inputs) ∨ a = 9 ∨ b = 9) →
      ∃ x : Fin 9 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
        (w.getD a false && w.getD b false) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
      x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hlen hfan hnot ha hb
  by_cases h : (∀ g ∈ gs, 9 ∉ g.inputs) ∧ a ≠ 9 ∧ b ≠ 9
  · exact seedUnused gs a b hlen hfan hnot ha hb h
  · apply seedUsed gs a b hlen hfan hnot ha hb
    by_cases h1 : ∀ g ∈ gs, 9 ∉ g.inputs
    · right
      by_cases h2 : a = 9
      · exact Or.inl h2
      · exact Or.inr (by
          by_contra h3
          exact h ⟨h1, h2, h3⟩)
    · left
      push_neg at h1
      exact h1
