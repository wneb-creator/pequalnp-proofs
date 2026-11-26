import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3901_1
    (h0 : ∀ (g0 : Fin 24 × Fin 24 × Bool × Bool) (rest : List (Fin 24 × Fin 24 × Bool × Bool)),
      rest.length ≤ 12 → g0.1.val = 0 → g0.2.2.1 = false →
      (have p : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i;
       [g0.1.val, g0.2.1.val] ≤ [p g0.1.val, p g0.2.1.val]) →
      ∀ (x4 : Fin 24) (x5 : Bool), ∃ (x6 : Fin 512),
        have x7 : Fin 9 → Bool := fun x7 => (BitVec.ofNat 9 x6.val).getLsbD x7.val;
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 || x7 1, false];
        ((List.foldl (fun (x9 : List Bool) (x10 : Fin 24 × Fin 24 × Bool × Bool) =>
            x9 ++ [x9.getD x10.1.val false == x10.2.2.1 && x9.getD x10.2.1.val false == x10.2.2.2])
          x8 (g0 :: rest)).getD x4.val false != x5) ≠
        ([18440827511444797640, 18441957826578283724, 18446744073709222136,
          18446744073709485308, 18446744073708175304, 18446744073709551615,
          18446744073709223928, 18446744073709551615].getD (x6.val / 64) 0).testBit (x6.val % 64))
    (h14 : ∀ (g0 : Fin 24 × Fin 24 × Bool × Bool) (rest : List (Fin 24 × Fin 24 × Bool × Bool)),
      rest.length ≤ 12 → 1 ≤ g0.1.val → g0.1.val ≤ 4 → g0.2.2.1 = false →
      (have p : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i;
       [g0.1.val, g0.2.1.val] ≤ [p g0.1.val, p g0.2.1.val]) →
      ∀ (x4 : Fin 24) (x5 : Bool), ∃ (x6 : Fin 512),
        have x7 : Fin 9 → Bool := fun x7 => (BitVec.ofNat 9 x6.val).getLsbD x7.val;
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 || x7 1, false];
        ((List.foldl (fun (x9 : List Bool) (x10 : Fin 24 × Fin 24 × Bool × Bool) =>
            x9 ++ [x9.getD x10.1.val false == x10.2.2.1 && x9.getD x10.2.1.val false == x10.2.2.2])
          x8 (g0 :: rest)).getD x4.val false != x5) ≠
        ([18440827511444797640, 18441957826578283724, 18446744073709222136,
          18446744073709485308, 18446744073708175304, 18446744073709551615,
          18446744073709223928, 18446744073709551615].getD (x6.val / 64) 0).testBit (x6.val % 64))
    (h5 : ∀ (g0 : Fin 24 × Fin 24 × Bool × Bool) (rest : List (Fin 24 × Fin 24 × Bool × Bool)),
      rest.length ≤ 12 → 5 ≤ g0.1.val → g0.2.2.1 = false →
      (have p : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i;
       [g0.1.val, g0.2.1.val] ≤ [p g0.1.val, p g0.2.1.val]) →
      ∀ (x4 : Fin 24) (x5 : Bool), ∃ (x6 : Fin 512),
        have x7 : Fin 9 → Bool := fun x7 => (BitVec.ofNat 9 x6.val).getLsbD x7.val;
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 || x7 1, false];
        ((List.foldl (fun (x9 : List Bool) (x10 : Fin 24 × Fin 24 × Bool × Bool) =>
            x9 ++ [x9.getD x10.1.val false == x10.2.2.1 && x9.getD x10.2.1.val false == x10.2.2.2])
          x8 (g0 :: rest)).getD x4.val false != x5) ≠
        ([18440827511444797640, 18441957826578283724, 18446744073709222136,
          18446744073709485308, 18446744073708175304, 18446744073709551615,
          18446744073709223928, 18446744073709551615].getD (x6.val / 64) 0).testBit (x6.val % 64)) :
    ∀ (x1 : List (Fin 24 × Fin 24 × Bool × Bool)),
      x1.length ≤ 13 →
      (∀ x3 ∈ x1.head?.toList,
        x3.2.2.1 = false ∧
        have x5 : ℕ → ℕ := fun x5 => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD x5 x5;
        [x3.1.val, x3.2.1.val] ≤ [x5 x3.1.val, x5 x3.2.1.val]) →
      ∀ (x4 : Fin 24) (x5 : Bool), ∃ (x6 : Fin 512),
        have x7 : Fin 9 → Bool := fun x7 => (BitVec.ofNat 9 x6.val).getLsbD x7.val;
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 || x7 1, false];
        ((List.foldl (fun x9 x10 => x9 ++ [x9.getD x10.1.val false == x10.2.2.1 && x9.getD x10.2.1.val false == x10.2.2.2])
          x8 x1).getD x4.val false != x5) ≠
        ([18440827511444797640, 18441957826578283724, 18446744073709222136,
          18446744073709485308, 18446744073708175304, 18446744073709551615,
          18446744073709223928, 18446744073709551615].getD (x6.val / 64) 0).testBit (x6.val % 64) := by
  intro x1 hlen hhead x4 x5
  cases x1 with
  | nil =>
    have hnil : ∀ (a : Fin 24) (b : Bool), ∃ (x6 : Fin 512),
        have x7 : Fin 9 → Bool := fun x7 => (BitVec.ofNat 9 x6.val).getLsbD x7.val;
        have x8 : List Bool := List.ofFn x7 ++ [x7 0 || x7 1, false];
        (x8.getD a.val false != b) ≠
        ([18440827511444797640, 18441957826578283724, 18446744073709222136,
          18446744073709485308, 18446744073708175304, 18446744073709551615,
          18446744073709223928, 18446744073709551615].getD (x6.val / 64) 0).testBit (x6.val % 64) := by
      intro a b
      fin_cases a <;> cases b <;>
        first | refine ⟨0, by dsimp; decide⟩ | refine ⟨3, by dsimp; decide⟩ | refine ⟨12, by dsimp; decide⟩
    exact hnil x4 x5
  | cons g0 rest =>
    have hrest : rest.length ≤ 12 := by simp only [List.length_cons] at hlen; omega
    have hg0 := hhead g0 (by simp)
    rcases Nat.lt_or_ge g0.1.val 1 with ha0 | ha1
    · exact h0 g0 rest hrest (by omega) hg0.1 hg0.2 x4 x5
    · rcases Nat.lt_or_ge g0.1.val 5 with ha14 | ha5
      · exact h14 g0 rest hrest ha1 (by omega) hg0.1 hg0.2 x4 x5
      · exact h5 g0 rest hrest ha5 hg0.1 hg0.2 x4 x5
