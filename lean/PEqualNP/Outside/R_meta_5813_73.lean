import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5813_73
    (hFull :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin 13) (x4 : Bool),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 x1 →
        2 ≤ PEqualNP.TopForm.andPairs 27 x1 →
        have x8 : Finset (Fin 13) := {0, 1, 3, 9};
        have x9 : Finset (Fin 13) → Finset (Fin 13) → List Bool :=
          fun a b => (List.ofFn (fun i => decide (i ∈ a)) ++ List.ofFn (fun i => decide (i ∈ b))) ++ [x4];
        (∀ a b : Fin 13, a - b ∈ x8 → a ≠ x2 ∨ b ≠ x3 → x1.eval (x9 {a} {b}) = true) →
        (∀ q : Finset (Fin 13), q.card = 4 → (∀ k : Fin 13, {p ∈ q | p - k ∈ x8}.card ≤ 2) →
          x1.eval (x9 q {l : Fin 13 | ∀ p ∈ q, p - l ∉ x8}) = false) →
        (∀ a b c d : Fin 13, a - c ∉ x8 → a - d ∉ x8 → b - c ∉ x8 → b - d ∉ x8 →
          x1.eval (x9 {a, b} {c, d}) = false) →
        x1.eval (x9 {x2} {x3}) = true →
        63 ≤ x1.size)
    (hPunctTwo :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin 13) (x4 : Bool),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 x1 →
        PEqualNP.TopForm.andPairs 27 x1 = 2 →
        have x8 : Finset (Fin 13) := {0, 1, 3, 9};
        have x9 : Finset (Fin 13) → Finset (Fin 13) → List Bool :=
          fun a b => (List.ofFn (fun i => decide (i ∈ a)) ++ List.ofFn (fun i => decide (i ∈ b))) ++ [x4];
        (∀ a b : Fin 13, a - b ∈ x8 → a ≠ x2 ∨ b ≠ x3 → x1.eval (x9 {a} {b}) = true) →
        (∀ q : Finset (Fin 13), q.card = 4 → (∀ k : Fin 13, {p ∈ q | p - k ∈ x8}.card ≤ 2) →
          x1.eval (x9 q {l : Fin 13 | ∀ p ∈ q, p - l ∉ x8}) = false) →
        (∀ a b c d : Fin 13, a - c ∉ x8 → a - d ∉ x8 → b - c ∉ x8 → b - d ∉ x8 →
          x1.eval (x9 {a, b} {c, d}) = false) →
        x1.eval (x9 {x2} {x3}) = false →
        63 ≤ x1.size)
    (hPunctMany :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin 13) (x4 : Bool),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 x1 →
        3 ≤ PEqualNP.TopForm.andPairs 27 x1 →
        have x8 : Finset (Fin 13) := {0, 1, 3, 9};
        have x9 : Finset (Fin 13) → Finset (Fin 13) → List Bool :=
          fun a b => (List.ofFn (fun i => decide (i ∈ a)) ++ List.ofFn (fun i => decide (i ∈ b))) ++ [x4];
        (∀ a b : Fin 13, a - b ∈ x8 → a ≠ x2 ∨ b ≠ x3 → x1.eval (x9 {a} {b}) = true) →
        (∀ q : Finset (Fin 13), q.card = 4 → (∀ k : Fin 13, {p ∈ q | p - k ∈ x8}.card ≤ 2) →
          x1.eval (x9 q {l : Fin 13 | ∀ p ∈ q, p - l ∉ x8}) = false) →
        (∀ a b c d : Fin 13, a - c ∉ x8 → a - d ∉ x8 → b - c ∉ x8 → b - d ∉ x8 →
          x1.eval (x9 {a, b} {c, d}) = false) →
        x1.eval (x9 {x2} {x3}) = false →
        63 ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size) := by
  intro C r s b hm hr hap D X hpos hquad hrect
  cases hpt : C.eval (X {r} {s})
  · cases Nat.eq_or_lt_of_le hap with
    | inl h2 => exact hPunctTwo C r s b hm hr h2.symm hpos hquad hrect hpt
    | inr h3 => exact hPunctMany C r s b hm hr h3 hpos hquad hrect hpt
  · exact hFull C r s b hm hr hap hpos hquad hrect hpt
