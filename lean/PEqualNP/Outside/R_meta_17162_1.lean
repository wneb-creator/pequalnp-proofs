import PEqualNP.Defs

-- The exceptional neighbourhood pattern can occur only at width three.
-- The bounded-width step therefore retains the exclusion; the general
-- step starts at width four and needs no exceptional-pattern condition.
theorem PEqualNP.Outside.R_meta_17162_1
    (hNarrow :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        n ≤ 3 →
        ¬(n = 3 ∧ ∀ a : Fin n, ∃ b : Fin m,
          ∀ u : Fin n, (u, b) ∈ E ↔ u ≠ a) →
        let support := fun F : Finset (Fin n × Fin m) =>
          F.biUnion fun e => {Fin.castAdd m e.1, Fin.natAdd n e.2}
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ z : Fin (n + m) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C z =
            Decidable.decide (∃ e ∈ E,
              z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)) →
        (¬∃ (A B : Finset (Fin n × Fin m)) (v : Fin (n + m)),
          A.Nonempty ∧ A ∪ B = E ∧ Disjoint (support A) (support B) ∧
            ∀ e ∈ A, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
        ∃ (X : Finset (Fin n)) (Y : Finset (Fin m)),
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧ E.card + X.card + Y.card ≤ C.size + 1)
    (hWide :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        3 < n →
        let support := fun F : Finset (Fin n × Fin m) =>
          F.biUnion fun e => {Fin.castAdd m e.1, Fin.natAdd n e.2}
        (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ z : Fin (n + m) → Bool,
          PEqualNP.MetaComplexity.circuitFun (n + m) C z =
            Decidable.decide (∃ e ∈ E,
              z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)) →
        (¬∃ (A B : Finset (Fin n × Fin m)) (v : Fin (n + m)),
          A.Nonempty ∧ A ∪ B = E ∧ Disjoint (support A) (support B) ∧
            ∀ e ∈ A, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
        ∃ (X : Finset (Fin n)) (Y : Finset (Fin m)),
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧ E.card + X.card + Y.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   ¬(x1 = (3 : ℕ) ∧ ∀ (x6 : Fin x1), ∃ (x7 : Fin x2), ∀ (x8 : Fin x1), (x8, x7) ∈ x3 ↔ x8 ≠ x6) → (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x9 = Decidable.decide (∃ x10 ∈ x3, x9 (Fin.castAdd x2 x10.1) = Bool.true ∧ x9 (Fin.natAdd x1 x10.2) = Bool.true)) → (¬∃ (x10 : Finset (Fin x1 × Fin x2)) (x11 : Finset (Fin x1 × Fin x2)) (x12 : Fin (x1 + x2)), x10.Nonempty ∧ x10 ∪ x11 = x3 ∧ Disjoint (x5 x10) (x5 x11) ∧ ∀ x13 ∈ x10, Fin.castAdd x2 x13.1 = x12 ∨ Fin.natAdd x1 x13.2 = x12) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C support hExceptional hC4 hAO hFun hNoStar
  -- The equality case stays with the bounded-width step.
  rcases le_or_gt n 3 with hSmall | hLarge
  · exact hNarrow n m E C hSmall hExceptional hC4 hAO hFun hNoStar
  · exact hWide n m E C hLarge hC4 hAO hFun hNoStar
