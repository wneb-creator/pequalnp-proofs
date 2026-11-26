import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_8069_859
    (single :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        centreless G C = ∅ → (orN G C \ lam G C).card ≤ 1 → (Ustar G C).card ≤ 2)
    (centre :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        2 ≤ (junk G C).card →
        (∃ a b, a ∈ junk G C ∧ b ∈ junk G C ∧ a ≠ b ∧
          (InCone 11 C a b ∨ InCone 11 C b a)) →
        (∀ u v, s(u, v) ∈ Ustar G C → ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true) →
        let U := (Ustar G C).card
        let D := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        3 ≤ U → D < 2 * U →
        (centreless G C).Nonempty → (orN G C \ lam G C).card ≤ 1 → U ≤ D)
    (multiple :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        2 ≤ (junk G C).card →
        (∃ a b, a ∈ junk G C ∧ b ∈ junk G C ∧ a ≠ b ∧
          (InCone 11 C a b ∨ InCone 11 C b a)) →
        (∀ u v, s(u, v) ∈ Ustar G C → ∃ j ∈ junk G C, gateVal 11 C j (pairInput u v) = true) →
        let U := (Ustar G C).card
        let D := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        3 ≤ U → D < 2 * U →
        2 ≤ (orN G C \ lam G C).card → U ≤ D) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C sz least top hjunk nested cover hU budget
  by_cases many : 2 ≤ (orN G C \ lam G C).card
  · exact multiple C sz least top hjunk nested cover hU budget many
  have few : (orN G C \ lam G C).card ≤ 1 := by omega
  by_cases noCentre : centreless G C = ∅
  · have h : (Ustar G C).card ≤ 2 := single C least top noCentre few
    exact (Nat.not_le_of_gt (by decide : 2 < 3) (hU.trans h)).elim
  · exact centre C sz least top hjunk nested cover hU budget
      (Finset.nonempty_iff_ne_empty.mpr noCentre) few
