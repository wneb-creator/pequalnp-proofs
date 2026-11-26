import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8071_846
    (twoShape : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.junk x2 x4).card = (2 : ℕ) → (2 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ∨ ∃ (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), PEqualNP.TopForm.junk x2 x4 = {x9, x10} ∧ PEqualNP.EdgeOwnership.InCone x1 x4 x9 x10 ∧ PEqualNP.TopForm.centreless x2 x4 = ∅ ∧ PEqualNP.TopForm.readers x1 x4 x9 = {x10} ∧ PEqualNP.TopForm.readers x1 x4 x10 = {x11} ∧ PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4 = {x11} ∧ ∀ (x12 x13 : Fin x1), s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → PEqualNP.EdgeOwnership.gateVal x1 x4 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true)
    (twoLarge :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit), C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let J := junk G C
        let U := Ustar G C
        let B := 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card
        J.card = 2 →
        (∃ g h : ℕ, g ∈ J ∧ h ∈ J ∧ g ≠ h ∧ ¬InCone 11 C g h ∧ ¬InCone 11 C h g) →
        (∀ u v : Fin 11, s(u,v) ∈ U → ∃ g ∈ J, gateVal 11 C g (pairInput u v) = true) →
        5 ≤ U.card → B < 2 * U.card → U.card ≤ B)
    (many : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C short least top minimum incomparable covered three high
  let J := junk G C
  let U := Ustar G C
  let P := 2 * (centreless G C).card + (orN G C \ lam G C).card
  change U.card ≤ 2 * (centreless G C).card + J.card + (orN G C \ lam G C).card
  by_cases two : J.card = 2
  · by_cases large : 5 ≤ U.card
    · exact twoLarge C short least top two incomparable covered large high
    · have nonempty : G.edgeFinset.Nonempty := by decide +kernel
      rcases twoShape 11 G C nonempty least top two with charge |
        ⟨g,h,m, gh, cone, _, _, _, _, _⟩
      · change 2 ≤ P at charge
        omega
      · obtain ⟨a,b,ha,hb,ab,hN,hR⟩ := incomparable
        have contained : ({a,b} : Finset ℕ) ⊆ J := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          exact hx.elim (· ▸ ha) (· ▸ hb)
        have pairCard : ({a,b} : Finset ℕ).card = 2 := by simp [ab]
        have pairEq : ({a,b} : Finset ℕ) = J :=
          Finset.eq_of_subset_of_card_le contained (by omega)
        have gIn : g ∈ J := by
          change g ∈ junk G C
          rw [gh]
          exact Finset.mem_insert_self _ _
        have hIn : h ∈ J := by
          change h ∈ junk G C
          rw [gh]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have distinct : g ≠ h := by
          intro hEq
          subst h
          have gone : J = {g} := by
            change junk G C = {g}
            exact gh.trans (Finset.insert_eq_of_mem (Finset.mem_singleton_self g))
          rw [gone,Finset.card_singleton] at two
          omega
        have gOr : g = a ∨ g = b := by
          rw [← pairEq,Finset.mem_insert,Finset.mem_singleton] at gIn
          exact gIn
        have hOr : h = a ∨ h = b := by
          rw [← pairEq,Finset.mem_insert,Finset.mem_singleton] at hIn
          exact hIn
        rcases gOr with rfl | rfl <;> rcases hOr with rfl | rfl
        · exact (distinct rfl).elim
        · exact (hN cone).elim
        · exact (hR cone).elim
        · exact (distinct rfl).elim
  · have manyN : 3 ≤ J.card := by change 2 ≤ J.card at minimum; omega
    exact many C short least top manyN covered three high
