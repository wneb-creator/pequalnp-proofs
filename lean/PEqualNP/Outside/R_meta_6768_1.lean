import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_6768_1
    (h1 : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        16 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C \ centreless G C).card) ∧
        ((Ustar G C).Nonempty → 1 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card))
    (h2 : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card = 2 → C.size ≤ 21 →
        2 * (centreless G C).card + (orN G C \ lam G C).card = 1 → 2 ≤ (Ustar G C).card →
        16 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C \ centreless G C).card) →
        (∀ v : Fin 11, v.val < 4 → (∀ j < C.size, v.val ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧ ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → v.val ∉ (gateAt C k).inputs) →
        False)
    (h3 : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card = 2 → C.size ≤ 21 →
        2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        3 ≤ (Ustar G C).card →
        16 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C \ centreless G C).card) →
        (∀ v : Fin 11, v.val < 4 → (∀ j < C.size, v.val ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧ ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → v.val ∉ (gateAt C k).inputs) →
        False)
    (h4 : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card → C.size ≤ 21 →
        1 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        3 ≤ (Ustar G C).card →
        16 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
        (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) K → K.card ≤ (tops G C \ centreless G C).card) →
        (∀ v : Fin 11, v.val < 4 → (∀ j < C.size, v.val ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧ ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → v.val ∉ (gateAt C k).inputs) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → (∀ x10 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x10 x11 x12 : ℕ), x10 < x11 → x11 < x12 → x12 < x2.size → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) := by
  intro x1 C hL hT hJ hS hB hSp
  exfalso
  obtain ⟨hLed, hCov, hNE⟩ := h1 C hL hT
  have hU2 : 2 ≤ (Ustar x1 C).card := by omega
  have hUne : (Ustar x1 C).Nonempty := Finset.card_pos.mp (by omega)
  have hPos : 1 ≤ 2 * (centreless x1 C).card + (orN x1 C \ lam x1 C).card := hNE hUne
  by_cases hj2 : (junk x1 C).card = 2
  · by_cases hcr : 2 * (centreless x1 C).card + (orN x1 C \ lam x1 C).card = 1
    · exact h2 C hL hT hj2 hS hcr hU2 hLed hCov hSp
    · have hcr2 : 2 ≤ 2 * (centreless x1 C).card + (orN x1 C \ lam x1 C).card := by omega
      have hU3 : 3 ≤ (Ustar x1 C).card := by omega
      exact h3 C hL hT hj2 hS hcr2 hB hU3 hLed hCov hSp
  · have hj3 : 3 ≤ (junk x1 C).card := by omega
    have hU3 : 3 ≤ (Ustar x1 C).card := by omega
    exact h4 C hL hT hj3 hS hPos hB hU3 hLed hCov hSp
