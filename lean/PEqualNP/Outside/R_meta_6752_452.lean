import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_6752_452
    (connection : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C → (Ustar G C).Nonempty →
      (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty)
    (coreBound : let G := edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e : ℕ => (e/11,e%11))
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))),
      let J := junk G C
      let U := Ustar G C
      let H := gammaE G C
      C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ J.card → J.card + 2 ≤ U.card →
      T ⊆ U → (U \ T).card ≤ (J.filter fun g => Disjoint T (H g)).card →
      (∀ e ∈ U, ∃ g ∈ J, e ∈ H g) → (∀ g ∈ J, (T ∩ H g).card ≠ 1) →
      (∀ Z ⊆ T, Z.Nonempty → (∀ g ∈ J, Disjoint Z (H g) ∨ Disjoint (T \ Z) (H g)) →
        (J.filter fun g => ¬ Disjoint Z (H g)).card < Z.card) →
      U.card ≤ J.card + 2 * (centreless G C).card + (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → ∀ x9 ⊆ x7, x9.Nonempty → (x7 \ x9).card ≤ {x12 ∈ x6 | Disjoint x9 (PEqualNP.TopForm.gammaE x1 x2 x12)}.card → (∀ x13 ∈ x6, (x9 ∩ PEqualNP.TopForm.gammaE x1 x2 x13).card ≠ (1 : ℕ)) → (∀ x14 ∈ x7, ∃ x16 ∈ x6, x14 ∈ PEqualNP.TopForm.gammaE x1 x2 x16) → x9.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x9).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  intro G C size least top J U many X subX nonempty debt singles covered
  let H := gammaE G C
  let idle (S : Finset (Sym2 (Fin 11))) := J.filter fun g => Disjoint S (H g)
  let valid (S : Finset (Sym2 (Fin 11))) :=
    S ⊆ U ∧ (U \ S).card ≤ (idle S).card ∧ ∀ g ∈ J, (S ∩ H g).card ≠ 1
  have start : valid X := ⟨subX, debt, singles⟩
  have existsSize : ∃ k, ∃ S, valid S ∧ S.card = k := ⟨_, X, start, rfl⟩
  obtain ⟨T, hT, hsize⟩ := Nat.find_spec existsSize
  obtain ⟨subT, available, noSingle⟩ := hT
  have critical (Z : Finset (Sym2 (Fin 11))) (subZ : Z ⊆ T) (nz : Z.Nonempty)
      (closed : ∀ g ∈ J, Disjoint Z (H g) ∨ Disjoint (T \ Z) (H g)) :
      (J.filter fun g => ¬ Disjoint Z (H g)).card < Z.card := by
    by_contra! pay
    let A := J.filter fun g => ¬ Disjoint Z (H g)
    let R := T \ Z
    have dis : Disjoint (idle T) A := by
      apply Finset.disjoint_left.mpr
      intro g h b
      exact (Finset.mem_filter.mp b).2 ((Finset.mem_filter.mp h).2.mono_left subZ)
    have unionSub : idle T ∪ A ⊆ idle R := by
      intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · obtain ⟨hj,hd⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hj,hd.mono_left Finset.sdiff_subset⟩
      · obtain ⟨hj,hd⟩ := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hj,(closed g hj).resolve_left hd⟩
    have more := Finset.card_le_card unionSub
    rw [Finset.card_union_of_disjoint dis] at more
    have subR : R ⊆ U := Finset.sdiff_subset.trans subT
    have rcard : R.card + Z.card = T.card := Finset.card_sdiff_add_card_eq_card subZ
    have oldCard := Finset.card_sdiff_add_card_eq_card subT
    have newCard := Finset.card_sdiff_add_card_eq_card subR
    have enough : (U \ R).card ≤ (idle R).card := by
      change Z.card ≤ A.card at pay
      omega
    have stable : ∀ g ∈ J, (R ∩ H g).card ≠ 1 := by
      intro g hg
      rcases closed g hg with left | right
      · have eq : R ∩ H g = T ∩ H g := by
          ext e
          simp only [R, Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · exact fun h => ⟨h.1.1,h.2⟩
          · exact fun h => ⟨⟨h.1,fun hz => Finset.disjoint_left.mp left hz h.2⟩,h.2⟩
        rw [eq]
        exact noSingle g hg
      · rw [Finset.disjoint_iff_inter_eq_empty.mp right]
        decide
    have smaller := Nat.find_min' existsSize (show ∃ S, valid S ∧ S.card = R.card from
      ⟨R,⟨subR,enough,stable⟩,rfl⟩)
    have := Finset.card_pos.mpr nz
    omega
  have room : (U \ X).card ≤ J.card := le_trans debt (Finset.card_le_card (Finset.filter_subset _ _))
  have splitCard := Finset.card_sdiff_add_card_eq_card subX
  have global : U.card ≤ J.card + 2 * (centreless G C).card + (orN G C \ lam G C).card := by
    by_cases gap : J.card + 2 ≤ U.card
    · exact coreBound C T size least top many gap subT available covered noSingle critical
    · obtain left | right := connection G C least top (nonempty.mono subX)
      · have := Finset.card_pos.mpr left
        omega
      · have := Finset.card_pos.mpr right
        omega
  omega
