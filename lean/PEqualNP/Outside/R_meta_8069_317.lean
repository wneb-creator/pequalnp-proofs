import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
theorem PEqualNP.Outside.R_meta_8069_317
  (pairCore : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      let J := junk G C
      let P := 2*(centreless G C).card + (orN G C \ lam G C).card
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → InCone 11 C a b →
      let K := (J.erase a).erase b
      let H := fun S : Finset ℕ => U ∩ S.biUnion (gammaE G C)
      let V := U \ H K
      (H K).card ≤ K.card → P + 3 ≤ V.card →
      V ⊆ gammaE G C a ∪ gammaE G C b →
      V.card ≤ P + (J.card - (H K).card))
  (expandingCore : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      let J := junk G C
      let P := 2*(centreless G C).card + (orN G C \ lam G C).card
      ∀ a ∈ J, ∀ b ∈ J, a ≠ b → InCone 11 C a b →
      let K := (J.erase a).erase b
      let H := fun S : Finset ℕ => U ∩ S.biUnion (gammaE G C)
      ∀ D ⊆ K, let V := U \ H D
        (K \ D).Nonempty → (H D).card ≤ D.card → P + 3 ≤ V.card →
        V ⊆ (J \ D).biUnion (gammaE G C) →
        (∀ S ⊆ K \ D, S.Nonempty → S.card < (V ∩ S.biUnion (gammaE G C)).card) →
        V.card ≤ P + (J.card - (H D).card)) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  classical
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  intro _ C hs hl ht _ hn hc _ _
  let U := Ustar G C
  let J := junk G C
  let P := 2*(centreless G C).card + (orN G C \ lam G C).card
  suffices U.card ≤ P + J.card by
    change U.card ≤ 2*(centreless G C).card + J.card + (orN G C \ lam G C).card
    change U.card ≤ (2*(centreless G C).card + (orN G C \ lam G C).card) + J.card at this
    omega
  have nested : ∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ InCone 11 C a b := by
    obtain ⟨a,b,ha,hb,ne,ab|ba⟩ := hn
    · exact ⟨a,ha,b,hb,ne,ab⟩
    · exact ⟨b,hb,a,ha,ne.symm,ba⟩
  obtain ⟨a,ha,b,hb,ne,ab⟩ := nested
  let K := (J.erase a).erase b
  let H := fun S : Finset ℕ => U ∩ S.biUnion (gammaE G C)
  let choices := K.powerset.filter (fun D => (H D).card ≤ D.card)
  have empty : ∅ ∈ choices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
    change (U ∩ (∅ : Finset ℕ).biUnion (gammaE G C)).card ≤ (∅ : Finset ℕ).card
    rw [Finset.biUnion_empty, Finset.inter_empty]
    exact le_rfl
  obtain ⟨D,hD,hmax⟩ := Finset.exists_max_image choices Finset.card ⟨∅,empty⟩
  obtain ⟨hDK,paid⟩ := Finset.mem_filter.mp hD
  have sub : D ⊆ K := Finset.mem_powerset.mp hDK
  let V := U \ H D
  have apart : (H D).card + V.card = U.card := by
    have Q := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : H D ⊆ U)
    change V.card + (H D).card = U.card at Q
    omega
  have capacity : D.card + 2 ≤ J.card := by
    have r := Finset.card_le_card sub
    have rb := Finset.card_erase_add_one (s := J.erase a) (Finset.mem_erase.mpr ⟨ne.symm,hb⟩)
    have ra := Finset.card_erase_add_one ha
    change D.card ≤ ((J.erase a).erase b).card at r
    omega
  by_cases small : V.card ≤ P + 2
  · omega
  have big : P + 3 ≤ V.card := by omega
  have covers : ∀ e ∈ U, ∃ j ∈ J, e ∈ gammaE G C j := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro h
      obtain ⟨j,hj,hval⟩ := hc u v h
      exact ⟨j,hj,Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1,u,v,rfl,hval⟩⟩
  have remCov : V ⊆ (J \ D).biUnion (gammaE G C) := by
    intro e he
    obtain ⟨hu,notHit⟩ := Finset.mem_sdiff.mp he
    obtain ⟨j,hj,hit⟩ := covers e hu
    have hjD : j ∉ D := fun h => notHit (Finset.mem_inter.mpr ⟨hu,Finset.mem_biUnion.mpr ⟨j,h,hit⟩⟩)
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_sdiff.mpr ⟨hj,hjD⟩,hit⟩
  suffices V.card ≤ P + (J.card - (H D).card) by omega
  by_cases terminal : D = K
  · subst D
    apply pairCore C hs hl ht a ha b hb ne ab paid big
    intro e he
    obtain ⟨j,hj,hit⟩ := Finset.mem_biUnion.mp (remCov he)
    obtain ⟨hjJ,hjK⟩ := Finset.mem_sdiff.mp hj
    by_cases eq : j = a
    · exact Finset.mem_union_left _ (eq ▸ hit)
    · have jb : j = b := by
        by_contra nb
        exact hjK (Finset.mem_erase.mpr ⟨nb,Finset.mem_erase.mpr ⟨eq,hjJ⟩⟩)
      exact Finset.mem_union_right _ (jb ▸ hit)
  · have more : (K \ D).Nonempty := Finset.sdiff_nonempty.mpr (fun h => terminal (Finset.Subset.antisymm sub h))
    apply expandingCore C hs hl ht a ha b hb ne ab D sub more paid big remCov
    intro S hS hne
    apply lt_of_not_ge
    intro smallS
    have dis : Disjoint D S := Finset.disjoint_left.mpr (fun j hd hs => (Finset.mem_sdiff.mp (hS hs)).2 hd)
    have incl : H (D ∪ S) ⊆ H D ∪ (V ∩ S.biUnion (gammaE G C)) := by
      intro e he
      obtain ⟨hu,j,hj,hit⟩ := (Finset.mem_inter.mp he).imp_right Finset.mem_biUnion.mp
      by_cases h : e ∈ H D
      · exact Finset.mem_union_left _ h
      · have sj : j ∈ S := (Finset.mem_union.mp hj).resolve_left (fun dj =>
          h (Finset.mem_inter.mpr ⟨hu,Finset.mem_biUnion.mpr ⟨j,dj,hit⟩⟩))
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hu,h⟩,Finset.mem_biUnion.mpr ⟨j,sj,hit⟩⟩)
    have bound := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
    have count := Finset.card_union_of_disjoint dis
    have cost : (H (D ∪ S)).card ≤ (D ∪ S).card :=
      bound.trans ((Nat.add_le_add paid smallS).trans_eq count.symm)
    have mem : D ∪ S ∈ choices := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset sub (hS.trans Finset.sdiff_subset)),cost⟩
    have hi := hmax (D ∪ S) mem
    have positive := Finset.card_pos.mpr hne
    omega
