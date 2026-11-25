import PEqualNP.Outside.L_meta_3760

namespace PEqualNP.Outside.L_meta_2448_aux.mixedSupport

lemma no_common_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (L R : Finset (Fin n)) (a b : Fin n)
    (hab : a ≠ b) (hL : 2 ≤ L.card) (hR : 2 ≤ R.card)
    (ha : ∀ u ∈ L, G.Adj a u) (hb : ∀ u ∈ R, G.Adj b u) :
    ¬ ∃ z : Fin n, ∀ u ∈ L ∪ R, G.Adj z u := by
  rintro ⟨z, hz⟩
  have za : z = a := by
    by_contra hza
    have hsub : L ⊆ Finset.univ.filter (fun u => G.Adj z u ∧ G.Adj a u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz u (Finset.mem_union_left _ hu), ha u hu⟩
    have hc := Finset.card_le_card hsub
    have hd := h4 z a hza
    omega
  have zb : z = b := by
    by_contra hzb
    have hsub : R ⊆ Finset.univ.filter (fun u => G.Adj z u ∧ G.Adj b u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz u (Finset.mem_union_right _ hu), hb u hu⟩
    have hc := Finset.card_le_card hsub
    have hd := h4 z b hzb
    omega
  exact hab (za.symm.trans zb)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3760 PEqualNP.Outside.L_meta_3760.Close
open PEqualNP.Outside.L_meta_3760.M1528.P1.S98 (W AO AO_of_IsAO2 W_and)
open PEqualNP.Outside.L_meta_3760.M1528.P2 (OrR mem_orIn orR_mono opnd_eq graphFun_pair)

lemma clean_sides_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j ∈ tops G C)
    (t : Fin 2) (x z : Fin n) (hx : x ∈ side (n := n) C j t)
    (hz : z ∈ side (n := n) C j (1 - t)) : G.Adj x z := by
  have hA : AO n C := AO_of_IsAO2 n C hAO
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at hj
  have hW0 := orR_mono n C hA (pairInput x z) (opnd C j t) x.val
    ((mem_orIn n C hA _ (by have := opnd_lt' hA j hj.1 t; omega) x).mp hx)
    (by rw [M1528.P2.W_input n C _ x.val x.isLt]; simp [pairInput])
  have hW1 := orR_mono n C hA (pairInput x z) (opnd C j (1 - t)) z.val
    ((mem_orIn n C hA _ (by have := opnd_lt' hA j hj.1 (1 - t); omega) z).mp hz)
    (by rw [M1528.P2.W_input n C _ z.val z.isLt]; simp [pairInput])
  have hWj : W n C (pairInput x z) (n + j) = true := by
    rw [W_and n C _ j hj.1 hj.2.1 (opnd C j 0) (opnd C j 1) (opnd_eq n C hA j hj.1)
      (opnd_lt' hA j hj.1 0) (opnd_lt' hA j hj.1 1), Bool.and_eq_true]
    rcases fin2_cases t with rfl | rfl
    · exact ⟨hW0, hW1⟩
    · exact ⟨hW1, hW0⟩
  have hF := hj.2.2 (pairInput x z) hWj
  rwa [graphFun_pair] at hF

lemma mixed_side_opposite_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j ∈ tops G C) (t : Fin 2)
    (L R : Finset (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (hL : 2 ≤ L.card) (hR : 2 ≤ R.card)
    (ha : ∀ u ∈ L, G.Adj a u) (hb : ∀ u ∈ R, G.Adj b u)
    (hsub : L ∪ R ⊆ side (n := n) C j t) :
    side (n := n) C j (1 - t) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply no_common_guard G h4 L R a b hab hL hR ha hb
  refine ⟨z, ?_⟩
  intro u hu
  exact (clean_sides_adjacent G C hAO j hj t u z (hsub hu) hz).symm

lemma mixed_reader_centreless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j ∈ tops G C) (t : Fin 2)
    (L R : Finset (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (hL : 2 ≤ L.card) (hR : 2 ≤ R.card)
    (ha : ∀ u ∈ L, G.Adj a u) (hb : ∀ u ∈ R, G.Adj b u)
    (hsub : L ∪ R ⊆ side (n := n) C j t) : j ∈ centreless G C := by
  have he := mixed_side_opposite_empty G h4 C hAO j hj t L R a b hab hL hR ha hb hsub
  apply Finset.mem_filter.mpr
  refine ⟨hj, ?_⟩
  rcases fin2_cases t with rfl | rfl
  · exact Or.inr he
  · exact Or.inl he

end PEqualNP.Outside.L_meta_2448_aux.mixedSupport
