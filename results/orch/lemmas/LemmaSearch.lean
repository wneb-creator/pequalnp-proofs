import Mathlib

namespace PEqualNP.Outside.L_meta_1770

lemma peel_graph_core (n : ℕ) (F : SimpleGraph (Fin n)) :
    ∃ H : SimpleGraph (Fin n), H ≤ F ∧
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
      F.edgeSet.ncard ≤ H.edgeSet.ncard + 2 * F.support.ncard := by
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + 2 * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases h : ∀ v : Fin n, (F.neighborSet v).ncard = 0 ∨ 3 ≤ (F.neighborSet v).ncard
      · exact ⟨F,le_rfl,h,by omega⟩
      · push Not at h
        obtain ⟨v,hv0,hv2⟩ := h
        have hDeg := F.ncard_neighborSet v
        have hvPos : 0 < F.degree v := by omega
        have hv : v ∈ F.support := by
          by_contra hn
          have hz : F.neighborSet v = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hn ⟨w,hw⟩
          exact hv0 (by rw [hz,Set.ncard_empty])
        have hPpos : 0 < F.support.ncard := by
          rw [← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ F.support.ncard - 1 := by
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        obtain ⟨H,hHR,hMin,hH⟩ := smaller R.support.ncard (by omega) R rfl
        refine ⟨H,hHR.trans (F.deleteIncidenceSet_le v),hMin,?_⟩
        have hRemoved : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
          F.card_edgeFinset_deleteIncidenceSet v
        have hLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        rw [edgeCount R] at hH
        rw [edgeCount F]
        omega
  exact peel F.support.ncard F rfl

lemma bound_of_core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Sym2 (Fin n))) (hT : T ⊆ G.edgeFinset) (B K : ℕ)
    (hSupport : G.support.ncard ≤ B)
    (hCore : ∀ H : SimpleGraph (Fin n), H ≤ G → H.edgeSet ⊆ (T : Set _) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ K * B) :
    T.card ≤ (K + 2) * B := by
  classical
  let D := G.deleteEdges ((G.edgeFinset \ T : Finset (Sym2 (Fin n))) : Set _)
  have hDG : D ≤ G := G.deleteEdges_le _
  have hDE : D.edgeFinset = T := by
    dsimp [D]
    rw [SimpleGraph.edgeFinset_deleteEdges]
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · intro h
      by_contra hn
      exact h.2 ⟨h.1, hn⟩
    · intro h
      exact ⟨hT h, fun h' => h'.2 h⟩
  obtain ⟨H, hHD, hMin, hPeel⟩ := peel_graph_core n D
  have hDSupport : D.support ⊆ G.support := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hDG hw⟩
  have hBound := hCore H (hHD.trans hDG) (by
    rw [← hDE, SimpleGraph.coe_edgeFinset]
    exact SimpleGraph.edgeSet_mono hHD) hMin
  have hSupportD := (Set.ncard_le_ncard hDSupport).trans hSupport
  have hCount : D.edgeSet.ncard = T.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hDE]
  rw [hCount] at hPeel
  calc
    T.card ≤ H.edgeSet.ncard + 2 * D.support.ncard := hPeel
    _ ≤ K * B + 2 * B := Nat.add_le_add hBound (Nat.mul_le_mul_left 2 hSupportD)
    _ = (K + 2) * B := by ring

end PEqualNP.Outside.L_meta_1770
