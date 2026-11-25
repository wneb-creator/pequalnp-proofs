import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1768_45
    (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (core : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      H.edgeFinset ⊆ (Ustar G C).filter (fun e =>
        ∃ u v : Fin n, e = s(u, v) ∧
          ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
            u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
            gateVal n C g (pairInput u v) = true) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      H.edgeFinset.card ≤ k * (C.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k, hCore⟩ := core
  refine ⟨k + 2, ?_⟩
  intro n G inst C hGirth hLeast hTop
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + 2 * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F instF hF
      by_cases h : ∀ v : Fin n,
          (F.neighborSet v).ncard = 0 ∨ 3 ≤ (F.neighborSet v).ncard
      · exact ⟨F, le_rfl, h, by omega⟩
      · push Not at h
        obtain ⟨v, hv0, hv2⟩ := h
        have hDeg := F.ncard_neighborSet v
        have hvPos : 0 < F.degree v := by omega
        have hv : v ∈ F.support := by
          by_contra hn
          have hz : F.neighborSet v = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hn ⟨w, hw⟩
          exact hv0 (by rw [hz, Set.ncard_empty])
        have hPpos : 0 < F.support.ncard := by
          rw [← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ F.support.ncard - 1 := by
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        obtain ⟨H, hHR, hMin, hH⟩ := smaller R.support.ncard (by omega) R rfl
        refine ⟨H, hHR.trans (F.deleteIncidenceSet_le v), hMin, ?_⟩
        have hRemoved : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
          F.card_edgeFinset_deleteIncidenceSet v
        have hLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        rw [edgeCount R] at hH
        rw [edgeCount F]
        omega
  let E := (Ustar G C).filter (fun e =>
    ∃ u v : Fin n, e = s(u, v) ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧
        gateVal n C g (pairInput u v) = true)
  change E.card ≤ (k + 2) * (C.size + 1)
  have hEG : E ⊆ G.edgeFinset :=
    (Finset.filter_subset _ _).trans Finset.sdiff_subset
  let D := G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 (Fin n))) : Set _)
  have hDE : D.edgeFinset = E := by
    rw [SimpleGraph.edgeFinset_deleteEdges]
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · intro h
      by_contra he
      exact h.2 ⟨h.1, he⟩
    · intro he
      exact ⟨hEG he, fun h => h.2 he⟩
  obtain ⟨H, hHD, hMin, hPeel⟩ := peel D.support.ncard D rfl
  have hDSupport : D.support ⊆ G.support := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, (G.deleteEdges_le _) hw⟩
  have hHE : H.edgeFinset ⊆ E := by
    rw [← hDE]
    exact SimpleGraph.edgeFinset_mono hHD
  have hBound := hCore n G C H hGirth hLeast hTop hHE hMin
  have hSupport := (Set.ncard_le_ncard hDSupport).trans (essential n G C hLeast)
  rw [edgeCount D, hDE, edgeCount H] at hPeel
  rw [Nat.add_mul]
  omega
