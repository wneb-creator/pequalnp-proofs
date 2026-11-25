import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1770_63
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (core : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (H : SimpleGraph (Fin n)),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      H.edgeSet ⊆ (↑{x9 ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk G C, x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ x13 ∈ PEqualNP.TopForm.junk G C, ∃ x14 ∈ PEqualNP.TopForm.junk G C, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true} : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k, hcore⟩ := core
  refine ⟨k + 2, ?_⟩
  intro n G _ C hGirth hLeast hTop
  classical
  let T : Finset (Sym2 (Fin n)) := {x9 ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk G C, x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ x13 ∈ PEqualNP.TopForm.junk G C, ∃ x14 ∈ PEqualNP.TopForm.junk G C, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}
  have hT : T ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1

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
        have hv : v ∈ F.support := (F.degree_pos_iff_mem_support v).mp hvPos
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

  let D := G.deleteEdges ((G.edgeFinset \ T : Finset (Sym2 (Fin n))) : Set _)
  have hDG : D ≤ G := G.deleteEdges_le _
  have hDE : D.edgeFinset = T := by
    dsimp [D]
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact Finset.sdiff_sdiff_eq_self hT
  obtain ⟨H, hHD, hMin, hPeel⟩ := peel D.support.ncard D rfl
  have hDSupport : D.support ⊆ G.support := SimpleGraph.support_mono hDG
  have hBound := hcore n G C H hGirth hLeast hTop (by
    change H.edgeSet ⊆ (T : Set _)
    rw [← hDE, SimpleGraph.coe_edgeFinset]
    exact SimpleGraph.edgeSet_mono hHD) hMin
  have hSupportD := (Set.ncard_le_ncard hDSupport).trans (support n G C hLeast)
  have hCount : D.edgeSet.ncard = T.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hDE]
  rw [hCount] at hPeel
  calc
    T.card ≤ H.edgeSet.ncard + 2 * D.support.ncard := hPeel
    _ ≤ k * (C.size + 1) + 2 * (C.size + 1) := Nat.add_le_add hBound (Nat.mul_le_mul_left 2 hSupportD)
    _ = (k + 2) * (C.size + 1) := by ring
