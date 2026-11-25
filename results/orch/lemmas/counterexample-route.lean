import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685

lemma empty_incidence (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  refine ⟨⟨[], Np + Nl⟩, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · intro y
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hI]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · simp
  · simp
  · simp

lemma monotone_eq_of_hypergraph_boundary {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset (Finset α)) (f : Finset α → Bool)
    (mono : ∀ S T, S ⊆ T → f S ≤ f T)
    (positive : ∀ e ∈ E, f e = true)
    (negative : ∀ T, (∀ e ∈ E, ¬ e ⊆ T) →
      (∀ a, a ∉ T → ∃ e ∈ E, e ⊆ insert a T) → f T = false)
    (S : Finset α) : f S = decide (∃ e ∈ E, e ⊆ S) := by
  classical
  by_cases h : ∃ e ∈ E, e ⊆ S
  · obtain ⟨e, he, hs⟩ := h
    have hm := mono e S hs
    have ht : f S = true := by
      cases hfs : f S with
      | false =>
        have hn : ¬ ((true : Bool) ≤ false) := by decide
        exact False.elim (hn (by simpa [positive e he, hfs] using hm))
      | true => rfl
    simp [ht, show ∃ e ∈ E, e ⊆ S from ⟨e, he, hs⟩]
  · let A : Finset (Finset α) := Finset.univ.filter fun T =>
      S ⊆ T ∧ ∀ e ∈ E, ¬ e ⊆ T
    have hs : ∀ e ∈ E, ¬ e ⊆ S := fun e he hsub => h ⟨e, he, hsub⟩
    have hmem : S ∈ A := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (fun _ ha => ha), hs⟩
    obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image A Finset.card ⟨S, hmem⟩
    have hST : S ⊆ T := (Finset.mem_filter.mp hT).2.1
    have hfree : ∀ e ∈ E, ¬ e ⊆ T := (Finset.mem_filter.mp hT).2.2
    have hboundary : ∀ a, a ∉ T → ∃ e ∈ E, e ⊆ insert a T := by
      intro a ha
      by_contra hn
      have hfree' : ∀ e ∈ E, ¬ e ⊆ insert a T := fun e he hsub => hn ⟨e, he, hsub⟩
      have hmem' : insert a T ∈ A := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hST.trans (Finset.subset_insert _ _), hfree'⟩
      have hcard := hmax (insert a T) hmem'
      simp [Finset.card_insert_of_notMem ha] at hcard
    have hn := negative T hfree hboundary
    have hf : f S = false := by
      cases hfs : f S with
      | false => rfl
      | true =>
        have hbad : ¬ ((true : Bool) ≤ false) := by decide
        exact False.elim (hbad (by simpa [hn, hfs] using mono S T hST))
    simp [h, hf]

end PEqualNP.Outside.L_meta_2685
