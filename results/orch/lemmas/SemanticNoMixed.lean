import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

lemma no_twoColour (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ht : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) :
    ¬ PEqualNP.TwoColour.IsTwoColour (p + l) C (fun i => decide (p ≤ i)) g := by
  intro h
  have he : PEqualNP.TwoColour.twoColour (p + l) C (fun i => decide (p ≤ i)) = ∅ :=
    Finset.card_eq_zero.mp ht
  have hm : g ∈ PEqualNP.TwoColour.twoColour (p + l) C (fun i => decide (p ≤ i)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h⟩
  rw [he] at hm
  exact Finset.notMem_empty g hm

lemma orIn_monochromatic (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ht : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) (hg : g < C.gates.length)
    (ho : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
      PEqualNP.CircuitLowerBounds.GateOp.or) :
    (∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), (i : ℕ) < p) ∨
    (∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), p ≤ (i : ℕ)) := by
  classical
  by_cases h : ∀ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + g), p ≤ (i : ℕ)
  · exact Or.inr h
  · push Not at h
    obtain ⟨i, hi, hip⟩ := h
    refine Or.inl ?_
    intro j hj
    by_contra hnp
    apply no_twoColour p l C ht g
    refine ⟨hg, ho, ⟨i, hi, ?_⟩, ⟨j, hj, ?_⟩⟩
    · exact decide_eq_false (by omega)
    · exact decide_eq_true (by omega)

end PEqualNP.Outside.L_meta_4970_aux
