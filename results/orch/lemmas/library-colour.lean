import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

lemma no_twoColour {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {s : ℕ → Bool} (h : PEqualNP.TwoColour.tCount n C s = 0) (g : ℕ) :
    ¬ PEqualNP.TwoColour.IsTwoColour n C s g := by
  intro hg
  have he : PEqualNP.TwoColour.twoColour n C s = ∅ := Finset.card_eq_zero.mp h
  have hm : g ∈ PEqualNP.TwoColour.twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simp at hm

lemma orIn_colour_eq {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {s : ℕ → Bool} (h : PEqualNP.TwoColour.tCount n C s = 0)
    {g : ℕ} (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
      PEqualNP.CircuitLowerBounds.GateOp.or)
    {i j : Fin n} (hi : i ∈ PEqualNP.TopForm.orIn n C (n + g))
    (hj : j ∈ PEqualNP.TopForm.orIn n C (n + g)) : s i = s j := by
  have hn := no_twoColour h g
  cases hsi : s i <;> cases hsj : s j
  · rfl
  · exact False.elim (hn ⟨hg, hop, ⟨i, hi, hsi⟩, ⟨j, hj, hsj⟩⟩)
  · exact False.elim (hn ⟨hg, hop, ⟨j, hj, hsj⟩, ⟨i, hi, hsi⟩⟩)
  · rfl

end PEqualNP.Outside.L_meta_4675
