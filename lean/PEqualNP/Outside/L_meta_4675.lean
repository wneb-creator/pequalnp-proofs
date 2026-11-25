import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

lemma no_mixed_or {n : ℕ} {C : Circuit} {colour : ℕ → Bool}
    (ht : tCount n C colour = 0) {g : ℕ} (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) {i j : Fin n}
    (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g))
    (hci : colour i = false) (hcj : colour j = true) : False := by
  have hmem : g ∈ twoColour n C colour :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,
      hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩
  have hempty : twoColour n C colour = ∅ := Finset.card_eq_zero.mp ht
  simpa [hempty] using hmem

lemma no_point_line_or {p l : ℕ} {C : Circuit}
    (ht : tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    {g : ℕ} (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    {a : Fin p} {b : Fin l}
    (ha : Fin.castAdd l a ∈ orIn (p + l) C (p + l + g))
    (hb : Fin.natAdd p b ∈ orIn (p + l) C (p + l + g)) : False := by
  apply no_mixed_or ht hg hop ha hb
  · simp only [Fin.coe_castAdd, decide_eq_false_iff_not, not_le]
    exact a.isLt
  · simp

end PEqualNP.Outside.L_meta_4675
