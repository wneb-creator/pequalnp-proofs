import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.ZeroNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem monotone_of_zero_not (C : Circuit) (legal : FanInTwo C)
    (zero : PEqualNP.NotBracket.notCount C = 0) : Monotone2 C := by
  have empty : C.gates.filter (fun g : Gate =>
      @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = [] :=
    List.length_eq_zero_iff.mp zero
  intro g hg
  obtain ⟨ho, hl⟩ := legal g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
  refine ⟨?_, hl⟩
  rcases ho with ha | hb | hn
  · exact Or.inl ha
  · exact Or.inr hb
  · have member : g ∈ C.gates.filter (fun g : Gate =>
        @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) :=
      List.mem_filter.mpr ⟨hg, by simp [hn]⟩
    rw [empty] at member
    exact False.elim (List.not_mem_nil member)

theorem eighteen_of_floors (C : Circuit) (legal : FanInTwo C)
    (binary : 17 + PEqualNP.NotBracket.notCount C ≤ C.size)
    (mono : Monotone2 C → 18 ≤ C.size) : 18 ≤ C.size := by
  by_cases zero : PEqualNP.NotBracket.notCount C = 0
  · exact mono (monotone_of_zero_not C legal zero)
  · omega

end PEqualNP.Outside.L_meta_1884.ZeroNot
