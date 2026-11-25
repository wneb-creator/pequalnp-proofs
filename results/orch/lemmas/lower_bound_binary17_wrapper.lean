namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.CircuitLowerBounds

lemma binary17 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  exact binary_floor17_of_canonical (fun j d _ _ run raw => suffixSixteen j d run raw)
    C legal computes

lemma at_most_two_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  have bound := binary17 C legal computes
  omega

lemma one_or_two_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    PEqualNP.NotBracket.notCount C = 1 ∨ PEqualNP.NotBracket.notCount C = 2 := by
  have bound := at_most_two_not C legal small computes
  have pos : 0 < PEqualNP.NotBracket.notCount C := by
    obtain ⟨g,hg,hnot⟩ := hasNot
    let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
    have mem : g ∈ C.gates.filter (fun h => decide (h.op = GateOp.not)) :=
      List.mem_filter.mpr ⟨hg,decide_eq_true hnot⟩
    by_contra! h
    have hz : PEqualNP.NotBracket.notCount C = 0 := by omega
    have empty := List.length_eq_zero_iff.mp hz
    rw [empty] at mem
    cases mem
  omega

end PEqualNP.Outside.L_meta_2592_aux.Binary16
