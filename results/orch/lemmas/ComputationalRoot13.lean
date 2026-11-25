import ComputationalBounds

namespace PEqualNP.Outside.L_meta_10760_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root13_check : okE [] rootSeeds (0, 13) = true := by decide +kernel

lemma root13 : Imp [] 0 13 :=
  imp_okE (E := []) (Q := rootSeeds) (e := (0, 13)) (Or.inl rfl) root13_check rootSeeds_sound

lemma lower13 (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ x : Fin 7 → Bool, D.eval (List.ofFn x) = f x) : 13 ≤ D.size := by
  by_contra h
  exact root13 D.size (by omega) (bridge D hD hf)

end PEqualNP.Outside.L_meta_10760_aux
