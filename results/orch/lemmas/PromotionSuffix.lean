namespace PEqualNP.Outside.L_meta_2592_aux.Promotion

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGate
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma binary_floor_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) : 17 ≤ D.gates.length := by
  have hsize : HasU2Size pet D.gates.length := ⟨D, hwf, le_rfl, computes⟩
  obtain ⟨M, hm, hle⟩ := exists_minU2 hsize
  obtain ⟨v, s, hs, hc⟩ := zero_restriction_saves_two M hm
  have hf := floor v s hc
  omega

lemma minimal_of_cap17 (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17) :
    IsMinU2 pet D := by
  refine ⟨hwf, computes, ?_⟩
  intro M hm hc
  have hf := binary_floor_of_compute floor M hm hc
  omega

lemma first_sources_negative_any (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17)
    (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true ∧
    ∀ j (hj : j < D.gates.length),
      (D.gates[j].a = D.gates[0].a → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].a → D.gates[j].pb = true) ∧
      (D.gates[j].a = D.gates[0].b → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].b → D.gates[j].pb = true) :=
  first_sources_negative_everywhere floor D (minimal_of_cap17 floor D hwf computes small)
    small h0

end PEqualNP.Outside.L_meta_2592_aux.Promotion
