import MonoBase
namespace PEqualNP.Outside.L_meta_1884.GeneralFloorBridgeCheck
open PEqualNP.Outside.L_meta_2590.Mono18
lemma nineFloorOfCert {u : Bool} {n : Nat}
    (cert : Impossible u graph n inputs.toFinset) : Lower u inputs graph (n + 1) := by
  apply lower_impossible graph_proper (by decide +kernel) (by decide +kernel) _ cert
  intro a ha
  have idx (b : Sig) (hb : b ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = b := by
    rw [← input_list] at hb
    exact List.mem_ofFn.mp hb
  obtain ⟨i, rfl⟩ := idx a ha
  refine ⟨absentRow670 i, presentRow670 i, requiredInputs.1 i, ?_⟩
  intro v hv hne
  obtain ⟨j, rfl⟩ := idx v hv
  apply requiredInputs.2 i j
  rintro rfl
  exact hne rfl


end PEqualNP.Outside.L_meta_1884.GeneralFloorBridgeCheck
