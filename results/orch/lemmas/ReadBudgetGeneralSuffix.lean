namespace PEqualNP.Outside.L_meta_2592_aux.ReadBudget

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma reader_bound_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (v : Fin 10) :
    (readers D v).card + 15 ≤ D.gates.length := by
  obtain ⟨hwf', hev, hlen, hEv, _⟩ := restrictU2_spec D hwf v false
  have hc : HasU2Size (fun x => pet (Function.update x v false))
      (restrictU2 D v false).gates.length :=
    ⟨restrictU2 D v false, hwf', le_rfl, fun x => (hev x).trans (computes _)⟩
  have hf := floor v _ hc
  have hs : readers D v ⊆ elimSet D v false := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [elimSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with ha | hb
    · left
      rw [ha, hEv]
      rfl
    · right
      rw [hb, hEv]
      rfl
  have hcard := Finset.card_le_card hs
  omega

lemma at_most_two_readers_of_compute (floor : ZeroFloor) (D : U2Circuit) (hwf : U2Wf D)
    (computes : ∀ x, u2Eval D x = pet x) (small : D.gates.length ≤ 17) (v : Fin 10) :
    (readers D v).card ≤ 2 := by
  have h := reader_bound_of_compute floor D hwf computes v
  omega

end PEqualNP.Outside.L_meta_2592_aux.ReadBudget
