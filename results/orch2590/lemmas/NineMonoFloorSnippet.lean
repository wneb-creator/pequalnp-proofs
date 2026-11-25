def neighbor670 (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow670 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor670 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel

set_option maxHeartbeats 1000000 in
lemma nineMonoFloorOfCert (cert : Impossible false graph 15 inputs.toFinset) :
    Lower false inputs graph 16 := by
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
