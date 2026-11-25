import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113GlobalData

open PEqualNP.Outside.L_meta_6581

def inputPos : Fin 10 → Fin 10 := ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def vertexAut : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
    ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
    ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
    ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1],
    ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1],
    ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
    ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0]]

def embedAt (i : Fin 10) (r : Row) : Extended.Row :=
  ⟨((List.ofFn fun j : Fin 10 =>
      if r.val.testBit (inputPos (vertexAut i j)).val
      then 2 ^ (inputPos j).val else 0).sum) % 1024,
    Nat.mod_lt _ (by decide)⟩

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

def RowCorrect (i : Fin 10) (r : Row) : Prop :=
  Extended.bit (embedAt i r) Extended.target = bit r graph ∧
  ∀ j : Fin 10, Extended.bit (embedAt i r) (pin j) =
    bit r (inputs.getD (inputPos (vertexAut i j)).val zero)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_0 : ∀ r : Row, RowCorrect 0 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_1 : ∀ r : Row, RowCorrect 1 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_2 : ∀ r : Row, RowCorrect 2 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_3 : ∀ r : Row, RowCorrect 3 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_4 : ∀ r : Row, RowCorrect 4 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_5 : ∀ r : Row, RowCorrect 5 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_6 : ∀ r : Row, RowCorrect 6 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_7 : ∀ r : Row, RowCorrect 7 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_8 : ∀ r : Row, RowCorrect 8 r := by
  unfold RowCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma row_data_9 : ∀ r : Row, RowCorrect 9 r := by
  unfold RowCorrect
  decide +kernel

lemma row_data : ∀ (i : Fin 10) (r : Row), RowCorrect i r := by
  intro i
  fin_cases i
  · exact row_data_0
  · exact row_data_1
  · exact row_data_2
  · exact row_data_3
  · exact row_data_4
  · exact row_data_5
  · exact row_data_6
  · exact row_data_7
  · exact row_data_8
  · exact row_data_9

lemma target_restriction (i : Fin 10) :
    restrictRows (embedAt i) (Extended.observe Extended.target) = observe graph := by
  funext r
  exact (row_data i r).1

lemma pin_restriction (i j : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (pin j)) =
      observe (inputs.getD (inputPos (vertexAut i j)).val zero) := by
  funext r
  exact (row_data i r).2 j

lemma chosen_pin_zero (i : Fin 10) :
    restrictRows (embedAt i) (Extended.observe (pin i)) = fun _ => false := by
  rw [pin_restriction]
  have h : ∀ i : Fin 10, inputPos (vertexAut i i) = 9 := by decide +kernel
  rw [h]
  funext r
  simp [observe, bit, inputs, zero]

lemma pin_available (i j : Fin 10) : Available true (inputs.map observe)
    (restrictRows (embedAt i) (Extended.observe (pin j))) := by
  rw [pin_restriction]
  by_cases h : (inputPos (vertexAut i j)).val < inputs.length
  · apply Or.inl
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem _
  · apply Or.inr
    apply Or.inl
    rw [List.getD_eq_default _ _ (by omega)]
    refine ⟨false, ?_⟩
    funext r
    simp [observe, bit, zero]

end PEqualNP.Outside.Pilot113GlobalData
