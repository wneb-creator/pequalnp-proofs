import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113GlobalWitness

open PEqualNP.Outside.L_meta_6581

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

def inputPos : Fin 10 → Fin 10 := ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def andRows : Fin 10 → Fin 10 → Extended.Row :=
  ![![0, 64, 128, 128, 128, 128, 128, 128, 128, 128],
    ![32, 0, 512, 512, 512, 512, 512, 512, 512, 512],
    ![128, 256, 0, 128, 128, 128, 128, 128, 128, 128],
    ![32, 32, 64, 0, 32, 32, 32, 32, 32, 32],
    ![256, 512, 512, 512, 0, 512, 512, 512, 512, 512],
    ![1, 512, 512, 512, 512, 0, 512, 512, 512, 512],
    ![128, 8, 128, 128, 128, 128, 0, 128, 128, 128],
    ![32, 32, 16, 32, 32, 32, 32, 0, 32, 32],
    ![256, 256, 256, 16, 256, 256, 256, 256, 0, 256],
    ![64, 64, 64, 64, 4, 64, 64, 64, 64, 0]]

def otherRows : Fin 10 → Fin 10 → Extended.Row :=
  ![![0, 128, 96, 384, 64, 16, 68, 129, 136, 130],
    ![512, 0, 32, 768, 96, 48, 4, 513, 520, 514],
    ![768, 128, 0, 256, 192, 144, 260, 1, 136, 130],
    ![544, 192, 32, 0, 64, 48, 36, 65, 8, 34],
    ![512, 384, 544, 256, 0, 272, 516, 513, 520, 2],
    ![512, 129, 544, 768, 65, 0, 516, 1, 8, 514],
    ![520, 128, 40, 384, 192, 144, 0, 129, 8, 2],
    ![544, 144, 32, 272, 96, 16, 36, 0, 40, 2],
    ![768, 384, 48, 256, 80, 16, 4, 257, 0, 258],
    ![516, 192, 96, 260, 64, 80, 4, 1, 72, 0]]

def witnessLo (op : Fin 3) (i j : Fin 10) : Extended.Row :=
  if op = 0 then andRows i j else otherRows i j

def witnessHi (op : Fin 3) (i j : Fin 10) : Extended.Row :=
  witnessLo op i j + 2 ^ (inputPos i).val

def WitnessCorrect (op : Fin 3) (i j : Fin 10) : Prop := i ≠ j →
  Extended.bit (witnessLo op i j) Extended.target ≠
    Extended.bit (witnessHi op i j) Extended.target ∧
  Extended.bit (witnessLo op i j) (Extended.bin op.val (pin i) (pin j)) =
    Extended.bit (witnessHi op i j) (Extended.bin op.val (pin i) (pin j)) ∧
  Extended.initial.all (fun a => (a == pin i) ||
    (Extended.bit (witnessLo op i j) a ==
      Extended.bit (witnessHi op i j) a)) = true ∧
  Extended.bin op.val (pin i) (pin j) ≠ pin i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_0 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 0 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_1 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 1 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_2 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 2 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_3 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 3 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_4 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 4 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_5 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 5 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_6 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 6 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_7 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 7 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_8 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 8 j := by
  unfold WitnessCorrect
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data_9 : ∀ (op : Fin 3) (j : Fin 10), WitnessCorrect op 9 j := by
  unfold WitnessCorrect
  decide +kernel

lemma witness_data : ∀ (i : Fin 10) (op : Fin 3) (j : Fin 10), WitnessCorrect op i j := by
  intro i
  fin_cases i
  · exact witness_data_0
  · exact witness_data_1
  · exact witness_data_2
  · exact witness_data_3
  · exact witness_data_4
  · exact witness_data_5
  · exact witness_data_6
  · exact witness_data_7
  · exact witness_data_8
  · exact witness_data_9

lemma first_pin_retained (op : Fin 3) (i j : Fin 10) (hij : i ≠ j)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin op.val (pin i) (pin j)) U)) :
    pin i ∈ U := by
  obtain ⟨different, same, onlyFirst, _⟩ := witness_data i op j hij
  obtain ⟨a, ha, changes⟩ := Extended.live_row_difference tailRun different
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact False.elim (changes same)
  · have h := List.all_eq_true.mp onlyFirst a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    exact h.resolve_right changes ▸ ha

end PEqualNP.Outside.Pilot113GlobalWitness
