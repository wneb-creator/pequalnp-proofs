namespace PEqualNP.Outside.L_meta_2592_aux.GateFirst

def firstLow (d : Fin 4) (j : Fin 10) : Extended.Row :=
  if d.val = 0 ∨ d.val = 3 then
    ![16, 16, 16, 16, 16, 64, 16, 16, 16, 16] j
  else ![16, 128, 48, 272, 64, 16, 20, 65, 72, 18] j

def firstHigh (d : Fin 4) (j : Fin 10) : Extended.Row :=
  ⟨(firstLow d j).val + 512, by unfold firstLow; split <;> fin_cases j <;> decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma first_binary_samples : ∀ (d : Fin 4) (j : Fin 10), j ≠ 0 →
    Extended.bit (firstLow d j) Extended.target ≠
      Extended.bit (firstHigh d j) Extended.target ∧
    Extended.bit (firstLow d j)
        (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) =
      Extended.bit (firstHigh d j)
        (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) ∧
    Extended.initial.all (fun a =>
      (Extended.bit (firstLow d j) a == Extended.bit (firstHigh d j) a) ||
        (a == Extended.first)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma first_binary_projected : ∀ (d : Fin 4) (j : Fin 10),
    projected (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) = zero ∨
      projected (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) ∈ inputs := by
  decide +kernel

lemma first_live_retained (d : Fin 4) (j : Fin 10) (distinct : j ≠ 0)
    {k : Nat} {U : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k
      (insert (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) U))
    (raw : ∀ a ∈ U, a ∈ Extended.initial) : Extended.first ∈ U := by
  obtain ⟨diff, equal, stable⟩ := first_binary_samples d j distinct
  obtain ⟨a, ha, changed⟩ := Extended.live_row_difference run diff
  rcases Finset.mem_insert.mp ha with eq | hm
  · exact False.elim (changed (eq.symm ▸ equal))
  · have chk := List.all_eq_true.mp stable a (raw a hm)
    simp only [Bool.or_eq_true, beq_iff_eq] at chk
    exact chk.resolve_left changed ▸ hm

lemma first_live_tail_floor (d : Fin 4) (j : Fin 10) (distinct : j ≠ 0)
    {k : Nat} {U : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k
      (insert (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) U))
    (raw : ∀ a ∈ U, a ∈ Extended.initial) : 16 ≤ k := by
  have retained := first_live_retained d j distinct run raw
  have permitted : Extended.initial.all
      (fun a => (projected a == zero) || inputs.contains (projected a)) = true := by
    decide +kernel
  apply tail_constant_floor run _ Extended.first (Finset.mem_insert_of_mem retained)
    (by decide +kernel)
  intro a ha
  rcases Finset.mem_insert.mp ha with eq | hm
  · exact eq.symm ▸ first_binary_projected d j
  · have hh := List.all_eq_true.mp permitted a (raw a hm)
    simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using hh

end PEqualNP.Outside.L_meta_2592_aux.GateFirst
