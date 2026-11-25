namespace PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors

lemma every_vertex_nine_times : ∀ i : Fin 10,
    (records.map (fun r =>
      (if r.a = i then 1 else 0) + (if r.b = i then 1 else 0) +
        (if r.c = i then 1 else 0))).sum = 9 := by
  decide +kernel

lemma weighted_record_sum (c : Fin 10 → Nat) :
    (records.map (fun r => c r.a + c r.b + c r.c)).sum = 9 * ∑ i, c i := by
  simp only [records, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Record.a, Record.b, Record.c, Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change _ = 9 * (c 0 + (c 1 + (c 2 + (c 3 + (c 4 + (c 5 + (c 6 + (c 7 + (c 8 + c 9)))))))))
  omega

lemma record_sum_ge_one_fifty (c : Fin 10 → Nat)
    (bound : ∀ r ∈ records, 5 ≤ c r.a + c r.b + c r.c) :
    150 ≤ 9 * ∑ i, c i := by
  rw [← weighted_record_sum]
  have lower : ∀ L : List Record, (∀ r ∈ L, 5 ≤ c r.a + c r.b + c r.c) →
      5 * L.length ≤ (L.map (fun r => c r.a + c r.b + c r.c)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons r L ih =>
      intro h
      have hr := h r (by simp)
      have hl := ih (fun q hq => h q (by simp [hq]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  have result := lower records bound
  have length : records.length = 30 := by rfl
  rw [length] at result
  exact result

end PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors
