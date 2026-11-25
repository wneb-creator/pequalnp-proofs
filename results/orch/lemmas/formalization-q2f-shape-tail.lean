namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_raw_mem (s : Fin 15) (a b c : Fin 10) (i : Fin 10) :
    q2f_raw s a b c i ∈ q2f_codes s a b c := by
  apply (q2f_mem_iff s a b c _).mp
  simp only [q2f_mem, Bool.or_eq_true, decide_eq_true_eq]
  fin_cases i <;> tauto

lemma q2f_missing_mem (s : Fin 15) (a b c : Fin 10) :
    q2f_missing s a b c ∈ q2f_codes s a b c :=
  q2f_raw_mem s a b c _

lemma q2f_certificate_card (s : Fin 15) (a b c : Fin 10)
    (h : q2f_certificate s a b c = true) : 7 ≤ (q2f_codes s a b c).card := by
  exact of_decide_eq_true (q2f_and_true_iff.mp h).1

lemma q2f_certificate_shape (s : Fin 15) (a b c : Fin 10)
    (h : q2f_certificate s a b c = true)
    (bound : (q2f_codes s a b c).card ≤ 7)
    (closed : q2f_generators s a b c = true →
      ∀ m ∈ q2f_codes s a b c, q2f_closed s a b c m = true) :
    q2f_shape s a b c = true := by
  have alternatives := (q2f_and_true_iff.mp h).2
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at alternatives
  rcases alternatives with eight | shape | ⟨generators,missing⟩
  · omega
  · exact shape
  · have yes := closed generators _ (q2f_missing_mem s a b c)
    simp only [yes, Bool.not_true, Bool.false_eq_true] at missing

lemma q2f_shape_member (s : Fin 15) (a b c : Fin 10)
    (h : q2f_shape s a b c = true) (m : Fin 128) (hm : m ∈ q2f_codes s a b c) :
    cap7_card m ≤ 2 ∨ m = 11 ∨ m = 69 ∨ m = 49 ∨ m = q2f_superCode s := by
  obtain ⟨i,rfl⟩ := q2f_mem_exists s a b c m ((q2f_mem_iff s a b c m).mpr hm)
  simp only [q2f_shape, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    and_assoc,or_assoc] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

lemma q2f_allowed_shape (s : Fin 15) (a b c : Fin 10)
    (h : q2f_shape s a b c = true) (m : Fin 128)
    (ha : q2f_allowed s a b c m = true) :
    cap7_card m ≤ 2 ∨ m = 11 ∨ m = 69 ∨ m = 49 ∨ m = q2f_superCode s := by
  rcases q2f_or_true_iff.mp ha with small | member
  · exact Or.inl (q2f_small_card s a b c m small)
  · exact q2f_shape_member s a b c h m ((q2f_mem_iff s a b c m).mp member)

end PEqualNP.Outside.L_meta_6659_aux
