namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_union_comm (x y : Fin 128) : q2f_union x y = q2f_union y x := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, Finset.union_comm]

lemma q2f_inter_comm (x y : Fin 128) : q2f_inter x y = q2f_inter y x := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, Finset.inter_comm]

lemma q2f_union_self (x : Fin 128) : q2f_union x x = x := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, Finset.union_self]

lemma q2f_inter_self (x : Fin 128) : q2f_inter x x = x := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, Finset.inter_self]

lemma q2f_pair_comm (s : Fin 15) (a b c : Fin 10) (i j : Fin 3) :
    q2f_pair s a b c i j = q2f_pair s a b c j i := by
  simp only [q2f_pair, q2f_union_comm (q2f_known s a b c i),
    q2f_inter_comm (q2f_known s a b c i)]

lemma q2f_pair_self (s : Fin 15) (a b c : Fin 10) (i : Fin 3) :
    q2f_pair s a b c i i = true := by
  simp only [q2f_pair, q2f_union_self, q2f_inter_self,
    q2f_closed_known, Bool.or_true, Bool.true_and]

lemma q2f_generators_pair (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (i j : Fin 3) :
    q2f_pair s a b c i j = true := by
  have pairs : q2f_pair s a b c 0 1 = true ∧ q2f_pair s a b c 0 2 = true ∧
      q2f_pair s a b c 1 2 = true := by
    simp only [q2f_generators, Bool.and_eq_true, and_assoc] at h
    exact h.2.2.2.2.2.2.2.2.2.2
  fin_cases i <;> fin_cases j
  · exact q2f_pair_self s a b c 0
  · exact pairs.1
  · exact pairs.2.1
  · exact (q2f_pair_comm s a b c 1 0).trans pairs.1
  · exact q2f_pair_self s a b c 1
  · exact pairs.2.2
  · exact (q2f_pair_comm s a b c 2 0).trans pairs.2.1
  · exact (q2f_pair_comm s a b c 2 1).trans pairs.2.2
  · exact q2f_pair_self s a b c 2

lemma q2f_generators_union (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (x y : Fin 128)
    (hx : q2f_closed s a b c x = true) (hy : q2f_closed s a b c y = true)
    (allowed : q2f_allowed s a b c (q2f_union x y) = true) :
    q2f_closed s a b c (q2f_union x y) = true := by
  rcases q2f_closed_cases s a b c x hx with sx | ⟨i, rfl⟩
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · by_cases low : cap7_card (q2f_union x y) ≤ 2
      · exact q2f_closed_of_small s a b c _ (q2f_small_of_allowed s a b c _ allowed low)
      · exact q2f_closed_seed s a b c h _ allowed
          (q2f_small_union_seed s a b c x y sx sy (by omega))
    · rw [q2f_union_comm] at allowed ⊢
      exact q2f_closed_grow s a b c h _ allowed j (q2f_grow_union s a b c _ x sx)
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · exact q2f_closed_grow s a b c h _ allowed i (q2f_grow_union s a b c _ y sy)
    · have pair := q2f_generators_pair s a b c h i j
      have left := (q2f_and_true_iff.mp pair).1
      simpa only [allowed, Bool.not_true, Bool.false_or] using left

lemma q2f_generators_inter (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (x y : Fin 128)
    (hx : q2f_closed s a b c x = true) (hy : q2f_closed s a b c y = true)
    (allowed : q2f_allowed s a b c (q2f_inter x y) = true) :
    q2f_closed s a b c (q2f_inter x y) = true := by
  have fromSmall (u v : Fin 128) (small : q2f_small s a b c u = true)
      (ha : q2f_allowed s a b c (q2f_inter u v) = true) :
      q2f_closed s a b c (q2f_inter u v) = true := by
    apply q2f_closed_of_small s a b c _
    apply q2f_small_of_allowed s a b c _ ha
    calc
      cap7_card (q2f_inter u v) = (cap7_decode u ∩ cap7_decode v).card := by
        rw [cap7_card_correct, q2f_decode_inter]
      _ ≤ (cap7_decode u).card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ 2 := by simpa only [cap7_card_correct] using q2f_small_card s a b c u small
  rcases q2f_closed_cases s a b c x hx with sx | ⟨i, rfl⟩
  · exact fromSmall x y sx allowed
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · rw [q2f_inter_comm] at allowed ⊢
      exact fromSmall y _ sy allowed
    · have pair := q2f_generators_pair s a b c h i j
      have right := (q2f_and_true_iff.mp pair).2
      simpa only [allowed, Bool.not_true, Bool.false_or] using right

lemma q2f_encode_union (A B : Finset (Fin 7)) :
    q2f_union (cap7_encode A) (cap7_encode B) = cap7_encode (A ∪ B) := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, cap7_decode_encode]

lemma q2f_encode_inter (A B : Finset (Fin 7)) :
    q2f_inter (cap7_encode A) (cap7_encode B) = cap7_encode (A ∩ B) := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, cap7_decode_encode]

lemma q2f_closed_empty (s : Fin 15) (a b c : Fin 10) :
    q2f_closed s a b c (cap7_encode ∅) = true := by
  apply q2f_closed_of_small s a b c _
  apply q2f_small_of_one s a b c _
  simp only [cap7_card_correct, cap7_decode_encode, Finset.card_empty]
  omega

lemma q2f_closed_singleton (s : Fin 15) (a b c : Fin 10) (i : Fin 7) :
    q2f_closed s a b c (cap7_encode {i}) = true := by
  apply q2f_closed_of_small s a b c _
  apply q2f_small_of_one s a b c _
  simp only [cap7_card_correct, cap7_decode_encode, Finset.card_singleton, le_refl]

lemma q2f_finset_union (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (A B : Finset (Fin 7))
    (ha : q2f_closed s a b c (cap7_encode A) = true)
    (hb : q2f_closed s a b c (cap7_encode B) = true)
    (allowed : q2f_allowed s a b c (cap7_encode (A ∪ B)) = true) :
    q2f_closed s a b c (cap7_encode (A ∪ B)) = true := by
  rw [← q2f_encode_union] at allowed ⊢
  exact q2f_generators_union s a b c h _ _ ha hb allowed

lemma q2f_finset_inter (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (A B : Finset (Fin 7))
    (ha : q2f_closed s a b c (cap7_encode A) = true)
    (hb : q2f_closed s a b c (cap7_encode B) = true)
    (allowed : q2f_allowed s a b c (cap7_encode (A ∩ B)) = true) :
    q2f_closed s a b c (cap7_encode (A ∩ B)) = true := by
  rw [← q2f_encode_inter] at allowed ⊢
  exact q2f_generators_inter s a b c h _ _ ha hb allowed

end PEqualNP.Outside.L_meta_6659_aux
