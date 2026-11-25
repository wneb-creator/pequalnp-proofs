namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

lemma q2f_and_true_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

lemma q2f_mem_iff (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_mem s a b c m = true ↔ m ∈ q2f_codes s a b c := by
  simp only [q2f_mem,q2f_codes,Bool.or_eq_true,decide_eq_true_eq,
    Finset.mem_insert,Finset.mem_singleton,or_assoc]

lemma q2f_mem_exists (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_mem s a b c m = true) : ∃ i : Fin 10, m = q2f_raw s a b c i := by
  simp only [q2f_mem,Bool.or_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩
  · exact ⟨4,h⟩
  · exact ⟨5,h⟩
  · exact ⟨6,h⟩
  · exact ⟨7,h⟩
  · exact ⟨8,h⟩
  · exact ⟨9,h⟩

lemma q2f_outside_correct : ∀ m : Fin 128,
    q2f_outside m = true ↔ (cap7_decode m).card = 2 ∧
      ∀ i : Fin 3, ¬ cap7_decode m ⊆ cap7_decode (q2f_tripleCode i) := by
  have coded : ∀ m : Fin 128, q2f_outside m = true ↔ cap7_card m = 2 ∧
      ∀ i : Fin 3, q2f_sub m (q2f_tripleCode i) = false := by decide +kernel
  intro m
  rw [coded,cap7_card_correct]
  constructor
  · rintro ⟨card,sub⟩
    refine ⟨card,?_⟩
    intro i hi
    have yes := (q2f_sub_iff _ _).mpr hi
    have no := sub i
    simp only [yes,Bool.true_eq_false] at no
  · rintro ⟨card,sub⟩
    refine ⟨card,?_⟩
    intro i
    cases hi : q2f_sub m (q2f_tripleCode i)
    · rfl
    · exact False.elim (sub i ((q2f_sub_iff _ _).mp hi))

lemma q2f_small_card (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_small s a b c m = true) : cap7_card m ≤ 2 := by
  simp only [q2f_small,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨h,_⟩ <;> omega

lemma q2f_small_of_one (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : cap7_card m ≤ 1) : q2f_small s a b c m = true := by
  simp only [q2f_small,h,decide_true,Bool.true_or]

lemma q2f_small_of_allowed (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_allowed s a b c m = true) (low : cap7_card m ≤ 2) :
    q2f_small s a b c m = true := by
  rcases q2f_or_true_iff.mp h with small | member
  · exact small
  · by_cases one : cap7_card m ≤ 1
    · exact q2f_small_of_one s a b c m one
    · have two : cap7_card m = 2 := by omega
      simp only [q2f_small,two,member,decide_true,Bool.or_true,Bool.and_true]

lemma q2f_small_downward (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hy : q2f_small s a b c y = true) (sub : cap7_decode x ⊆ cap7_decode y) :
    q2f_small s a b c x = true := by
  have upper := q2f_small_card s a b c y hy
  have lower : cap7_card x ≤ cap7_card y := by
    rw [cap7_card_correct,cap7_card_correct]
    exact Finset.card_le_card sub
  by_cases one : cap7_card x ≤ 1
  · exact q2f_small_of_one s a b c x one
  · have equal : cap7_decode x = cap7_decode y :=
      Finset.eq_of_subset_of_card_le sub (by rw [← cap7_card_correct,← cap7_card_correct]; omega)
    exact (cap7_decode_injective equal) ▸ hy

lemma q2f_small_union_seed (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hx : q2f_small s a b c x = true) (hy : q2f_small s a b c y = true)
    (large : 3 ≤ cap7_card (q2f_union x y)) : q2f_seed s a b c (q2f_union x y) = true := by
  obtain ⟨i,hi⟩ := q2f_bridge_small_complete x (q2f_small_card s a b c x hx)
  obtain ⟨j,hj⟩ := q2f_bridge_small_complete y (q2f_small_card s a b c y hy)
  have coverage := q2f_cut_cover i j (by simpa only [hi,hj] using large)
  simp only [hi,hj] at coverage
  obtain ⟨card,k,parts⟩ := coverage
  have both : q2f_small s a b c (q2f_cut (q2f_union x y) k 0) = true ∧
      q2f_small s a b c (q2f_cut (q2f_union x y) k 1) = true := by
    rcases parts with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact ⟨q2f_small_downward s a b c _ x hx ((q2f_sub_iff _ _).mp h0),
        q2f_small_downward s a b c _ y hy ((q2f_sub_iff _ _).mp h1)⟩
    · exact ⟨q2f_small_downward s a b c _ y hy ((q2f_sub_iff _ _).mp h0),
        q2f_small_downward s a b c _ x hx ((q2f_sub_iff _ _).mp h1)⟩
  simp only [q2f_seed,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  refine ⟨card,?_⟩
  fin_cases k
  · exact Or.inl (Or.inl both)
  · exact Or.inl (Or.inr both)
  · exact Or.inr both

lemma q2f_grow_union (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hy : q2f_small s a b c y = true) : q2f_grow s a b c x (q2f_union x y) = true := by
  apply q2f_and_true_iff.mpr
  constructor
  · apply (q2f_sub_iff _ _).mpr
    rw [q2f_decode_union]
    exact Finset.subset_union_left
  · apply q2f_small_downward s a b c _ y hy
    rw [q2f_decode_diff,q2f_decode_union]
    intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_union] at hi
    tauto

lemma q2f_closed_of_small (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_small s a b c m = true) : q2f_closed s a b c m = true := by
  simp only [q2f_closed,h,Bool.true_or]

lemma q2f_closed_known (s : Fin 15) (a b c : Fin 10) (j : Fin 3) :
    q2f_closed s a b c (q2f_known s a b c j) = true := by
  simp only [q2f_closed,Bool.or_eq_true,decide_eq_true_eq]
  fin_cases j <;> tauto

lemma q2f_closed_cases (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_closed s a b c m = true) :
    q2f_small s a b c m = true ∨ ∃ j : Fin 3, m = q2f_known s a b c j := by
  simp only [q2f_closed,Bool.or_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with small | h | h | h
  · exact Or.inl small
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

lemma q2f_generators_node (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (i : Fin 10) : q2f_node s a b c i = true := by
  simp only [q2f_generators,Bool.and_eq_true,and_assoc] at h
  rcases h with ⟨n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,_,_,_⟩
  fin_cases i
  · exact n0
  · exact n1
  · exact n2
  · exact n3
  · exact n4
  · exact n5
  · exact n6
  · exact n7
  · exact n8
  · exact n9

lemma q2f_closed_seed (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (seed : q2f_seed s a b c m = true) :
    q2f_closed s a b c m = true := by
  rcases q2f_or_true_iff.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    simpa only [q2f_node,← hi,seed,Bool.not_true,Bool.false_and,Bool.or_false] using node

lemma q2f_closed_grow (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (j : Fin 3)
    (grow : q2f_grow s a b c (q2f_known s a b c j) m = true) :
    q2f_closed s a b c m = true := by
  rcases q2f_or_true_iff.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    simp only [q2f_node,← hi,Bool.or_eq_true,Bool.and_eq_true] at node
    rcases node with closed | ⟨⟨⟨_,g0⟩,g1⟩,g2⟩
    · exact closed
    · fin_cases j
      · change q2f_grow s a b c (q2f_known s a b c 0) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g0
      · change q2f_grow s a b c (q2f_known s a b c 1) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g1
      · change q2f_grow s a b c (q2f_known s a b c 2) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g2

end PEqualNP.Outside.L_meta_6659_aux
