lemma q2_semantic_contradiction
    (certificate : ∀ c : Fin 34, ∀ a b d : Fin 33, q2_bad c a b d = false)
    (c : Fin 34) (a b d : Fin 33)
    (budget : ∀ t : Fin 7,
      (q2_bit (q2_ctx c 1) t).toNat + (q2_bit (q2_ctx c 2) t).toNat +
      (q2_bit (q2_ctx c 3) t).toNat + (q2_bit (q2_ctx c 4) t).toNat +
      (if t = 0 then 0 else 1) ≤
        2 + (q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) t).card)
    (labels : ∀ i : Fin 4, ∀ x t : Fin 7,
      x ∈ q2_decode (q2_nb i) →
      q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) x ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) t →
      ((q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) x).Nonempty ∨
        q2_shared x t = true) → t ∈ q2_decode (q2_ctx c i.succ))
    (center :
      (q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0).card +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 1 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 2 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 3 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 4 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 5 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 6 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) ≤ 5) :
    False := by
  classical
  let u := q2_unit c a
  let v := q2_unit c b
  let w := q2_unit c d
  have hb (t : Fin 7) : q2_budget_at c u v w t = true := by
    simpa only [q2_budget_at, decide_eq_true_eq, q2_count_card] using budget t
  have budgetB : q2_budget c u v w = true := by
    simp only [q2_budget, hb, Bool.and_true]
  have or_split (x y : Bool) (h : (x || y) = true) : x = true ∨ y = true := by
    simpa only [Bool.or_eq_true] using h
  have force (i : Fin 4) (x t : Fin 7) (hx : x ∈ q2_decode (q2_nb i))
      (hf : q2_force u v w x t = true) : q2_bit (q2_ctx c i.succ) t = true := by
    apply (q2_bit_mem _ _).mpr
    have hf' : q2_sub u v w x t = true ∧
        (!q2_empty u v w x || q2_shared x t) = true := by
      simpa only [q2_force, Bool.and_eq_true] using hf
    have hs := (q2_sub_iff u v w x t).mp hf'.1
    apply labels i x t hx hs
    rcases or_split _ _ hf'.2 with hn | hshared
    · left
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have he' := (q2_empty_iff u v w x).mpr he
      simp only [he', Bool.not_true, Bool.false_eq_true] at hn
    · exact Or.inr hshared
  have row (i : Fin 4) (t : Fin 7) (hr : q2_row u v w i t = true) :
      q2_bit (q2_ctx c i.succ) t = true := by
    fin_cases i
    · change (q2_force u v w 0 t || q2_force u v w 1 t || q2_force u v w 3 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 0 0 t (by decide +kernel) hr
        · exact force 0 1 t (by decide +kernel) hr
      · exact force 0 3 t (by decide +kernel) hr
    · change (q2_force u v w 0 t || q2_force u v w 2 t || q2_force u v w 6 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 1 0 t (by decide +kernel) hr
        · exact force 1 2 t (by decide +kernel) hr
      · exact force 1 6 t (by decide +kernel) hr
    · change (q2_force u v w 1 t || q2_force u v w 5 t || q2_force u v w 6 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 2 1 t (by decide +kernel) hr
        · exact force 2 5 t (by decide +kernel) hr
      · exact force 2 6 t (by decide +kernel) hr
    · change (q2_force u v w 0 t || q2_force u v w 4 t || q2_force u v w 5 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 3 0 t (by decide +kernel) hr
        · exact force 3 4 t (by decide +kernel) hr
      · exact force 3 5 t (by decide +kernel) hr
  have entry (i : Fin 4) (t : Fin 7) :
      (!q2_row u v w i t || q2_bit (q2_ctx c i.succ) t) = true := by
    cases hrow : q2_row u v w i t
    · simp only [Bool.not_false, Bool.true_or]
    · simpa only [Bool.not_true, Bool.false_or] using row i t hrow
  have labelsB : q2_labels c u v w = true := by
    have e0 : ∀ t : Fin 7, (!q2_row u v w 0 t || q2_bit (q2_ctx c 1) t) = true := entry 0
    have e1 : ∀ t : Fin 7, (!q2_row u v w 1 t || q2_bit (q2_ctx c 2) t) = true := entry 1
    have e2 : ∀ t : Fin 7, (!q2_row u v w 2 t || q2_bit (q2_ctx c 3) t) = true := entry 2
    have e3 : ∀ t : Fin 7, (!q2_row u v w 3 t || q2_bit (q2_ctx c 4) t) = true := entry 3
    simp only [q2_labels, e0, e1, e2, e3, Bool.and_true]
  have subcount (x t : Fin 7) : (q2_sub u v w x t).toNat =
      if q2_res u v w x ⊆ q2_res u v w t then 1 else 0 := by
    cases hs : q2_sub u v w x t
    · have hn : ¬ q2_res u v w x ⊆ q2_res u v w t := by
        intro hh
        have htrue := (q2_sub_iff u v w x t).mpr hh
        simp only [hs, Bool.false_eq_true] at htrue
      simp only [hn, ite_false, Bool.toNat_false]
    · simp only [(q2_sub_iff u v w x t).mp hs, ite_true, Bool.toNat_true]
  have centerB : q2_center u v w = true := by
    simpa only [q2_center, decide_eq_true_eq, q2_count_card, subcount] using center
  have bad : q2_bad c a b d = true := by
    change q2_budget c u v w && q2_center u v w && q2_labels c u v w = true
    simp only [budgetB, centerB, labelsB, Bool.and_true, Bool.true_and, decide_true]
  have impossible := certificate c a b d
  rw [bad] at impossible
  exact Bool.noConfusion impossible
