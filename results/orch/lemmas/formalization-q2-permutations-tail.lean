lemma q2_force_swap (u v w : Fin 128) (x t : Fin 7) :
    q2_force u v w x t = q2_force v u w x t := by
  simp only [q2_force, q2_sub_swap u v w, q2_empty_swap u v w]

lemma q2_row_swap (u v w : Fin 128) (i : Fin 4) (t : Fin 7) :
    q2_row u v w i t = q2_row v u w i t := by
  simp only [q2_row, q2_force_swap u v w]

lemma q2_budget_at_swap (c : Fin 34) (u v w : Fin 128) (t : Fin 7) :
    q2_budget_at c u v w t = q2_budget_at c v u w t := by
  simp only [q2_budget_at, q2_count_swap u v w]

lemma q2_budget_swap (c : Fin 34) (u v w : Fin 128)  :
    q2_budget c u v w = q2_budget c v u w := by
  simp only [q2_budget, q2_budget_at_swap c u v w]

lemma q2_center_swap (u v w : Fin 128)  :
    q2_center u v w = q2_center v u w := by
  simp only [q2_center, q2_count_swap u v w, q2_sub_swap u v w]

lemma q2_labels_swap (c : Fin 34) (u v w : Fin 128)  :
    q2_labels c u v w = q2_labels c v u w := by
  simp only [q2_labels, q2_row_swap u v w]

lemma q2_bad_swap (c : Fin 34) (a b d : Fin 33) :
    q2_bad c a b d = q2_bad c b a d := by
  simp only [q2_bad, q2_budget_swap c (q2_unit c a) (q2_unit c b) (q2_unit c d),
    q2_center_swap (q2_unit c a) (q2_unit c b) (q2_unit c d), q2_labels_swap c (q2_unit c a) (q2_unit c b) (q2_unit c d)]

lemma q2_force_rotate (u v w : Fin 128) (x t : Fin 7) :
    q2_force u v w x t = q2_force v w u x t := by
  simp only [q2_force, q2_sub_rotate u v w, q2_empty_rotate u v w]

lemma q2_row_rotate (u v w : Fin 128) (i : Fin 4) (t : Fin 7) :
    q2_row u v w i t = q2_row v w u i t := by
  simp only [q2_row, q2_force_rotate u v w]

lemma q2_budget_at_rotate (c : Fin 34) (u v w : Fin 128) (t : Fin 7) :
    q2_budget_at c u v w t = q2_budget_at c v w u t := by
  simp only [q2_budget_at, q2_count_rotate u v w]

lemma q2_budget_rotate (c : Fin 34) (u v w : Fin 128)  :
    q2_budget c u v w = q2_budget c v w u := by
  simp only [q2_budget, q2_budget_at_rotate c u v w]

lemma q2_center_rotate (u v w : Fin 128)  :
    q2_center u v w = q2_center v w u := by
  simp only [q2_center, q2_count_rotate u v w, q2_sub_rotate u v w]

lemma q2_labels_rotate (c : Fin 34) (u v w : Fin 128)  :
    q2_labels c u v w = q2_labels c v w u := by
  simp only [q2_labels, q2_row_rotate u v w]

lemma q2_bad_rotate (c : Fin 34) (a b d : Fin 33) :
    q2_bad c a b d = q2_bad c b d a := by
  simp only [q2_bad, q2_budget_rotate c (q2_unit c a) (q2_unit c b) (q2_unit c d),
    q2_center_rotate (q2_unit c a) (q2_unit c b) (q2_unit c d), q2_labels_rotate c (q2_unit c a) (q2_unit c b) (q2_unit c d)]

lemma q2_ordered_from_blocks
    (blocks : ∀ c : Fin 34, ∀ g : Fin 11, ∀ r : Fin 3, ∀ b d : Fin 33,
      q2_ordered_bad c (q2_index g r) b d = false) (c : Fin 34) (a b d : Fin 33)
    (hab : a ≤ b) (hbd : b ≤ d) : q2_bad c a b d = false := by
  let g : Fin 11 := ⟨a.val / 3, by omega⟩
  let r : Fin 3 := ⟨a.val % 3, by omega⟩
  have ha : q2_index g r = a := by
    apply Fin.ext
    simp only [q2_index, g, r]
    omega
  have h := blocks c g r b d
  rw [ha] at h
  simpa only [q2_ordered_bad, hab, hbd, and_self, decide_true, Bool.true_and] using h

lemma q2_sorting_from_ordered
    (ordered : ∀ c : Fin 34, ∀ a b d : Fin 33,
      a ≤ b → b ≤ d → q2_bad c a b d = false) (c : Fin 34) (a b d : Fin 33) : q2_bad c a b d = false := by
  by_cases hab : a ≤ b
  · by_cases hbd : b ≤ d
    · exact ordered c a b d hab hbd
    · by_cases had : a ≤ d
      · have h := ordered c a d b had (by omega)
        rw [q2_bad_swap, q2_bad_rotate] at h
        exact h
      · have h := ordered c d a b (by omega) hab
        rw [q2_bad_rotate] at h
        exact h
  · by_cases had : a ≤ d
    · have h := ordered c b a d (by omega) had
      rw [q2_bad_swap] at h
      exact h
    · by_cases hbd : b ≤ d
      · have h := ordered c b d a hbd (by omega)
        rw [← q2_bad_rotate] at h
        exact h
      · have h := ordered c d b a (by omega) (by omega)
        rw [q2_bad_swap, ← q2_bad_rotate] at h
        exact h

