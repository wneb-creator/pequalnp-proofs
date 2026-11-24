import Mathlib

namespace PEqualNP.Outside.L_meta_3787

lemma incidence_zero (q : Fin 13) :
    (0 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      q = 0 ∨ q = 1 ∨ q = 3 ∨ q = 9 := by
  fin_cases q <;> decide

lemma incidence_one (q : Fin 13) :
    (1 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      q = 0 ∨ q = 2 ∨ q = 8 ∨ q = 12 := by
  fin_cases q <;> decide

lemma incidence_three (q : Fin 13) :
    (3 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      q = 0 ∨ q = 6 ∨ q = 10 ∨ q = 11 := by
  fin_cases q <;> decide

lemma incidence_nine (q : Fin 13) :
    (9 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
      q = 0 ∨ q = 4 ∨ q = 5 ∨ q = 7 := by
  fin_cases q <;> decide

lemma point_selected (p : Fin 13) :
    p.val ∈ ([0, 1, 3, 9] : List ℕ) ↔
      p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by
  fin_cases p <;> decide

lemma incidence_term_iff (s t : Finset (Fin 13)) :
    (∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧
      ∃ q ∈ t, (p.val + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ↔
    (0 ∈ s ∧ (0 ∈ t ∨ 1 ∈ t ∨ 3 ∈ t ∨ 9 ∈ t)) ∨
    (1 ∈ s ∧ (0 ∈ t ∨ 2 ∈ t ∨ 8 ∈ t ∨ 12 ∈ t)) ∨
    (3 ∈ s ∧ (0 ∈ t ∨ 6 ∈ t ∨ 10 ∈ t ∨ 11 ∈ t)) ∨
    (9 ∈ s ∧ (0 ∈ t ∨ 4 ∈ t ∨ 5 ∈ t ∨ 7 ∈ t)) := by
  have select (P Q : Fin 13 → Prop) (a : Fin 13) :
      (∃ p, P p ∧ p = a ∧ Q p) ↔ P a ∧ Q a := by
    aesop
  simp_rw [point_selected]
  simp only [or_and_right, and_or_left, exists_or, select]
  change ((0 ∈ s ∧ ∃ q ∈ t, (0 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
    (1 ∈ s ∧ ∃ q ∈ t, (1 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
    (3 ∈ s ∧ ∃ q ∈ t, (3 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
    (9 ∈ s ∧ ∃ q ∈ t, (9 + q.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) ↔ _
  simp_rw [incidence_zero, incidence_one, incidence_three, incidence_nine]
  simp only [and_or_left, exists_or, exists_eq_right]

end PEqualNP.Outside.L_meta_3787
