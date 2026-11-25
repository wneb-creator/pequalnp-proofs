import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_1890.ReadTwice

lemma input_mass_eq (l : List ℕ) (n : ℕ) :
    (l.filter (fun i => decide (i < n))).length = ∑ i ∈ Finset.range n, l.count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : a < n
      · simp [List.count_cons, Finset.sum_add_distrib, ih, ha]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba
          simp [Ne.symm hba]
        · intro hn
          exact (hn (Finset.mem_range.mpr ha)).elim
      · simp [List.count_cons, Finset.sum_add_distrib, ih, ha]
        intro b hb he
        subst b
        exact ha hb

lemma input_mass_two (l : List ℕ) (n : ℕ)
    (twice : ∀ i < n, 2 ≤ l.count i) :
    2 * n ≤ (l.filter (fun i => decide (i < n))).length := by
  rw [input_mass_eq]
  calc
    2 * n = ∑ _i ∈ Finset.range n, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ Finset.range n, l.count i := by
      apply Finset.sum_le_sum
      intro i hi
      exact twice i (Finset.mem_range.mp hi)

end PEqualNP.Outside.L_meta_1890.ReadTwice
