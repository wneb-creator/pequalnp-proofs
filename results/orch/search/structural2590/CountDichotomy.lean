import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

lemma count_dichotomy (s : ℕ) (o : Fin s) (r : Fin 10 → ℕ) (u : Fin s → ℕ)
    (budget : s ≤ 19) (balance : (∑ i, r i) + (∑ j, u j) = 2 * s)
    (live : ∀ j, j ≠ o → 1 ≤ u j) (twice : ∀ i, 2 ≤ r i) :
    s = 19 ∧ (∀ i, r i = 2) ∧ u o = 0 ∧ ∀ j, j ≠ o → u j = 1 := by
  classical
  let base : Fin s → ℕ := fun j => if j = o then 0 else 1
  have base_sum : (∑ j, base j) = s - 1 := by
    simp [base, Finset.sum_ite, Finset.filter_ne']
  have base_le : ∀ j, base j ≤ u j := by
    intro j
    by_cases hj : j = o
    · simp [base, hj]
    · simpa [base, hj] using live j hj
  have rmin : 20 ≤ ∑ i, r i := by
    calc
      20 = ∑ _ : Fin 10, 2 := by norm_num
      _ ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ => twice i)
  have umin : s - 1 ≤ ∑ j, u j := by
    rw [← base_sum]
    exact Finset.sum_le_sum (fun j _ => base_le j)
  have spos : 0 < s := by have := o.isLt; omega
  have size : s = 19 := by omega
  have rsum : (∑ i, r i) = 20 := by omega
  have usum : (∑ j, u j) = s - 1 := by omega
  have requal : ∀ i, r i = 2 := by
    have eq : (∑ _ : Fin 10, 2) = ∑ i, r i := by simpa using rsum.symm
    have each := (Finset.sum_eq_sum_iff_of_le (fun i _ => twice i)).mp eq
    exact fun i => (each i (Finset.mem_univ i)).symm
  have uequal : ∀ j, u j = base j := by
    have eq : (∑ j, base j) = ∑ j, u j := base_sum.trans usum.symm
    have each := (Finset.sum_eq_sum_iff_of_le (fun j _ => base_le j)).mp eq
    exact fun j => (each j (Finset.mem_univ j)).symm
  exact ⟨size, requal, by simp [uequal, base], fun j hj => by simp [uequal, base, hj]⟩

end PEqualNP.Outside.L_meta_2590
