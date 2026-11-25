import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux

lemma sum_wire_counts {N : ℕ} (L : List (Fin N)) :
    (∑ w, L.count w) = L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ck (w : Fin N) : (a :: l).count w = l.count w + if w = a then 1 else 0 := by
      by_cases h : w = a
      · subst w
        simp
      · simp [h, Ne.symm h]
    simp [ck, Finset.sum_add_distrib, ih]

lemma single_use_primary {n s : ℕ} (parents : Fin s → List (Fin (n + s)))
    (binary : ∀ j, (parents j).length ≤ 2)
    (unary : ∃ j, (parents j).length ≤ 1)
    (live : ∀ j : Fin s, j.val + 1 < s →
      1 ≤ ∑ k, (parents k).count (Fin.natAdd n j))
    (small : s < 2 * n) :
    ∃ i : Fin n, (∑ j, (parents j).count (Fin.castAdd s i)) ≤ 1 := by
  classical
  obtain ⟨u, hu⟩ := unary
  have spos : 0 < s := Nat.zero_lt_of_lt u.isLt
  let uses (w : Fin (n + s)) := ∑ j, (parents j).count w
  have slots : (∑ w, uses w) = ∑ j, (parents j).length := by
    simp only [uses]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_wire_counts (parents j))
  have capacity : (∑ j, (parents j).length) + 1 ≤ 2 * s := by
    have cap : ∀ j : Fin s, (parents j).length + (if j = u then 1 else 0) ≤ 2 := by
      intro j
      by_cases e : j = u
      · subst j
        simp only [ite_true]
        omega
      · simp only [e, ite_false, Nat.add_zero]
        exact binary j
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => cap j)
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using h
  have internal : s ≤ (∑ j : Fin s, uses (Fin.natAdd n j)) + 1 := by
    let last : Fin s := ⟨s - 1, by omega⟩
    have each : ∀ j : Fin s,
        1 ≤ uses (Fin.natAdd n j) + (if j = last then 1 else 0) := by
      intro j
      by_cases e : j = last
      · simp [e]
      · have hlt : j.val + 1 < s := by
          have hj := j.isLt
          have hne : j.val ≠ s - 1 := by
            intro eq
            apply e
            apply Fin.ext
            exact eq
          omega
        simpa [e, uses] using live j hlt
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
    simpa [Finset.sum_add_distrib] using h
  by_contra! frequent
  have primary : 2 * n ≤ ∑ i : Fin n, uses (Fin.castAdd s i) := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => show 2 ≤ uses (Fin.castAdd s i) by exact frequent i)
    simpa [Nat.mul_comm] using h
  rw [Fin.sum_univ_add] at slots
  omega

end PEqualNP.Outside.L_meta_2592_aux
