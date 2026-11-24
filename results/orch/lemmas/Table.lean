import Mathlib

theorem table : ∀ u v : Fin 25,
    (u.val < 12 ∧ 12 ≤ v.val ∧
      (u.val + v.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ↔
    u.val < 12 ∧ 12 ≤ v.val ∧
      Fin.ofNat 13 (u.val + 1) + Fin.ofNat 13 (v.val - 12) ∈
        ({0, 1, 3, 9} : Finset (Fin 13)) := by
  intro u v
  by_cases hu : u.val < 12
  · by_cases hv : 12 ≤ v.val
    · simp only [hu, hv, true_and]
      have hval : (Fin.ofNat 13 (u.val + 1) +
          Fin.ofNat 13 (v.val - 12)).val = (u.val + v.val + 2) % 13 := by
        change ((u.val + 1) % 13 + (v.val - 12) % 13) % 13 = _
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      change (_ = 0 ∨ _ = 1 ∨ _ = 3 ∨ _ = 9) ↔
        (_ = 0 ∨ _ = 1 ∨ _ = 3 ∨ _ = 9)
      rw [hval]
    · simp [hv]
  · simp [hu]
