theorem m9_mask_surjective : Function.Surjective m9_mask := by decide +kernel

theorem m9_mask_injective : Function.Injective m9_mask := by decide +kernel

theorem m9_no_point_constraints_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    (r : Fin 6 → Finset (Fin 3)) (a b : Fin 3) (T : Finset (Fin 3))
    (first : r 0 = {0} ∨ r 0 = {0,1}) (normal : m9_constraints r a b)
    (point : m9_point_constraints r a b T) : False := by
  classical
  choose code encoded using (fun t => m9_mask_surjective (r t))
  obtain ⟨pointCode,pointEncoded⟩ := m9_mask_surjective T
  have vector : (fun t => m9_mask (code t)) = r := funext encoded
  have firstCode : code 0 = 1 ∨ code 0 = 3 := by
    rcases first with first | first
    · apply Or.inl
      apply m9_mask_injective
      rw [encoded,first]
      rfl
    · apply Or.inr
      apply m9_mask_injective
      rw [encoded,first]
      rfl
  have normalCode : m9_normal code a b = true :=
    m9_normal_of_constraints code a b (by simpa only [vector] using normal)
  have pointTrue : m9_pointAllowed code a b pointCode = true :=
    m9_pointAllowed_of_constraints code a b pointCode
      (by simpa only [vector,pointEncoded] using point)
  have pointFalse := certificate code a b pointCode firstCode normalCode
  rw [pointFalse] at pointTrue
  exact Bool.false_ne_true pointTrue
