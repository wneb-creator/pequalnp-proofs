
lemma canonicalize_first_used (d : Fin 4) (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live true target k S)
    (used : bin d.val (pins.getD a.val zero) (pins.getD b.val zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin d.val (pins.getD a.val zero) (pins.getD b.val zero)]) :
    ∃ (j : Fin 2) (U : Finset Sig), Live true target k U ∧
      bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero) ∈ U ∧
      ∀ v ∈ U, v ∈ pins ++ [bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero)] := by
  classical
  obtain ⟨p, hzero, hsecond, hp⟩ := normalize_pair a b hab
  let j : Fin 2 := if adjacent a b then 0 else 1
  let q := p.symm
  have hqa : q a = 0 := by
    dsimp [q]
    rw [← hzero, Equiv.symm_apply_apply]
  have hqb : (q b).val = j.val + 1 := by
    dsimp [q]
    rw [← hsecond, Equiv.symm_apply_apply]
    cases h : adjacent a b <;> simp [j, h]
  have hq : ∀ u v, adjacent (q u) (q v) = adjacent u v := by
    intro u v
    simpa only [q, Equiv.apply_symm_apply] using (hp (p.symm u) (p.symm v)).symm
  refine ⟨j, S.image (renameVertices q), ?_, ?_, ?_⟩
  · simpa only [renameVertices_target q hq] using live_renameVertices run q
  · apply Finset.mem_image.mpr
    refine ⟨bin d.val (pins.getD a.val zero) (pins.getD b.val zero), used, ?_⟩
    rw [renameVertices_bin, renameVertices_pin, renameVertices_pin, hqa, hqb]
    rfl
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hw' := raw w hw
    simp only [List.mem_append, List.mem_singleton] at hw' ⊢
    rcases hw' with hpin | rfl
    · exact Or.inl (renameVertices_mem_pins q hpin)
    · right
      rw [renameVertices_bin, renameVertices_pin, renameVertices_pin, hqa, hqb]
      rfl
