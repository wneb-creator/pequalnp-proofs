namespace PEqualNP.Outside.L_meta_2592.Binary17.Geometry

lemma first_or_of_seventeen {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) (small : k ≤ 17) :
    ∃ (m : ℕ) (U : Finset Extended.Sig) (v u : Fin 10),
      k = m + 1 ∧ S = insert (pin v) (insert (pin u) U) ∧ v ≠ u ∧
      Extended.bin 1 (pin v) (pin u) ∉ insert (pin v) (insert (pin u) U) ∧
      (∀ a ∈ U, a ∈ Extended.initial) ∧
      Extended.Live true Extended.target m (insert (Extended.bin 1 (pin v) (pin u)) U) := by
  cases k with
  | zero =>
    have lower := binary_floor_seventeen run raw
    omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := run
    obtain ⟨v, rfl⟩ := (pin_mem_iff a).mp (raw a (by simp))
    obtain ⟨u, rfl⟩ := (pin_mem_iff b).mp (raw b (by simp))
    have hne : v ≠ u := by intro h; exact hab (congrArg pin h)
    have hfour : d < 4 := by rcases hd with hd | ⟨_, hd⟩ <;> omega
    have rawU : ∀ a ∈ U, a ∈ Extended.initial := by
      intro a ha
      exact raw a (by simp [ha])
    have hor : d = 1 := by
      by_contra hn
      have lower := first_non_or_floor v u ⟨d, hfour⟩ hne hn rawU fresh tail
      omega
    subst d
    exact ⟨k, U, v, u, rfl, rfl, hne, fresh, rawU, tail⟩

end PEqualNP.Outside.L_meta_2592.Binary17.Geometry
