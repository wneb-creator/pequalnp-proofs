import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17926 : (∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11)) := by
  classical
  intro lines f mono positives hempty hcompl points selected hc
  constructor
  · intro hf
    obtain rfl | hne := selected.eq_empty_or_nonempty
    · have absurd := mono points Finset.univ ∅ ∅ (Finset.subset_univ _) (by simp) hf
      simp [hempty] at absurd
    have hone : selected.card = 1 := by
      have hpos := Finset.card_pos.mpr hne
      omega
    obtain ⟨line, rfl⟩ := Finset.card_eq_one.mp hone
    by_contra! hn
    have hs : points ⊆ (lines line)ᶜ := by
      intro point hp
      simpa using hn point hp line (by simp)
    have absurd := mono points (lines line)ᶜ {line} {line} hs (by simp) hf
    simp [hcompl] at absurd
  · rintro ⟨point, hp, line, hl, hinc⟩
    exact mono {point} points {line} selected (by simpa using hp) (by simpa using hl)
      (positives point line hinc)