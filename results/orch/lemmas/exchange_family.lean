import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.ExchangeFamily

theorem filtered_rectangles (xs : List (Bool × Bool)) (a d : Bool)
    (ha : ∀ p ∈ xs, a = true → p.1 = true)
    (hd : ∀ p ∈ xs, d = true → p.2 = true) :
    (xs.any (fun p => p.1 && p.2) && (a || d)) =
      ((a && xs.any Prod.snd) || (d && xs.any Prod.fst)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨⟨p, hp, h1, h2⟩, had⟩
    rcases had with ha' | hd'
    · exact Or.inl ⟨ha', p, hp, h2⟩
    · exact Or.inr ⟨hd', p, hp, h1⟩
  · rintro (⟨ha', p, hp, h2⟩ | ⟨hd', p, hp, h1⟩)
    · exact ⟨⟨p, hp, ha p hp ha', h2⟩, Or.inl ha'⟩
    · exact ⟨⟨p, hp, h1, hd p hp hd'⟩, Or.inr hd'⟩

theorem nonempty_gate_budget (k : ℕ) (hk : 0 < k) :
    k + (k - 1) + 1 + 1 = 2 + 2 * (k - 1) + 1 := by
  omega

end PEqualNP.Outside.L_meta_1031_aux.ExchangeFamily
