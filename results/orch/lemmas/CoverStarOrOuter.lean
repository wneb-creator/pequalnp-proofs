import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.CoverStarOrOuter

theorem twoCover_star_or_outer {α : Type*} (T : α → α → Prop)
    (symm : ∀ u v, T u v → T v u) (irrefl : ∀ u, ¬ T u u)
    (c d : α) (cover : ∀ u v, T u v → u = c ∨ v = c ∨ u = d ∨ v = d) :
    (∀ u v, T u v → u = c ∨ v = c) ∨
    (∀ u v, T u v → u = d ∨ v = d) ∨
    ∃ l r, T l c ∧ T d r ∧ ¬ T l r := by
  classical
  by_cases hc : ∀ u v, T u v → u = c ∨ v = c
  · exact Or.inl hc
  by_cases hd : ∀ u v, T u v → u = d ∨ v = d
  · exact Or.inr (Or.inl hd)
  right
  right
  have hleft : ∃ l, T l c ∧ l ≠ d := by
    push Not at hd
    obtain ⟨u, v, huv, hud, hvd⟩ := hd
    rcases cover u v huv with h | h | h | h
    · exact ⟨v, h ▸ symm u v huv, hvd⟩
    · exact ⟨u, h ▸ huv, hud⟩
    · exact (hud h).elim
    · exact (hvd h).elim
  have hright : ∃ r, T d r ∧ r ≠ c := by
    push Not at hc
    obtain ⟨u, v, huv, huc, hvc⟩ := hc
    rcases cover u v huv with h | h | h | h
    · exact (huc h).elim
    · exact (hvc h).elim
    · exact ⟨v, h ▸ huv, hvc⟩
    · exact ⟨u, h ▸ symm u v huv, huc⟩
  obtain ⟨l, hl, hld⟩ := hleft
  obtain ⟨r, hr, hrc⟩ := hright
  have hlc : l ≠ c := fun h => irrefl c (h ▸ hl)
  have hrd : r ≠ d := fun h => irrefl d (h ▸ hr)
  refine ⟨l, r, hl, hr, ?_⟩
  intro hlr
  rcases cover l r hlr with h | h | h | h
  · exact hlc h
  · exact hrc h
  · exact hld h
  · exact hrd h

end PEqualNP.Outside.L_meta_2732_aux.CoverStarOrOuter
