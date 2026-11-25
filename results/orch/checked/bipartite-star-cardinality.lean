import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896.BipartiteStar

variable {α β : Type} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
lemma common_endpoint (S : Finset (α × β)) (hne : S.Nonempty)
    (hpair : ∀ e ∈ S, ∀ f ∈ S, e.1 = f.1 ∨ e.2 = f.2) :
    (∃ a, ∀ e ∈ S, e.1 = a) ∨ (∃ b, ∀ e ∈ S, e.2 = b) := by
  obtain ⟨e, he⟩ := hne
  by_cases hx : ∃ f ∈ S, f.1 ≠ e.1
  · obtain ⟨f, hf, hfe⟩ := hx
    have hfb : f.2 = e.2 := (hpair f hf e he).resolve_left hfe
    right
    refine ⟨e.2, ?_⟩
    intro g hg
    rcases hpair g hg e he with hga | hgb
    · rcases hpair g hg f hf with hga' | hgb'
      · exact False.elim (hfe (hga'.symm.trans hga))
      · exact hgb'.trans hfb
    · exact hgb
  · left
    refine ⟨e.1, ?_⟩
    intro f hf
    by_contra hfe
    exact hx ⟨f, hf, hfe⟩

lemma card_le (S : Finset (α × β)) (d : ℕ)
    (hpair : ∀ e ∈ S, ∀ f ∈ S, e.1 = f.1 ∨ e.2 = f.2)
    (ha : ∀ a, (S.filter fun e => e.1 = a).card ≤ d)
    (hb : ∀ b, (S.filter fun e => e.2 = b).card ≤ d) :
    S.card ≤ d := by
  by_cases hne : S.Nonempty
  · rcases common_endpoint S hne hpair with ⟨a, ha'⟩ | ⟨b, hb'⟩
    · have he : (S.filter fun e => e.1 = a) = S := Finset.filter_eq_self.2 ha'
      simpa [he] using ha a
    · have he : (S.filter fun e => e.2 = b) = S := Finset.filter_eq_self.2 hb'
      simpa [he] using hb b
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

lemma card_le_ambient (E S : Finset (α × β)) (hsub : S ⊆ E) (d : ℕ)
    (hpair : ∀ e ∈ S, ∀ f ∈ S, e.1 = f.1 ∨ e.2 = f.2)
    (ha : ∀ a, (E.filter fun e => e.1 = a).card ≤ d)
    (hb : ∀ b, (E.filter fun e => e.2 = b).card ≤ d) :
    S.card ≤ d := by
  apply card_le S d hpair
  · intro a
    apply le_trans (Finset.card_le_card ?_) (ha a)
    intro e he
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · intro b
    apply le_trans (Finset.card_le_card ?_) (hb b)
    intro e he
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

end PEqualNP.Outside.L_meta_1896.BipartiteStar
