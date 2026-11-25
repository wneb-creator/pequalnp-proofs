import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma commonFilter_center {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) (p : α) (hp : S p)
    (cross : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → R p v) :
    ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R s i := fun s hs =>
    symm i s (safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs))
  have same : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → u = p := by
    intro u v ha hb hu hv
    apply Classical.byContradiction
    intro hup
    exact free u p i v hup (fun h => hv h.symm)
      ⟨common u hu, safe u v ha hb (Or.inl hu), common p hp,
        cross u v ha hb hu hv⟩
  intro u v ha hb hs
  cases hs with
  | inl hu =>
      by_cases hv : v = i
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr (Or.inl (same u v ha hb hu hv)))
  | inr hv =>
      by_cases hu : u = i
      · exact Or.inl hu
      · exact Or.inr (Or.inr (Or.inr
          (same v u (ha.elim Or.inr Or.inl) (hb.elim Or.inr Or.inl) hv hu)))

lemma commonFilter_twoStars {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) :
    ∃ p, ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R i s := fun s hs =>
    safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs)
  by_cases hA : ∃ p, A p ∧ S p
  · obtain ⟨p, hpA, hpS⟩ := hA
    refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
    intro u v _ hb hu _
    have hnu : ¬ B u := by
      intro hbu
      exact triangle i p u (common p hpS)
        (safe p u (Or.inl hpA) (Or.inr hbu) (Or.inl hpS)) (common u hu)
    exact safe p v (Or.inl hpA) (Or.inr (hb.resolve_left hnu)) (Or.inl hpS)
  · by_cases hB : ∃ p, B p ∧ S p
    · obtain ⟨p, hpB, hpS⟩ := hB
      refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
      intro u v ha _ hu _
      have hnu : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
      exact safe p v (Or.inr (ha.resolve_left hnu)) (Or.inl hpB) (Or.inl hpS)
    · by_cases hS : ∃ p, S p
      · obtain ⟨p, hpS⟩ := hS
        refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
        intro u v ha hb hu _
        have hna : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
        have hnb : ¬ B u := fun hbu => hB ⟨u, hbu, hu⟩
        exact safe p v (Or.inr (ha.resolve_left hna))
          (Or.inr (hb.resolve_left hnb)) (Or.inl hpS)
      · refine ⟨i, ?_⟩
        intro u v _ _ hs
        exact hs.elim (fun hu => False.elim (hS ⟨u, hu⟩))
          (fun hv => False.elim (hS ⟨v, hv⟩))

end PEqualNP.Outside.L_meta_2732_aux
