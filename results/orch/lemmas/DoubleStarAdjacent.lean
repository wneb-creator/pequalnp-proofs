import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma twoCover_oneSmall {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (irrefl : ∀ u, ¬ R u u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (p q : α) (hpq : p ≠ q) (hnpq : ¬ R p q)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    (∀ a b, R p a → R p b → a = b) ∨
    (∀ a b, R q a → R q b → a = b) := by
  have cross' : ∀ a c, R p a → R q c → R p c ∨ R q a := by
    intro a c hpa hqc
    have hanp : a ≠ p := fun h => irrefl p (h ▸ hpa)
    have hanq : a ≠ q := fun h => hnpq (h ▸ hpa)
    have hcnp : c ≠ p := fun h => hnpq (symm q p (h ▸ hqc))
    have hcnq : c ≠ q := fun h => irrefl q (h ▸ hqc)
    have hnac : ¬ R a c := by
      intro hac
      rcases cover a c hac with h | h | h | h
      · exact hanp h
      · exact hcnp h
      · exact hanq h
      · exact hcnq h
    rcases cross p a q c hpa hqc with h | h | h | h
    · exact False.elim (hnpq h)
    · exact Or.inl h
    · exact Or.inr (symm a q h)
    · exact False.elim (hnac h)
  by_cases hp : ∃ a b, R p a ∧ R p b ∧ a ≠ b
  · obtain ⟨a, b, hpa, hpb, hab⟩ := hp
    refine Or.inr ?_
    intro c d hqc hqd
    apply Classical.byContradiction
    intro hcd
    by_cases hqa : R q a
    · by_cases hqb : R q b
      · exact free p q a b hpq hab ⟨hpa, hpb, hqa, hqb⟩
      · exact free p q c d hpq hcd
          ⟨(cross' b c hpb hqc).resolve_right hqb,
            (cross' b d hpb hqd).resolve_right hqb, hqc, hqd⟩
    · exact free p q c d hpq hcd
        ⟨(cross' a c hpa hqc).resolve_right hqa,
          (cross' a d hpa hqd).resolve_right hqa, hqc, hqd⟩
  · refine Or.inl ?_
    intro a b hpa hpb
    exact Classical.byContradiction (fun hab => hp ⟨a, b, hpa, hpb, hab⟩)

lemma oneCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (p : α)
    (nonempty : ∃ u v, R u v)
    (cover : ∀ u v, R u v → u = p ∨ v = p) :
    ∃ q, R p q ∧ ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q := by
  have neighbor : ∃ q, R p q := by
    obtain ⟨u, v, huv⟩ := nonempty
    rcases cover u v huv with hu | hv
    · exact ⟨v, hu ▸ huv⟩
    · exact ⟨u, symm u p (hv ▸ huv)⟩
  obtain ⟨q, hpq⟩ := neighbor
  refine ⟨q, hpq, ?_⟩
  intro u v huv
  exact (cover u v huv).elim Or.inl (fun h => Or.inr (Or.inl h))

lemma twoCover_cross {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (irrefl : ∀ u, ¬ R u u)
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (p q : α) (hnpq : ¬ R p q)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    ∀ a c, R p a → R q c → R p c ∨ R q a := by
  intro a c hpa hqc
  have hanp : a ≠ p := fun h => irrefl p (h ▸ hpa)
  have hanq : a ≠ q := fun h => hnpq (h ▸ hpa)
  have hcnp : c ≠ p := fun h => hnpq (symm q p (h ▸ hqc))
  have hcnq : c ≠ q := fun h => irrefl q (h ▸ hqc)
  have hnac : ¬ R a c := by
    intro hac
    rcases cover a c hac with h | h | h | h
    · exact hanp h
    · exact hcnp h
    · exact hanq h
    · exact hcnq h
  rcases cross p a q c hpa hqc with h | h | h | h
  · exact False.elim (hnpq h)
  · exact Or.inl h
  · exact Or.inr (symm a q h)
  · exact False.elim (hnac h)

lemma smallCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (p q : α)
    (nonempty : ∃ u v, R u v)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q)
    (cross : ∀ a c, R p a → R q c → R p c ∨ R q a)
    (small : ∀ a b, R q a → R q b → a = b) :
    ∃ p' q', R p' q' ∧
      ∀ u v, R u v → u = p' ∨ v = p' ∨ u = q' ∨ v = q' := by
  by_cases hq : ∃ r, R q r
  · obtain ⟨r, hqr⟩ := hq
    by_cases hpr : R p r
    · refine ⟨p, r, hpr, ?_⟩
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (small v r (h ▸ huv) hqr)))
      · exact Or.inr (Or.inr (Or.inl (small u r (symm u q (h ▸ huv)) hqr)))
    · have hp : ∀ a, ¬ R p a := by
        intro a hpa
        have hqa := (cross a r hpa hqr).resolve_left hpr
        exact hpr ((small a r hqa hqr) ▸ hpa)
      have cq : ∀ u v, R u v → u = q ∨ v = q := by
        intro u v huv
        rcases cover u v huv with h | h | h | h
        · exact False.elim (hp v (h ▸ huv))
        · exact False.elim (hp u (symm u p (h ▸ huv)))
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨r', hqr', cr⟩ := oneCover_adjacent R symm q nonempty cq
      exact ⟨q, r', hqr', cr⟩
  · have cp : ∀ u v, R u v → u = p ∨ v = p := by
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hq ⟨v, h ▸ huv⟩)
      · exact False.elim (hq ⟨u, symm u q (h ▸ huv)⟩)
    obtain ⟨r, hpr, cr⟩ := oneCover_adjacent R symm p nonempty cp
    exact ⟨p, r, hpr, cr⟩

lemma twoCover_adjacent {α : Type} (R : α → α → Prop)
    (symm : ∀ u v, R u v → R v u) (irrefl : ∀ u, ¬ R u u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (cross : ∀ a b c d, R a b → R c d →
      R a c ∨ R a d ∨ R b c ∨ R b d)
    (nonempty : ∃ u v, R u v)
    (p q : α)
    (cover : ∀ u v, R u v → u = p ∨ v = p ∨ u = q ∨ v = q) :
    ∃ p' q', R p' q' ∧
      ∀ u v, R u v → u = p' ∨ v = p' ∨ u = q' ∨ v = q' := by
  by_cases hpq : p = q
  · subst q
    have cp : ∀ u v, R u v → u = p ∨ v = p := by
      intro u v huv
      rcases cover u v huv with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨r, hpr, cr⟩ := oneCover_adjacent R symm p nonempty cp
    exact ⟨p, r, hpr, cr⟩
  · by_cases hadj : R p q
    · exact ⟨p, q, hadj, cover⟩
    · rcases twoCover_oneSmall R symm irrefl free cross p q hpq hadj cover with hp | hq
      · have cqp : ∀ u v, R u v → u = q ∨ v = q ∨ u = p ∨ v = p := by
          intro u v huv
          rcases cover u v huv with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        have hnqp : ¬ R q p := fun h => hadj (symm q p h)
        exact smallCover_adjacent R symm q p nonempty cqp
          (twoCover_cross R symm irrefl cross q p hnqp cqp) hp
      · exact smallCover_adjacent R symm p q nonempty cover
          (twoCover_cross R symm irrefl cross p q hadj cover) hq

end PEqualNP.Outside.L_meta_2732_aux
