import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma twoCommonPoints_filters_unique {α ι : Type} (R : α → α → Prop)
    (A B : α → Prop) (S : ι → α → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ i u v, (A u ∨ A v) → (B u ∨ B v) → (S i u ∨ S i v) → R u v)
    (c d : α) (hcd : c ≠ d) (hcA : A c) (hcB : B c) (hdA : A d) (hdB : B d) :
    ∀ i j u v, S i u → S j v → u = v := by
  intro i j u v hu hv
  apply Classical.byContradiction
  intro huv
  exact free c d u v hcd huv
    ⟨safe i c u (Or.inl hcA) (Or.inl hcB) (Or.inr hu),
      safe j c v (Or.inl hcA) (Or.inl hcB) (Or.inr hv),
      safe i d u (Or.inl hdA) (Or.inl hdB) (Or.inr hu),
      safe j d v (Or.inl hdA) (Or.inl hdB) (Or.inr hv)⟩

lemma twoPoints_extra_noOwner {α : Type} (R : α → α → Prop) (A : α → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (p u v a : α) (huv : u ≠ v) (hu : A u) (hv : A v)
    (hpu : R p u) (hpv : R p v) (ha : A a) (hpa : ¬ R p a) :
    ¬ ∃ q, ∀ x, A x → R q x := by
  rintro ⟨q, hq⟩
  have hqp : q = p := by
    apply Classical.byContradiction
    intro hne
    exact free q p u v hne huv ⟨hq u hu, hq v hv, hpu, hpv⟩
  exact hpa (hqp ▸ hq a ha)

end PEqualNP.Outside.L_meta_2732_aux
