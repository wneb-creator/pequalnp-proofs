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

end PEqualNP.Outside.L_meta_2732_aux
