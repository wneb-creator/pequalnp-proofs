import Mathlib

namespace PEqualNP.Outside.L_meta_4675.StructuralIntersection

lemma same_colour_pair_intersection {α : Type*} [DecidableEq α]
    (A B : Finset α) (col : α → Bool) (u v : α)
    (huv : col u ≠ col v)
    (hcol : ∀ a ∈ A, ∀ b ∈ B, col a = col b) :
    ((∃ a ∈ A, a = u ∨ a = v) ∧ (∃ b ∈ B, b = u ∨ b = v)) ↔
      ∃ c ∈ A ∩ B, c = u ∨ c = v := by
  constructor
  · rintro ⟨⟨a, ha, hau | hav⟩, ⟨b, hb, hbu | hbv⟩⟩
    · subst a; subst b
      exact ⟨u, Finset.mem_inter.mpr ⟨ha, hb⟩, Or.inl rfl⟩
    · subst a; subst b
      exact (huv (hcol u ha v hb)).elim
    · subst a; subst b
      exact (huv (hcol v ha u hb).symm).elim
    · subst a; subst b
      exact ⟨v, Finset.mem_inter.mpr ⟨ha, hb⟩, Or.inr rfl⟩
  · rintro ⟨c, hc, hcu⟩
    exact ⟨⟨c, (Finset.mem_inter.mp hc).1, hcu⟩,
      ⟨c, (Finset.mem_inter.mp hc).2, hcu⟩⟩

lemma intersection_below_and {α : Type*} [DecidableEq α]
    (A B : Finset α) (x : α → Bool) :
    (∃ c ∈ A ∩ B, x c = true) →
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) := by
  rintro ⟨c, hc, hx⟩
  exact ⟨⟨c, (Finset.mem_inter.mp hc).1, hx⟩,
    ⟨c, (Finset.mem_inter.mp hc).2, hx⟩⟩

lemma same_colour_singleton_intersection {α : Type*} [DecidableEq α]
    (A B : Finset α) (col : α → Bool) (u v z : α)
    (huv : col u ≠ col v)
    (hcol : ∀ a ∈ A, ∀ b ∈ B, col a = col b)
    (hinter : A ∩ B = {z}) :
    ((∃ a ∈ A, a = u ∨ a = v) ∧ (∃ b ∈ B, b = u ∨ b = v)) ↔
      z = u ∨ z = v := by
  rw [same_colour_pair_intersection A B col u v huv hcol, hinter]
  simp

end PEqualNP.Outside.L_meta_4675.StructuralIntersection
