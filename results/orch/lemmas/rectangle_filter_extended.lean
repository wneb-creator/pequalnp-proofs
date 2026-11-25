import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

lemma rectangle_filter_point_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X : Finset α) (Y : Finset β) (p : α) (hp : p ∈ X) :
    (∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) → f p = true →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) ↔ ∀ y ∈ Y, R p y := by
  constructor
  · intro clean y hy
    obtain ⟨x, z, hR, hx, hz⟩ := clean (fun x => decide (x = p))
      (fun z => decide (z = y)) ⟨p, hp, by simp⟩ ⟨y, hy, by simp⟩ (by simp)
    simp only [decide_eq_true_eq] at hx hz
    subst x z
    exact hR
  · intro full f g _ hy hp
    obtain ⟨y, hy, hgy⟩ := hy
    exact ⟨p, y, full y hy, hp, hgy⟩

lemma rectangle_filter_line_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X : Finset α) (Y : Finset β) (l : β) (hl : l ∈ Y) :
    (∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) → g l = true →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) ↔ ∀ x ∈ X, R x l := by
  constructor
  · intro clean x hx
    obtain ⟨p, y, hR, hp, hy⟩ := clean (fun p => decide (p = x))
      (fun y => decide (y = l)) ⟨x, hx, by simp⟩ ⟨l, hl, by simp⟩ (by simp)
    simp only [decide_eq_true_eq] at hp hy
    subst p y
    exact hR
  · intro full f g hx _ hl
    obtain ⟨x, hx, hfx⟩ := hx
    exact ⟨x, l, full x hx, hfx, hl⟩

lemma rectangle_full_points_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X : Finset α) (Y : Finset β) (hY : 2 ≤ Y.card) :
    (X.filter (fun p => ∀ l ∈ Y, R p l)).card ≤ 1 := by
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.mp (by omega : 1 < Y.card)
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact noRect p q l m hpq hlm (hp' l hl) (hp' m hm) (hq' l hl) (hq' m hm)

lemma rectangle_full_lines_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X : Finset α) (Y : Finset β) (hX : 2 ≤ X.card) :
    (Y.filter (fun l => ∀ p ∈ X, R p l)).card ≤ 1 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  apply Finset.card_le_one.mpr
  intro l hl m hm
  by_contra hlm
  have hl' := (Finset.mem_filter.mp hl).2
  have hm' := (Finset.mem_filter.mp hm).2
  exact noRect p q l m hpq hlm (hl' p hp) (hm' p hp) (hl' q hq) (hm' q hq)

lemma rectangle_point_filter_absorb {α β : Type*}
    (X : Finset α) (Y : Finset β) (p : α) (hp : p ∈ X)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧ f p ↔ f p ∧ ∃ y ∈ Y, g y := by
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · exact fun h => ⟨⟨⟨p, hp, h.1⟩, h.2⟩, h.1⟩

lemma rectangle_line_filter_absorb {α β : Type*}
    (X : Finset α) (Y : Finset β) (l : β) (hl : l ∈ Y)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧ g l ↔ (∃ x ∈ X, f x) ∧ g l := by
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, ⟨l, hl, h.2⟩⟩, h.2⟩

lemma rectangle_filters_expand {α β : Type*}
    (X A : Finset α) (Y B : Finset β) (hA : A ⊆ X) (hB : B ⊆ Y)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧
        ((∃ a ∈ A, f a) ∨ ∃ b ∈ B, g b) ↔
      ((∃ a ∈ A, f a) ∧ ∃ y ∈ Y, g y) ∨
        ((∃ x ∈ X, f x) ∧ ∃ b ∈ B, g b) := by
  constructor
  · rintro ⟨⟨hx, hy⟩, ha | hb⟩
    · exact Or.inl ⟨ha, hy⟩
    · exact Or.inr ⟨hx, hb⟩
  · rintro (⟨⟨a, ha, hfa⟩, hy⟩ | ⟨hx, ⟨b, hb, hgb⟩⟩)
    · exact ⟨⟨⟨a, hA ha, hfa⟩, hy⟩, Or.inl ⟨a, ha, hfa⟩⟩
    · exact ⟨⟨hx, ⟨b, hB hb, hgb⟩⟩, Or.inr ⟨b, hb, hgb⟩⟩


lemma rectangle_filter_pair_footprint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X A : Finset α) (Y B : Finset β) (p : α) (l : β) :
    ((∃ x ∈ X, decide (x = p) = true) ∧ (∃ y ∈ Y, decide (y = l) = true)) ∧
        ((∃ a ∈ A, decide (a = p) = true) ∨ ∃ b ∈ B, decide (b = l) = true) ↔
      (p ∈ A ∩ X ∧ l ∈ Y) ∨ (p ∈ X ∧ l ∈ B ∩ Y) := by
  simp only [decide_eq_true_eq, exists_eq_right, Finset.mem_inter]
  tauto

lemma rectangle_filter_clean_centers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X A : Finset α) (Y B : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) →
      ((∃ a ∈ A, f a = true) ∨ ∃ b ∈ B, g b = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    (∀ p ∈ A ∩ X, ∀ l ∈ Y, R p l) ∧
      (∀ l ∈ B ∩ Y, ∀ p ∈ X, R p l) := by
  constructor
  · intro p hp
    obtain ⟨ha, hx⟩ := Finset.mem_inter.mp hp
    apply (rectangle_filter_point_iff R X Y p hx).mp
    intro f g hf hg hfp
    exact clean f g hf hg (Or.inl ⟨p, ha, hfp⟩)
  · intro l hl
    obtain ⟨hb, hy⟩ := Finset.mem_inter.mp hl
    apply (rectangle_filter_line_iff R X Y l hy).mp
    intro f g hf hg hgl
    exact clean f g hf hg (Or.inr ⟨l, hb, hgl⟩)

lemma rectangle_filter_two_stars {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X A : Finset α) (Y B : Finset β) (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) →
      ((∃ a ∈ A, f a = true) ∨ ∃ b ∈ B, g b = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    (A ∩ X).card ≤ 1 ∧ (B ∩ Y).card ≤ 1 := by
  obtain ⟨hp, hl⟩ := rectangle_filter_clean_centers R X A Y B clean
  constructor
  · apply le_trans (Finset.card_le_card ?_) (rectangle_full_points_card R noRect X Y hY)
    intro p h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).2, hp p h⟩
  · apply le_trans (Finset.card_le_card ?_) (rectangle_full_lines_card R noRect X Y hX)
    intro l h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).2, hl l h⟩

end PEqualNP.Outside.L_meta_2602_aux
