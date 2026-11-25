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


lemma rectangle_meet_full_point {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true)
    (p : α) (hp₁ : p ∈ X₁) (hp₂ : p ∈ X₂) :
    (∀ y ∈ Y₁, R p y) ∨ (∀ y ∈ Y₂, R p y) := by
  classical
  by_cases h₁ : ∀ y ∈ Y₁, R p y
  · exact Or.inl h₁
  right
  by_contra h₂
  push_neg at h₁ h₂
  obtain ⟨l,hl,hnl⟩ := h₁
  obtain ⟨m,hm,hnm⟩ := h₂
  obtain ⟨x,y,hxy,hx,hy⟩ := clean (fun x => decide (x = p))
    (fun y => decide (y = l ∨ y = m)) ⟨p,hp₁,by simp⟩ ⟨l,hl,by simp⟩
    ⟨p,hp₂,by simp⟩ ⟨m,hm,by simp⟩
  simp only [decide_eq_true_eq] at hx hy
  subst x
  rcases hy with rfl | rfl
  · exact hnl hxy
  · exact hnm hxy

lemma rectangle_meet_full_line {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true)
    (l : β) (hl₁ : l ∈ Y₁) (hl₂ : l ∈ Y₂) :
    (∀ x ∈ X₁, R x l) ∨ (∀ x ∈ X₂, R x l) := by
  apply rectangle_meet_full_point (fun y x => R x y) Y₁ Y₂ X₁ X₂ _ l hl₁ hl₂
  intro g f hy₁ hx₁ hy₂ hx₂
  obtain ⟨x,y,hxy,hx,hy⟩ := clean f g hx₁ hy₁ hx₂ hy₂
  exact ⟨y,x,hxy,hy,hx⟩

lemma rectangle_meet_global_centers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (hx₁ : 2 ≤ X₁.card) (hx₂ : 2 ≤ X₂.card)
    (hy₁ : 2 ≤ Y₁.card) (hy₂ : 2 ≤ Y₂.card)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    let P := X₁.filter (fun p => ∀ l ∈ Y₁, R p l) ∪
      X₂.filter (fun p => ∀ l ∈ Y₂, R p l)
    let L := Y₁.filter (fun l => ∀ p ∈ X₁, R p l) ∪
      Y₂.filter (fun l => ∀ p ∈ X₂, R p l)
    P.card ≤ 2 ∧ L.card ≤ 2 ∧
      X₁ ∩ X₂ ⊆ P ∧ Y₁ ∩ Y₂ ⊆ L := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · have h := Finset.card_union_le
      (X₁.filter (fun p => ∀ l ∈ Y₁, R p l))
      (X₂.filter (fun p => ∀ l ∈ Y₂, R p l))
    have h₁ := rectangle_full_points_card R noRect X₁ Y₁ hy₁
    have h₂ := rectangle_full_points_card R noRect X₂ Y₂ hy₂
    omega
  · have h := Finset.card_union_le
      (Y₁.filter (fun l => ∀ p ∈ X₁, R p l))
      (Y₂.filter (fun l => ∀ p ∈ X₂, R p l))
    have h₁ := rectangle_full_lines_card R noRect X₁ Y₁ hx₁
    have h₂ := rectangle_full_lines_card R noRect X₂ Y₂ hx₂
    omega
  · intro p hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_inter.mp hp
    rcases rectangle_meet_full_point R X₁ X₂ Y₁ Y₂ clean p hp₁ hp₂ with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp₁,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp₂,h⟩))
  · intro l hl
    obtain ⟨hl₁,hl₂⟩ := Finset.mem_inter.mp hl
    rcases rectangle_meet_full_line R X₁ X₂ Y₁ Y₂ clean l hl₁ hl₂ with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hl₁,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hl₂,h⟩))

end PEqualNP.Outside.L_meta_2602_aux
