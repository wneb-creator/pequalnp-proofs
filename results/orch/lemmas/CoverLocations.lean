import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.CoverConversion

lemma low_row_to_split {α : Type*} [DecidableEq α]
    (P Q : Finset α) (R : α → α → Prop) [DecidableRel R]
    (a b : α) (hQ : Q.Nonempty)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b)
    (hdegree : (Q.filter (R b)).card ≤ 1) :
    ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ y = q := by
  classical
  by_cases hne : (Q.filter (R b)).Nonempty
  · obtain ⟨q, hq⟩ := hne
    refine ⟨q, (Finset.mem_filter.mp hq).1, ?_⟩
    intro x hx y hy hxy
    rcases hcover x hx y hy hxy with hxa | hxb
    · exact Or.inl hxa
    · right
      exact (Finset.card_le_one.mp hdegree) y
        (Finset.mem_filter.mpr ⟨hy, hxb ▸ hxy⟩) q hq
  · obtain ⟨q, hq⟩ := hQ
    refine ⟨q, hq, ?_⟩
    intro x hx y hy hxy
    rcases hcover x hx y hy hxy with hxa | hxb
    · exact Or.inl hxa
    · exact False.elim (hne ⟨y, Finset.mem_filter.mpr ⟨hy, hxb ▸ hxy⟩⟩)

lemma row_cover_split_or_heavy {α : Type*} [DecidableEq α]
    (P Q : Finset α) (R : α → α → Prop) [DecidableRel R]
    (a b : α) (ha : a ∈ P) (hb : b ∈ P) (hQ : Q.Nonempty)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b) :
    (∃ p ∈ P, ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = p ∨ y = q) ∨
      (2 ≤ (Q.filter (R a)).card ∧ 2 ≤ (Q.filter (R b)).card) := by
  classical
  by_cases ha2 : 2 ≤ (Q.filter (R a)).card
  · by_cases hb2 : 2 ≤ (Q.filter (R b)).card
    · exact Or.inr ⟨ha2, hb2⟩
    · obtain ⟨q, hq, hc⟩ := low_row_to_split P Q R a b hQ hcover (by omega)
      exact Or.inl ⟨a, ha, q, hq, hc⟩
  · obtain ⟨q, hq, hc⟩ := low_row_to_split P Q R b a hQ
      (fun x hx y hy hxy => (hcover x hx y hy hxy).symm) (by omega)
    exact Or.inl ⟨b, hb, q, hq, hc⟩

end PEqualNP.Outside.L_meta_1477.CoverConversion

namespace PEqualNP.Outside.L_meta_1477.CoverLocations

open CoverConversion

def SplitCover {α : Type*} [DecidableEq α] (P Q : Finset α) (R : α → α → Prop) : Prop :=
  ∃ p ∈ P, ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = p ∨ y = q

def HeavyRows {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) [DecidableRel R] : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
    2 ≤ (Q.filter (R a)).card ∧ 2 ≤ (Q.filter (R b)).card ∧
    ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b

lemma row_classify {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) [DecidableRel R] (hQ : Q.Nonempty)
    (a b : α) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b) :
    SplitCover P Q R ∨ HeavyRows P Q R := by
  rcases row_cover_split_or_heavy P Q R a b ha hb hQ hc with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, b, hb, hne, h.1, h.2, hc⟩

lemma split_flip {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) (h : SplitCover Q P (fun y x => R x y)) :
    SplitCover P Q R := by
  obtain ⟨q, hq, p, hp, hc⟩ := h
  exact ⟨p, hp, q, hq, fun x hx y hy hxy => (hc y hy x hx hxy).symm⟩

lemma cover_locations {α : Type*} [DecidableEq α]
    (P Q T : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hdis : Disjoint P Q)
    (hcard : T.card ≤ 2)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x ∈ T ∨ y ∈ T) :
    SplitCover P Q R ∨ HeavyRows P Q R ∨ HeavyRows Q P (fun y x => R x y) := by
  classical
  let S := T ∩ (P ∪ Q)
  have hScard : S.card ≤ 2 := (Finset.card_le_card Finset.inter_subset_left).trans hcard
  have hSloc : ∀ a ∈ S, a ∈ P ∨ a ∈ Q := by
    intro a ha
    exact Finset.mem_union.mp (Finset.mem_inter.mp ha).2
  have hc : ∀ x ∈ P, ∀ y ∈ Q, R x y → x ∈ S ∨ y ∈ S := by
    intro x hx y hy hxy
    exact (hcover x hx y hy hxy).imp
      (fun h => Finset.mem_inter.mpr ⟨h, Finset.mem_union_left _ hx⟩)
      (fun h => Finset.mem_inter.mpr ⟨h, Finset.mem_union_right _ hy⟩)
  have hneq : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q := by
    intro p hp q hq he
    exact Finset.disjoint_left.mp hdis hp (he.symm ▸ hq)
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  by_cases hs : S.card ≤ 1
  · by_cases he : S.Nonempty
    · obtain ⟨a, ha⟩ := he
      have hall : ∀ z ∈ S, z = a := fun z hz => Finset.card_le_one.mp hs z hz a ha
      rcases hSloc a ha with haP | haQ
      · left
        refine ⟨a, haP, q, hq, ?_⟩
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact Or.inl (hall x hxs)
        · exact False.elim ((hneq a haP y hy) (hall y hys).symm)
      · left
        refine ⟨p, hp, a, haQ, ?_⟩
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact False.elim ((hneq x hx a haQ) (hall x hxs))
        · exact Or.inr (hall y hys)
    · left
      refine ⟨p, hp, q, hq, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · exact False.elim (he ⟨x, hxs⟩)
      · exact False.elim (he ⟨y, hys⟩)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hsub : {a, b} ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact h ▸ ha
      · exact (Finset.mem_singleton.mp h) ▸ hb
    have heq : ({a, b} : Finset α) = S :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hab] using hScard)
    have hmem : ∀ z ∈ S, z = a ∨ z = b := by
      intro z hz
      simpa only [← heq, Finset.mem_insert, Finset.mem_singleton] using hz
    rcases hSloc a ha with haP | haQ <;> rcases hSloc b hb with hbP | hbQ
    · have hr : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b := by
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact hmem x hxs
        · rcases hmem y hys with he | he
          · exact False.elim ((hneq a haP y hy) he.symm)
          · exact False.elim ((hneq b hbP y hy) he.symm)
      exact (row_classify P Q R ⟨q, hq⟩ a b haP hbP hab hr).imp id Or.inl
    · left
      refine ⟨a, haP, b, hbQ, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · rcases hmem x hxs with he | he
        · exact Or.inl he
        · exact False.elim ((hneq x hx b hbQ) he)
      · rcases hmem y hys with he | he
        · exact False.elim ((hneq a haP y hy) he.symm)
        · exact Or.inr he
    · left
      refine ⟨b, hbP, a, haQ, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · rcases hmem x hxs with he | he
        · exact False.elim ((hneq x hx a haQ) he)
        · exact Or.inl he
      · rcases hmem y hys with he | he
        · exact Or.inr he
        · exact False.elim ((hneq b hbP y hy) he.symm)
    · have hr : ∀ y ∈ Q, ∀ x ∈ P, R x y → y = a ∨ y = b := by
        intro y hy x hx hxy
        rcases hc x hx y hy hxy with hxs | hys
        · rcases hmem x hxs with he | he
          · exact False.elim ((hneq x hx a haQ) he)
          · exact False.elim ((hneq x hx b hbQ) he)
        · exact hmem y hys
      rcases row_classify Q P (fun y x => R x y) ⟨p, hp⟩ a b haQ hbQ hab hr with h | h
      · exact Or.inl (split_flip P Q R h)
      · exact Or.inr (Or.inr h)

end PEqualNP.Outside.L_meta_1477.CoverLocations
