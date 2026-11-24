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
