import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Fragment

lemma same_colour_disjoint_no_pair {α : Type*} [DecidableEq α]
    (A B : Finset α) (colour : α → Bool) (u v : α)
    (hdisj : Disjoint A B)
    (hmono : ∀ a ∈ A, ∀ b ∈ B, colour a = colour b)
    (hdiff : colour u ≠ colour v) :
    ¬ ((u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B)) := by
  rintro ⟨hu | hv, hu' | hv'⟩
  · exact Finset.disjoint_left.1 hdisj hu hu'
  · exact hdiff (hmono u hu v hv')
  · exact hdiff (hmono v hv u hu').symm
  · exact Finset.disjoint_left.1 hdisj hv hv'

lemma same_colour_disjoint_fragment {α : Type*} [DecidableEq α]
    (A B : Finset α) (colour : α → Bool) (u v : α) (P Q : Prop)
    (hdisj : Disjoint A B)
    (hmono : ∀ a ∈ A, ∀ b ∈ B, colour a = colour b)
    (hdiff : colour u ≠ colour v) :
    ((u ∈ A ∨ v ∈ A) ∨ P) ∧ ((u ∈ B ∨ v ∈ B) ∨ Q) → P ∨ Q := by
  rintro ⟨ha | hp, hb | hq⟩
  · exact (same_colour_disjoint_no_pair A B colour u v hdisj hmono hdiff ⟨ha, hb⟩).elim
  · exact Or.inr hq
  · exact Or.inl hp
  · exact Or.inl hp

lemma safe_fragment_replacement (F X Y : Prop)
    (hX : X → F) (hY : Y → F) : X ∨ Y → F := by
  rintro (hx | hy)
  · exact hX hx
  · exact hY hy

end PEqualNP.Outside.L_meta_4675.Fragment
