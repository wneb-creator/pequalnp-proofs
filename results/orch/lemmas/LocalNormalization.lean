import Mathlib

namespace PEqualNP.Outside.L_meta_3678_aux

lemma matching_intersection (a b c d : Bool) :
    (((a || d) && (b || c)) && ((a || c) && (b || d))) =
      ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma matching_first_dirty :
    ∃ a b c d : Bool,
      ((a || d) && (b || c)) = true ∧ ((a && b) || (c && d)) = false := by
  exact ⟨true, false, true, false, rfl, rfl⟩

lemma matching_second_dirty :
    ∃ a b c d : Bool,
      ((a || c) && (b || d)) = true ∧ ((a && b) || (c && d)) = false := by
  exact ⟨true, false, false, true, rfl, rfl⟩

lemma biclique_has_opposite_colors {α : Type*} (s : α → Bool)
    (A B : Set α) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, s a ≠ s b) :
    ∃ c : Bool, (∀ a ∈ A, s a = c) ∧ (∀ b ∈ B, s b = !c) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨s a, ?_, ?_⟩
  · intro a' ha'
    have hab := h a ha b hb
    have hab' := h a' ha' b hb
    cases hsa : s a <;> cases hsb : s b <;> cases hsap : s a' <;>
      simp_all
  · intro b' hb'
    have hab' := h a ha b' hb'
    cases hsa : s a <;> cases hsb : s b' <;> simp_all

end PEqualNP.Outside.L_meta_3678_aux
