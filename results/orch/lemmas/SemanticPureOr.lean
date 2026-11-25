import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

lemma pure_or_of_max_zero {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (haccept : ∀ x, (∃ i ∈ Q, x i = true) → f x = true)
    (hzero : f (fun i => decide (i ∉ Q)) = false) :
    ∀ x, f x = decide (∃ i ∈ Q, x i = true) := by
  intro x
  by_cases hx : ∃ i ∈ Q, x i = true
  · simp only [decide_eq_true hx]
    exact haccept x hx
  · have hf : f x = false := by
      cases heq : f x with
      | false => rfl
      | true =>
          have ht := hmono x (fun i => decide (i ∉ Q)) (by
            intro i hi
            apply decide_eq_true
            intro hmem
            exact hx ⟨i, hmem, hi⟩) heq
          rw [hzero] at ht
          contradiction
    simp only [decide_eq_false hx]
    exact hf

lemma pure_or_and_choice {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
    (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  classical
  have hzero : (f (fun i => decide (i ∉ Q)) && g (fun i => decide (i ∉ Q))) = false := by
    rw [heq]
    apply decide_eq_false
    rintro ⟨i, hi, hni⟩
    exact (of_decide_eq_true hni) hi
  have haccept : ∀ x, (∃ i ∈ Q, x i = true) → f x = true ∧ g x = true := by
    intro x hx
    have h := heq x
    rw [decide_eq_true hx] at h
    exact Bool.and_eq_true_iff.mp h
  rcases Bool.and_eq_false_iff.mp hzero with h | h
  · exact Or.inl (pure_or_of_max_zero Q f hf (fun x hx => (haccept x hx).1) h)
  · exact Or.inr (pure_or_of_max_zero Q g hg (fun x hx => (haccept x hx).2) h)

end PEqualNP.Outside.L_meta_4970_aux
