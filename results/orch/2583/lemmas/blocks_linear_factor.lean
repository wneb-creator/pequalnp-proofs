import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.LinearFactor

def linear {α : Type*} [DecidableEq α] (S : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

def outside {α : Type*} [DecidableEq α] (S : Finset α) : α → Bool :=
  fun i => decide (i ∉ S)

lemma linear_outside {α : Type*} [DecidableEq α] (S : Finset α) :
    linear S (outside S) = false := by
  simp [linear, outside]

lemma le_outside_of_linear_false {α : Type*} [DecidableEq α] (S : Finset α)
    (x : α → Bool) (hx : linear S x = false) : x ≤ outside S := by
  intro i
  by_cases hi : i ∈ S
  · have hxi : x i = false := by
      by_contra h
      have hxtrue : x i = true := by cases hxi : x i <;> simp_all
      have : linear S x = true := by
        simp only [linear, decide_eq_true_eq]
        exact ⟨i, hi, hxtrue⟩
      simp_all
    simp [hxi]
  · simp [outside, hi]

lemma linear_upper_of_outside_false {α : Type*} [DecidableEq α] (S : Finset α)
    (g : (α → Bool) → Bool) (hg : Monotone g) (hbase : g (outside S) = false) :
    ∀ x, g x = true → linear S x = true := by
  intro x hx
  cases hl : linear S x with
  | false =>
    have h := hg (le_outside_of_linear_false S x hl)
    rw [hx, hbase] at h
    exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
  | true => rfl

lemma eq_linear_of_outside_false {α : Type*} [DecidableEq α] (S : Finset α)
    (g : (α → Bool) → Bool) (hg : Monotone g)
    (hlower : ∀ x, linear S x = true → g x = true)
    (hbase : g (outside S) = false) : g = linear S := by
  funext x
  have hu := linear_upper_of_outside_false S g hg hbase x
  have hl := hlower x
  cases h1 : g x <;> cases h2 : linear S x <;> simp_all

lemma and_selects_linear_factor {α : Type*} [DecidableEq α] (S : Finset α)
    (a b : (α → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (hlower : ∀ x, linear S x = true → (a x && b x) = true)
    (hbase : (a (outside S) && b (outside S)) = false) :
    a = linear S ∨ b = linear S := by
  have hal : ∀ x, linear S x = true → a x = true := by
    intro x hx
    have h := hlower x hx
    cases ha : a x <;> cases hb : b x <;> simp_all
  have hbl : ∀ x, linear S x = true → b x = true := by
    intro x hx
    have h := hlower x hx
    cases ha : a x <;> cases hb : b x <;> simp_all
  cases h1 : a (outside S) with
  | false => exact Or.inl (eq_linear_of_outside_false S a ha hal h1)
  | true =>
    have h2 : b (outside S) = false := by simpa [h1] using hbase
    exact Or.inr (eq_linear_of_outside_false S b hb hbl h2)

lemma and_eq_linear_factor {α : Type*} [DecidableEq α] (S : Finset α)
    (a b : (α → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (heq : ∀ x, (a x && b x) = linear S x) :
    a = linear S ∨ b = linear S := by
  apply and_selects_linear_factor S a b ha hb
  · intro x hx
    rw [heq, hx]
  · rw [heq, linear_outside]

end PEqualNP.Outside.L_meta_2583_aux.LinearFactor
