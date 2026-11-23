import Mathlib

namespace CofactorObstruction

def gate (x a z : Bool) : Bool :=
  (x && a) || (z && (x || a))

theorem actual_output (x a : Bool) : gate x a (!a) = x := by
  cases x <;> cases a <;> rfl

theorem no_fixed_cofactor : ¬ ∃ z : Bool, ∀ x a : Bool, gate x a z = x := by
  decide

/-- Even a common monotone replacement for the NOT wire need not exist.
This is an obstruction to that substitution strategy, not a circuit-size lower bound. -/
theorem no_common_monotone_replacement :
    ¬ ∃ z : Bool → Bool → Bool → Bool,
      (∀ x y a b, a ≤ b → z x y a ≤ z x y b) ∧
      (∀ x y a, gate x a (z x y a) = x) ∧
      (∀ x y a, gate y a (z x y a) = y) := by
  rintro ⟨z, hmono, hx, hy⟩
  have h₁ := hx true false false
  have h₀ := hy true false true
  simp only [gate, Bool.and_false, Bool.true_or, Bool.and_true, Bool.false_or] at h₁
  simp only [gate, Bool.false_or, Bool.and_true] at h₀
  have hm := hmono true false false true (by decide)
  rw [h₁, h₀] at hm
  contradiction

end CofactorObstruction
