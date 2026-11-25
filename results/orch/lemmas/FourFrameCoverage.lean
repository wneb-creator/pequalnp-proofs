import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_gct_231_aux.FourFrameCoverage

def supported (a b c d e f : ℂ) : Prop :=
  (d = 0 ∧ e = 0 ∧ f = 0) ∨
  (b = 0 ∧ c = 0 ∧ f = 0) ∨
  (a = 0 ∧ c = 0 ∧ e = 0) ∨
  (a = 0 ∧ b = 0 ∧ d = 0) ∨
  (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  (a = 0 ∧ c = 0 ∧ d = 0 ∧ f = 0) ∨
  (a = 0 ∧ b = 0 ∧ e = 0 ∧ f = 0)

theorem support_of_products (a b c d e f : ℂ)
    (h₁ : a * b * d = 0) (h₂ : a * b * e = 0) (h₃ : a * b * f = 0)
    (h₄ : a * c * d = 0) (h₅ : a * c * e = 0) (h₆ : a * c * f = 0)
    (h₇ : a * d * f = 0) (h₈ : a * e * f = 0) (h₉ : b * c * d = 0)
    (h₁₀ : b * c * e = 0) (h₁₁ : b * c * f = 0) (h₁₂ : b * d * e = 0)
    (h₁₃ : b * e * f = 0) (h₁₄ : c * d * e = 0) (h₁₅ : c * d * f = 0)
    (h₁₆ : d * e * f = 0) : supported a b c d e f := by
  classical
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    by_cases hd : d = 0 <;> by_cases he : e = 0 <;> by_cases hf : f = 0 <;>
    simp_all [supported, mul_eq_zero]

theorem kernel_of_support (a b c d e f : ℂ) (h : supported a b c d e f) :
    ∃ x y z : ℂ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * z = 0 ∧ b * y = 0 ∧ c * (y - z) = 0 ∧
      d * x = 0 ∧ e * (x - z) = 0 ∧ f * (x - y) = 0 := by
  rcases h with ⟨hd, he, hf⟩ | ⟨hb, hc, hf⟩ | ⟨ha, hc, he⟩ |
    ⟨ha, hb, hd⟩ | ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · refine ⟨1, 0, 0, ?_⟩
    simp_all
  · refine ⟨0, 1, 0, ?_⟩
    simp_all
  · refine ⟨0, 0, 1, ?_⟩
    simp_all
  · refine ⟨1, 1, 1, ?_⟩
    simp_all
  · refine ⟨1, 1, 0, ?_⟩
    simp_all
  · refine ⟨1, 0, 1, ?_⟩
    simp_all
  · refine ⟨0, 1, 1, ?_⟩
    simp_all

end PEqualNP.Outside.L_gct_231_aux.FourFrameCoverage
