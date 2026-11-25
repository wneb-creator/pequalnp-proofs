import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_gct_231_aux

open MvPolynomial

noncomputable def binaryLinear (a : Fin 2 → ℂ) : MvPolynomial (Fin 2) ℂ :=
  C (a 0) * X 0 + C (a 1) * X 1

lemma pair_proportional_of_kernel
    (a₀ a₁ d₀ d₁ : ℂ) (ha : a₀ ≠ 0 ∨ a₁ ≠ 0)
    (h : d₀ * (-a₁) + d₁ * a₀ = 0) :
    ∃ r : ℂ, d₀ = r * a₀ ∧ d₁ = r * a₁ := by
  by_cases h₀ : a₀ = 0
  · have h₁ : a₁ ≠ 0 := ha.resolve_left (not_not_intro h₀)
    have hd₀ : d₀ = 0 := by
      have hz : d₀ * a₁ = 0 := by simpa [h₀] using h
      exact (mul_eq_zero.mp hz).resolve_right h₁
    refine ⟨d₁ / a₁, ?_, ?_⟩
    · simp [hd₀, h₀]
    · simp [div_mul_cancel₀ _ h₁]
  · refine ⟨d₀ / a₀, ?_, ?_⟩
    · simp [div_mul_cancel₀ _ h₀]
    · field_simp
      linear_combination h

lemma binaryLinear_proportional_of_kernel
    (a d : Fin 2 → ℂ) (ha : a ≠ 0) (hd : d ≠ 0)
    (h : d 0 * (-a 1) + d 1 * a 0 = 0) :
    ∃ r : ℂ, r ≠ 0 ∧ binaryLinear d = C r * binaryLinear a := by
  have ha' : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply ha
    funext i
    fin_cases i <;> simp_all
  obtain ⟨r, hr₀, hr₁⟩ := pair_proportional_of_kernel (a 0) (a 1) (d 0) (d 1) ha' h
  have hr : r ≠ 0 := by
    intro hz
    apply hd
    funext i
    fin_cases i <;> simp_all
  refine ⟨r, hr, ?_⟩
  simp only [binaryLinear, hr₀, hr₁, map_mul]
  ring

lemma binaryLinear_one_factor_matches
    (a b c d e f : Fin 2 → ℂ)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h : binaryLinear a * binaryLinear b * binaryLinear c =
      binaryLinear d * binaryLinear e * binaryLinear f) :
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear d = C r * binaryLinear a) ∨
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear e = C r * binaryLinear a) ∨
    (∃ r : ℂ, r ≠ 0 ∧ binaryLinear f = C r * binaryLinear a) := by
  let point : Fin 2 → ℂ := ![-a 1, a 0]
  have hz := congrArg (MvPolynomial.eval point) h
  have hea : MvPolynomial.eval point (binaryLinear a) = 0 := by
    simp [binaryLinear, point]
    ring
  simp only [map_mul, hea, zero_mul] at hz
  have hz' := mul_eq_zero.mp hz.symm
  rcases hz' with hde | hff
  · rcases mul_eq_zero.mp hde with hdd | hee
    · left
      apply binaryLinear_proportional_of_kernel a d ha hd
      simpa [binaryLinear, point] using hdd
    · right; left
      apply binaryLinear_proportional_of_kernel a e ha he
      simpa [binaryLinear, point] using hee
  · right; right
    apply binaryLinear_proportional_of_kernel a f ha hf
    simpa [binaryLinear, point] using hff

end PEqualNP.Outside.L_gct_231_aux
