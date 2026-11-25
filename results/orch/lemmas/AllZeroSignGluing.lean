import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231_aux.AllZeroSignGluing

theorem binary_coefficients (A B C p q : ℂ)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    A ^ 2 = 24 * p ^ 4 ∧ 2 * A * B = 96 * p ^ 3 * q ∧
      B ^ 2 + 2 * A * C = 144 * p ^ 2 * q ^ 2 ∧ C ^ 2 = 24 * q ^ 4 := by
  have h0 := H 1 0
  have h1 := H 1 1
  have hn1 := H 1 (-1)
  have h2 := H 1 2
  have hn2 := H 1 (-2)
  have hi := H 0 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h0
  · linear_combination (2 / 3 : ℂ) * (h1 - hn1) - (1 / 12 : ℂ) * (h2 - hn2)
  · linear_combination (2 / 3 : ℂ) * (h1 + hn1) - (1 / 24 : ℂ) * (h2 + hn2) - (5 / 4 : ℂ) * h0
  · linear_combination hi

theorem binary_first (A B C p q h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (hA : A = h * p ^ 2)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    B = 2 * h * p * q ∧ C = h * q ^ 2 := by
  obtain ⟨_, h3, h2, _⟩ := binary_coefficients A B C p q H
  have hn : h ≠ 0 := by
    intro hz
    rw [hz] at hh
    norm_num at hh
  have hs : 2 * h * p ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hn) (pow_ne_zero 2 hp)
  rw [hA] at h3 h2
  have hB0 : (2 * h * p ^ 2) * (B - 2 * h * p * q) = 0 := by
    linear_combination h3 - 4 * p ^ 3 * q * hh
  have hB : B = 2 * h * p * q := sub_eq_zero.mp ((mul_eq_zero.mp hB0).resolve_left hs)
  rw [hB] at h2
  have hC0 : (2 * h * p ^ 2) * (C - h * q ^ 2) = 0 := by
    linear_combination h2 - 6 * p ^ 2 * q ^ 2 * hh
  exact ⟨hB, sub_eq_zero.mp ((mul_eq_zero.mp hC0).resolve_left hs)⟩

theorem binary_mixed (A B C p q h : ℂ) (hh : h ^ 2 = 24)
    (hA : A = h * p ^ 2)
    (H : ∀ x y : ℂ, (A * x ^ 2 + B * x * y + C * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4) :
    B = 2 * h * p * q := by
  by_cases hp : p = 0
  · obtain ⟨_, _, h2, _⟩ := binary_coefficients A B C p q H
    have hB : B ^ 2 = 0 := by
      rw [hA, hp] at h2
      simpa using h2
    simpa [hp] using eq_zero_of_pow_eq_zero hB
  · exact (binary_first A B C p q h hh hp hA H).1

theorem anchored_known (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (hA : A = h * p ^ 2)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    A = h * p ^ 2 ∧ B = h * q ^ 2 ∧ C = h * r ^ 2 ∧
      D = h * p * q ∧ E = h * p * r ∧ F = h * q * r := by
  have hAB := binary_first A (2 * D) B p q h hh hp hA Hxy
  have hAC := binary_first A (2 * E) C p r h hh hp hA Hxz
  have hF := binary_mixed B (2 * F) C q r h hh hAB.2 Hyz
  refine ⟨hA, hAB.2, hAC.2, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * hAB.1
  · linear_combination (1 / 2 : ℂ) * hAC.1
  · linear_combination (1 / 2 : ℂ) * hF

theorem anchored_glue (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24) (hp : p ≠ 0)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    ∃ k : ℂ, k ^ 2 = 24 ∧ A = k * p ^ 2 ∧ B = k * q ^ 2 ∧ C = k * r ^ 2 ∧
      D = k * p * q ∧ E = k * p * r ∧ F = k * q * r := by
  have hAA := (binary_coefficients A (2 * D) B p q Hxy).1
  have hf : (A - h * p ^ 2) * (A + h * p ^ 2) = 0 := by
    linear_combination hAA - p ^ 4 * hh
  rcases mul_eq_zero.mp hf with hf | hf
  · exact ⟨h, hh, anchored_known A B C D E F p q r h hh hp (sub_eq_zero.mp hf) Hxy Hxz Hyz⟩
  · have hn : (-h) ^ 2 = 24 := by simpa using hh
    have hA : A = (-h) * p ^ 2 := by linear_combination hf
    exact ⟨-h, hn, anchored_known A B C D E F p q r (-h) hn hp hA Hxy Hxz Hyz⟩

theorem glue (A B C D E F p q r h : ℂ) (hh : h ^ 2 = 24)
    (Hxy : ∀ x y : ℂ, (A * x ^ 2 + 2 * D * x * y + B * y ^ 2) ^ 2 = 24 * (p * x + q * y) ^ 4)
    (Hxz : ∀ x z : ℂ, (A * x ^ 2 + 2 * E * x * z + C * z ^ 2) ^ 2 = 24 * (p * x + r * z) ^ 4)
    (Hyz : ∀ y z : ℂ, (B * y ^ 2 + 2 * F * y * z + C * z ^ 2) ^ 2 = 24 * (q * y + r * z) ^ 4) :
    ∃ k : ℂ, k ^ 2 = 24 ∧ A = k * p ^ 2 ∧ B = k * q ^ 2 ∧ C = k * r ^ 2 ∧
      D = k * p * q ∧ E = k * p * r ∧ F = k * q * r := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · by_cases hr : r = 0
      · have hA : A = 0 := by simpa [hp] using Hxy 1 0
        have hB : B = 0 := by simpa [hq] using Hxy 0 1
        have hC : C = 0 := by simpa [hr] using Hxz 0 1
        have hD := binary_mixed A (2 * D) B p q h hh (by simp [hA, hp]) Hxy
        have hE := binary_mixed A (2 * E) C p r h hh (by simp [hA, hp]) Hxz
        have hF := binary_mixed B (2 * F) C q r h hh (by simp [hB, hq]) Hyz
        refine ⟨h, hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hp] using hA
        · simpa [hq] using hB
        · simpa [hr] using hC
        · linear_combination (1 / 2 : ℂ) * hD
        · linear_combination (1 / 2 : ℂ) * hE
        · linear_combination (1 / 2 : ℂ) * hF
      · have Hzy : ∀ z y : ℂ, (C * z ^ 2 + 2 * F * z * y + B * y ^ 2) ^ 2 = 24 * (r * z + q * y) ^ 4 := by
          intro z y
          convert Hyz y z using 1 <;> ring
        have Hzx : ∀ z x : ℂ, (C * z ^ 2 + 2 * E * z * x + A * x ^ 2) ^ 2 = 24 * (r * z + p * x) ^ 4 := by
          intro z x
          convert Hxz x z using 1 <;> ring
        have Hyx : ∀ y x : ℂ, (B * y ^ 2 + 2 * D * y * x + A * x ^ 2) ^ 2 = 24 * (q * y + p * x) ^ 4 := by
          intro y x
          convert Hxy x y using 1 <;> ring
        obtain ⟨k, hk, hC, hB, hA, hF, hE, hD⟩ := anchored_glue C B A F E D r q p h hh hr Hzy Hzx Hyx
        refine ⟨k, hk, hA, hB, hC, ?_, ?_, ?_⟩
        · linear_combination hD
        · linear_combination hE
        · linear_combination hF
    · have Hyx : ∀ y x : ℂ, (B * y ^ 2 + 2 * D * y * x + A * x ^ 2) ^ 2 = 24 * (q * y + p * x) ^ 4 := by
        intro y x
        convert Hxy x y using 1 <;> ring
      obtain ⟨k, hk, hB, hA, hC, hD, hF, hE⟩ := anchored_glue B A C D F E q p r h hh hq Hyx Hyz Hxz
      refine ⟨k, hk, hA, hB, hC, ?_, hE, hF⟩
      linear_combination hD
  · exact anchored_glue A B C D E F p q r h hh hp Hxy Hxz Hyz

end PEqualNP.Outside.L_gct_231_aux.AllZeroSignGluing
