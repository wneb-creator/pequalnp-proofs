import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

lemma star_quartic_first_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, a*z + b*z^2 + c*z^3 + d*z^4 = 0) : a = 0 ∧ b = 0 := by
  have h₁ := h 1
  have h₂ := h (-1)
  have h₃ := h 2
  have h₄ := h (-2)
  constructor
  · linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  · linear_combination (2 / 3 : ℂ) * h₁ + (2 / 3 : ℂ) * h₂ -
      (1 / 24 : ℂ) * h₃ - (1 / 24 : ℂ) * h₄

def starLinear (V : Fin 4 × Fin 4 → ℂ) (a b : ℂ) : ℂ :=
  a^2 * (V (1,1) - 2 * V (1,3) + V (3,3)) +
  2*a*b * (V (1,2) - V (1,3) - V (2,3) + V (3,3)) -
  4*a * (V (1,1) + V (1,2) - V (2,3) - V (3,3)) +
  b^2 * (V (2,2) - 2 * V (2,3) + V (3,3)) -
  4*b * (V (1,2) - V (1,3) + V (2,2) - V (3,3)) +
  6 * (V (0,0) + 2 * V (0,1) + 2 * V (0,2) + 2 * V (0,3) +
    V (1,1) + 2 * V (1,2) + 2 * V (1,3) + V (2,2) + 2 * V (2,3) + V (3,3))

set_option maxHeartbeats 2000000 in
lemma starLinear_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i,j) + z * V (i,j)) = 24)
    (a b : ℂ) : starLinear V a b = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have h₁ := hp a b 1
  have h₂ := hp a b (-1)
  have h₃ := hp a b 2
  have h₄ := hp a b (-2)
  rw [permanent_four] at h₁ h₂ h₃ h₄
  simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄
  unfold starLinear
  linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
    (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄

set_option maxHeartbeats 4000000 in
lemma star_two_plane_maximal (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a b (i,j) + z * V (i,j)) = 24) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  have h₀ := starLinear_zero V hs hp 0 0
  have h₁ := starLinear_zero V hs hp 1 0
  have h₂ := starLinear_zero V hs hp (-1) 0
  have h₃ := starLinear_zero V hs hp 0 1
  have h₄ := starLinear_zero V hs hp 0 (-1)
  have h₅ := starLinear_zero V hs hp 1 1
  simp only [starLinear] at h₀ h₁ h₂ h₃ h₄ h₅
  have h11 : V (1,1) = V (3,3) := by
    linear_combination (-2 / 3 : ℂ) * h₀ + (5 / 12 : ℂ) * h₁ +
      (1 / 4 : ℂ) * h₂ + (1 / 3 : ℂ) * h₃ - (1 / 3 : ℂ) * h₅
  have h12 : V (1,2) = V (3,3) := by
    linear_combination (5 / 6 : ℂ) * h₀ - (3 / 8 : ℂ) * h₁ -
      (1 / 8 : ℂ) * h₂ - (3 / 8 : ℂ) * h₃ - (1 / 8 : ℂ) * h₄ +
      (1 / 6 : ℂ) * h₅
  have h13 : V (1,3) = V (3,3) := by
    linear_combination (1 / 6 : ℂ) * h₀ - (1 / 24 : ℂ) * h₁ -
      (1 / 8 : ℂ) * h₂ + (1 / 6 : ℂ) * h₃ - (1 / 6 : ℂ) * h₅
  have h22 : V (2,2) = V (3,3) := by
    linear_combination (-2 / 3 : ℂ) * h₀ + (1 / 3 : ℂ) * h₁ +
      (5 / 12 : ℂ) * h₃ + (1 / 4 : ℂ) * h₄ - (1 / 3 : ℂ) * h₅
  have h23 : V (2,3) = V (3,3) := by
    linear_combination (1 / 6 : ℂ) * h₀ + (1 / 6 : ℂ) * h₁ -
      (1 / 24 : ℂ) * h₃ - (1 / 8 : ℂ) * h₄ - (1 / 6 : ℂ) * h₅
  have h00 : V (0,0) = -2 * (V (0,1) + V (0,2) + V (0,3)) - 9 * V (3,3) := by
    linear_combination (-5 / 6 : ℂ) * h₀ - (1 / 4 : ℂ) * h₁ +
      (1 / 4 : ℂ) * h₂ - (1 / 4 : ℂ) * h₃ + (1 / 4 : ℂ) * h₄ + h₅
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  let s := V (0,1) + V (0,2) + V (0,3)
  let r := V (3,3)
  have hpoly : ∀ z : ℂ,
      2 * (s^2 - 6*s*r - 63*r^2) * z^2 +
      4*r * (s^2 - 6*s*r - 39*r^2) * z^3 +
      2*r^2 * (s-9*r) * (s+3*r) * z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h00] at hz
    dsimp [s, r]
    linear_combination hz
  have hq : 2 * (s^2 - 6*s*r - 63*r^2) = 0 := by
    exact (star_quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r * (s^2 - 6*s*r - 39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination (1 / 2 : ℂ) * h₁ - (1 / 2 : ℂ) * h₂
  have hr3 : r^3 = 0 := by
    linear_combination hc / 96 - r * hq / 48
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr3
  have hs2 : s^2 = 0 := by
    rw [hr] at hq
    linear_combination hq / 2
  have hsz : s = 0 := eq_zero_of_pow_eq_zero hs2
  have h33 : V (3,3) = 0 := hr
  have h03 : V (0,3) = -V (0,1) - V (0,2) := by
    dsimp [s] at hsz
    linear_combination hsz
  have h00z : V (0,0) = 0 := by
    change V (0,0) = -2*s - 9*r at h00
    rw [hsz, hr] at h00
    simpa using h00
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h33, h03, h00z]

end PEqualNP.Outside.L_gct_231
