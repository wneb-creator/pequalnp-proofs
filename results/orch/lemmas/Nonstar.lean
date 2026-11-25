import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

def nonstarPlane1 (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0, a, a, -2*a; a, 0, 0, b; a, 0, 0, -b; -2*a, b, -b, 0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 4000000 in
lemma nonstar1_normalized_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (h01 : V (0,1) = 0)
    (h13 : V (1,3) = 0)
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + nonstarPlane1 a b (i,j) + z * V (i,j)) = 24) :
    V = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a b : ℂ, 4*a^2*b*V (1,1) - 4*a^2*b*V (2,2) + a^2*V (1,1) + 2*a^2*V (1,2) + a^2*V (2,2) - 4*a^2*V (2,3) + 4*a^2*V (3,3) + 4*a*b*V (0,2) + 2*a*b*V (1,1) - 2*a*b*V (2,2) - 4*a*V (1,1) - 8*a*V (1,2) - 4*a*V (2,2) + 4*a*V (2,3) + 8*a*V (3,3) + b^2*V (1,1) - 2*b^2*V (1,2) + b^2*V (2,2) + 4*b*V (0,2) - 4*b*V (1,1) + 4*b*V (2,2) + 6*V (0,0) + 12*V (0,2) + 12*V (0,3) + 6*V (1,1) + 12*V (1,2) + 6*V (2,2) + 12*V (2,3) + 6*V (3,3) = 0 := by
    intro a b
    have h₁ := hp a b 1
    have h₂ := hp a b (-1)
    have h₃ := hp a b 2
    have h₄ := hp a b (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [nonstarPlane1, hs10, hs20, hs30, hs21, hs31, hs32, h01, h13] at h₁ h₂ h₃ h₄
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have h0 := hl (0) (0)
  have h1 := hl (1) (0)
  have h2 := hl (-1) (0)
  have h3 := hl (0) (1)
  have h4 := hl (0) (-1)
  have h5 := hl (1) (1)
  have hv00 : V (0,0) = -2*V (0,3) - 9*V (3,3) := by
    linear_combination (-31/30 : ℂ) * h0 + (19/20 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/20 : ℂ) * h3 + (3/20 : ℂ) * h4 + (-1/5 : ℂ) * h5
  have hv02 : V (0,2) = 0 := by
    linear_combination (1/10 : ℂ) * h0 + (-1/10 : ℂ) * h1 + (-1/40 : ℂ) * h3 + (-3/40 : ℂ) * h4 + (1/10 : ℂ) * h5
  have hv11 : V (1,1) = V (3,3) := by
    linear_combination (-7/60 : ℂ) * h0 + (-2/15 : ℂ) * h1 + (1/20 : ℂ) * h3 + (3/20 : ℂ) * h4 + (1/20 : ℂ) * h5
  have hv12 : V (1,2) = V (3,3) := by
    linear_combination (1/3 : ℂ) * h0 + (-1/12 : ℂ) * h1 + (-1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4
  have hv22 : V (2,2) = V (3,3) := by
    linear_combination (-13/60 : ℂ) * h0 + (-1/30 : ℂ) * h1 + (1/5 : ℂ) * h3 + (1/10 : ℂ) * h4 + (-1/20 : ℂ) * h5
  have hv23 : V (2,3) = 2*V (3,3) := by
    linear_combination (1/3 : ℂ) * h0 + (-5/24 : ℂ) * h1 + (-1/8 : ℂ) * h2
  let r := V (3,3)
  let u := V (0,3)
  have hpoly : ∀ z : ℂ,
      2*(u^2-6*u*r-63*r^2)*z^2 + 4*r*(u^2-6*u*r-39*r^2)*z^3 +
      2*r^2*(u-9*r)*(u+3*r)*z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [nonstarPlane1, hs10, hs20, hs30, hs21, hs31, hs32, h01, h13, hv00, hv02, hv11, hv12, hv22, hv23] at hz
    dsimp [u,r]
    linear_combination hz
  have hq : 2*(u^2-6*u*r-63*r^2) = 0 :=
    (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r*(u^2-6*u*r-39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination h₁ / 2 - h₂ / 2
  have hr3 : r^3 = 0 := by linear_combination hc / 96 - r * hq / 48
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr3
  have hu2 : u^2 = 0 := by rw [hr] at hq; linear_combination hq / 2
  have hu : u = 0 := eq_zero_of_pow_eq_zero hu2
  have hv03 : V (0,3) = 0 := hu
  have hv33 : V (3,3) = 0 := hr
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hs10, hs20, hs30, hs21, hs31, hs32, h01, h13, hv00, hv02, hv11, hv12, hv22, hv23, hv03, hv33]

def nonstarPlane2 (a b : ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0, a, b, -a - b; a, 0, a - b, -2*a - b; b, a - b, 0, a + 2*b; -a - b, -2*a - b, a + 2*b, 0] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

set_option maxHeartbeats 4000000 in
lemma nonstar2_normalized_zero (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (h01 : V (0,1) = 0)
    (h02 : V (0,2) = 0)
    (hp : ∀ a b z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + nonstarPlane2 a b (i,j) + z * V (i,j)) = 24) :
    V = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a b : ℂ, -4*a^3*V (0,0) + 4*a^3*V (2,2) - 6*a^2*b*V (0,0) - 2*a^2*b*V (1,1) + 6*a^2*b*V (2,2) + 2*a^2*b*V (3,3) - 4*a^2*V (0,3) - 4*a^2*V (1,2) + 4*a^2*V (2,2) - 4*a^2*V (2,3) + 4*a^2*V (3,3) + 6*a*b^2*V (0,0) - 6*a*b^2*V (1,1) + 2*a*b^2*V (2,2) - 2*a*b^2*V (3,3) - 8*a*b*V (1,2) + 8*a*b*V (2,2) + 4*a*V (0,3) - 4*a*V (1,2) - 8*a*V (2,2) + 4*a*V (2,3) + 8*a*V (3,3) + 4*b^3*V (0,0) - 4*b^3*V (1,1) + 4*b^2*V (0,3) + 4*b^2*V (1,1) - 4*b^2*V (1,2) - 4*b^2*V (1,3) + 4*b^2*V (2,2) - 4*b*V (0,3) + 8*b*V (1,1) - 4*b*V (1,2) + 4*b*V (1,3) - 8*b*V (2,2) + 6*V (0,0) + 12*V (0,3) + 6*V (1,1) + 12*V (1,2) + 12*V (1,3) + 6*V (2,2) + 12*V (2,3) + 6*V (3,3) = 0 := by
    intro a b
    have h₁ := hp a b 1
    have h₂ := hp a b (-1)
    have h₃ := hp a b 2
    have h₄ := hp a b (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [nonstarPlane2, hs10, hs20, hs30, hs21, hs31, hs32, h01, h02] at h₁ h₂ h₃ h₄
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have h0 := hl (0) (0)
  have h1 := hl (1) (0)
  have h2 := hl (-1) (0)
  have h3 := hl (0) (1)
  have h4 := hl (0) (-1)
  have h5 := hl (1) (1)
  have h6 := hl (-1) (1)
  have hv00 : V (0,0) = V (3,3) := by
    linear_combination (-1/54 : ℂ) * h0 + (-1/18 : ℂ) * h1 + (1/18 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-1/108 : ℂ) * h5 + (-1/18 : ℂ) * h6
  have hv03 : V (0,3) = -5*V (3,3) := by
    linear_combination (-65/72 : ℂ) * h0 + (19/24 : ℂ) * h1 + (1/3 : ℂ) * h2 + (1/4 : ℂ) * h3 + (1/8 : ℂ) * h4 + (-11/36 : ℂ) * h5 + (-5/24 : ℂ) * h6
  have hv11 : V (1,1) = V (3,3) := by
    linear_combination (1/9 : ℂ) * h0 + (-1/6 : ℂ) * h1 + (-1/12 : ℂ) * h2 + (1/18 : ℂ) * h5 + (1/12 : ℂ) * h6
  have hv12 : V (1,2) = V (3,3) := by
    linear_combination (29/216 : ℂ) * h0 + (-7/72 : ℂ) * h1 + (-1/36 : ℂ) * h2 + (-1/24 : ℂ) * h3 + (1/216 : ℂ) * h5 + (1/36 : ℂ) * h6
  have hv13 : V (1,3) = -4*V (3,3) := by
    linear_combination (-53/108 : ℂ) * h0 + (19/36 : ℂ) * h1 + (2/9 : ℂ) * h2 + (1/12 : ℂ) * h3 + (-35/216 : ℂ) * h5 + (-7/72 : ℂ) * h6
  have hv22 : V (2,2) = V (3,3) := by
    linear_combination (5/27 : ℂ) * h0 + (-7/36 : ℂ) * h1 + (-1/18 : ℂ) * h2 + (-1/12 : ℂ) * h3 + (5/54 : ℂ) * h5 + (1/18 : ℂ) * h6
  have hv23 : V (2,3) = 6*V (3,3) := by
    linear_combination (65/54 : ℂ) * h0 + (-73/72 : ℂ) * h1 + (-35/72 : ℂ) * h2 + (-7/24 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (85/216 : ℂ) * h5 + (17/72 : ℂ) * h6
  let r := V (3,3)
  have hpoly : ∀ z : ℂ, -16*r^2*z^2 + 64*r^3*z^3 + 56*r^4*z^4 = 0 := by
    intro z
    have hz := hp 0 0 z
    rw [permanent_four] at hz
    simp [nonstarPlane2, hs10, hs20, hs30, hs21, hs31, hs32, h01, h02, hv00, hv03, hv11, hv12, hv13, hv22, hv23] at hz
    dsimp [r]
    linear_combination hz
  have hq : -16*r^2 = 0 :=
    (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hr2 : r^2 = 0 := by linear_combination -hq / 16
  have hr : r = 0 := eq_zero_of_pow_eq_zero hr2
  have hv33 : V (3,3) = 0 := hr
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [hs10, hs20, hs30, hs21, hs31, hs32, h01, h02, hv00, hv03, hv11, hv12, hv13, hv22, hv23, hv33]

end PEqualNP.Outside.L_gct_231
