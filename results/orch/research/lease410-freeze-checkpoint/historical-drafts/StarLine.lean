import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231

set_option maxHeartbeats 4000000 in
lemma constant_lower_block_is_star (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hb : V (1,1) = V (3,3) ∧ V (1,2) = V (3,3) ∧
      V (1,3) = V (3,3) ∧ V (2,2) = V (3,3) ∧ V (2,3) = V (3,3))
    (hp : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * V (i,j)) = 24) :
    V = starMatrix (V (0,1)) (V (0,2)) := by
  rcases hb with ⟨h11,h12,h13,h22,h23⟩
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  let s := V (0,1) + V (0,2) + V (0,3)
  let r := V (3,3)
  have h00 : V (0,0) = -2*s - 9*r := by
    have h₁ := hp 1
    have h₂ := hp (-1)
    have h₃ := hp 2
    have h₄ := hp (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23] at h₁ h₂ h₃ h₄
    dsimp [s,r]
    linear_combination h₁ / 9 - h₂ / 9 - h₃ / 72 + h₄ / 72
  have hpoly : ∀ z : ℂ,
      2 * (s^2 - 6*s*r - 63*r^2) * z^2 +
      4*r * (s^2 - 6*s*r - 39*r^2) * z^3 +
      2*r^2 * (s-9*r) * (s+3*r) * z^4 = 0 := by
    intro z
    have hz := hp z
    rw [permanent_four] at hz
    simp [hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h00] at hz
    dsimp [s, r] at hz ⊢
    linear_combination hz
  have hq : 2 * (s^2 - 6*s*r - 63*r^2) = 0 := by
    exact (quartic_first_coefficients 0 _ _ _ (by simpa using hpoly)).2
  have hc : 4*r * (s^2 - 6*s*r - 39*r^2) = 0 := by
    have h₁ := hpoly 1
    have h₂ := hpoly (-1)
    linear_combination h₁ / 2 - h₂ / 2
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
    rw [hsz, hr] at h00
    simpa using h00
  funext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32,
      h11, h12, h13, h22, h23, h33, h03, h00z]

def starLineQuad (t e f g h i j : ℂ) : ℂ :=
  h*j+i^2+t^2*(e*j+g^2)+(1+t)^2*(e*h+f^2)+
    2*t*(f*j+g*i)-2*(1+t)*(f*i+g*h)-2*t*(1+t)*(e*i+f*g)

set_option maxHeartbeats 4000000 in
lemma star_line_constraints (t : ℂ) (V : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, V (i,j) = V (j,i))
    (hp : ∀ a z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + starMatrix a (t*a) (i,j) +
        z * V (i,j)) = 24) :
    (t+1)*V (1,2)-t*V (1,3)+t*V (2,2)-(t+1)*V (3,3)+
        V (1,1)-V (2,3) = 0 ∧
    t^2*(V (2,2)-2*V (2,3)+V (3,3))+
        2*t*(V (1,2)-V (1,3)-V (2,3)+V (3,3))+
        V (1,1)-2*V (1,3)+V (3,3) = 0 ∧
    starLineQuad t (V (1,1)) (V (1,2)) (V (1,3))
      (V (2,2)) (V (2,3)) (V (3,3)) = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs30 := hs 3 0
  have hs21 := hs 2 1
  have hs31 := hs 3 1
  have hs32 := hs 3 2
  have hl : ∀ a : ℂ, starLinear V a (t*a) = 0 := by
    intro a
    have h₁ := hp a 1
    have h₂ := hp a (-1)
    have h₃ := hp a 2
    have h₄ := hp a (-2)
    rw [permanent_four] at h₁ h₂ h₃ h₄
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄
    unfold starLinear
    linear_combination (2 / 3 : ℂ) * h₁ - (2 / 3 : ℂ) * h₂ -
      (1 / 12 : ℂ) * h₃ + (1 / 12 : ℂ) * h₄
  have hl0 := hl 0
  have hl1 := hl 1
  have hlm := hl (-1)
  simp only [starLinear] at hl0 hl1 hlm
  refine ⟨?_,?_,?_⟩
  · linear_combination -hl1 / 8 + hlm / 8
  · linear_combination hl1 / 2 + hlm / 2 - hl0
  · have h₁ := hp 1 1
    have h₂ := hp (-1) 1
    have h₃ := hp 1 (-1)
    have h₄ := hp (-1) (-1)
    have h₅ := hp 0 1
    have h₆ := hp 0 (-1)
    rw [permanent_four] at h₁ h₂ h₃ h₄ h₅ h₆
    simp [starMatrix, hs10, hs20, hs30, hs21, hs31, hs32] at h₁ h₂ h₃ h₄ h₅ h₆
    unfold starLineQuad
    linear_combination h₁ / 4 + h₂ / 4 + h₃ / 4 + h₄ / 4 - h₅ / 2 - h₆ / 2

def starLineU (t f g h i : ℂ) : ℂ := t*(t+2)*((g-i)-(f-i)+(h-i))
def starLineV (t f h i : ℂ) : ℂ := (f-i)+t*(h-i)
def starLineW (t f h i : ℂ) : ℂ :=
  (t^2-8*t-2)*(f-i)+t*(7*t^2+10*t+10)*(h-i)

set_option maxHeartbeats 4000000 in
lemma star_line_congruence (t e f g h i j : ℂ)
    (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (h1 : (t+1)*f-t*g+t*h-(t+1)*j+e-i = 0)
    (h2 : t^2*(h-2*i+j)+2*t*(f-g-i+j)+e-2*g+j = 0) :
    (t+2)^2 * starLineQuad t e f g h i j =
      2 * ((starLineU t f g h i)^2 - starLineV t f h i * starLineW t f h i) := by
  have he : e = (-f*t^2-4*f*t-f+g*t^2+3*g*t+2*g-2*h*t^2-h*t+
      2*i*t^2+3*i*t+i)/(t+2) := by
    apply (eq_div_iff ht2).2
    linear_combination (t+1)*h1+h2
  have hj : j = (-f*t+f+g*t+2*g-h*t^2+h*t+2*i*t^2+2*i*t-i)/
      ((t+1)*(t+2)) := by
    apply (eq_div_iff (mul_ne_zero ht1 ht2)).2
    linear_combination h2-h1
  rw [he,hj]
  unfold starLineQuad starLineU starLineV starLineW
  field_simp
  <;> ring

lemma star_line_coordinate_kernel (t e f g h i j : ℂ)
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0) (ht2 : t+2 ≠ 0)
    (h1 : (t+1)*f-t*g+t*h-(t+1)*j+e-i = 0)
    (h2 : t^2*(h-2*i+j)+2*t*(f-g-i+j)+e-2*g+j = 0)
    (hU : starLineU t f g h i = 0)
    (hV : starLineV t f h i = 0)
    (hW : starLineW t f h i = 0) : e=j ∧ f=j ∧ g=j ∧ h=j ∧ i=j := by
  simp only [starLineU, starLineV, starLineW] at hU hV hW
  have hh : 6*t*(t+1)*(t+2)*(h-i) = 0 := by
    linear_combination hW-(t^2-8*t-2)*hV
  have hhi : h = i := by
    have hz : h-i = 0 := (mul_eq_zero.mp hh).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht) ht1) ht2)
    linear_combination hz
  have hfi : f = i := by rw [hhi] at hV; linear_combination hV
  have hgi : g = i := by
    rw [hhi,hfi] at hU
    have hz : t*(t+2)*(g-i) = 0 := by simpa using hU
    have hz' : g-i = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ht ht2)
    linear_combination hz'
  have hji : j = i := by
    have hz : (t+1)*(t+2)*(j-i) = 0 := by
      rw [hfi,hgi,hhi] at h1 h2
      linear_combination h2-h1
    have hz' : j-i = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero ht1 ht2)
    linear_combination hz'
  have hei : e = i := by rw [hfi,hgi,hhi,hji] at h1; linear_combination h1
  exact ⟨hei.trans hji.symm,hfi.trans hji.symm,hgi.trans hji.symm,
    hhi.trans hji.symm,hji.symm⟩

end PEqualNP.Outside.L_gct_231
