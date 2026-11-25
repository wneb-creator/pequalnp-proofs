import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace PEqualNP.Outside.L_gct_231.TwoBlock

lemma branch_zero (h t x y : ℂ)
    (hh : h ^ 2 = 2)
    (hy : y * (2*h*x+t+3*y) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-6*y^2 = 0)
    (hc : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+t^2*x+2*t*x*y-4*x*y^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 := by
  by_cases hy0 : y = 0
  · subst y
    have hx3 : x ^ 3 = 0 := by
      linear_combination (x/4)*hq + (3/4 : ℂ)*hc
    have hx : x = 0 := eq_zero_of_pow_eq_zero hx3
    subst x
    have ht2 : t ^ 2 = 0 := by linear_combination (-1/3 : ℂ)*hq
    exact ⟨eq_zero_of_pow_eq_zero ht2, rfl, rfl⟩
  · have hl : 2*h*x+t+3*y = 0 := (mul_eq_zero.mp hy).resolve_left hy0
    have ht : t = -2*h*x-3*y := by linear_combination hl
    rw [ht] at hq hc
    have hQ : -20*x^2-12*h*x*y+3*y^2 = 0 := by
      linear_combination hq + 12*x^2*hh
    have hRprod : x * (8*x^2+4*h*x*y-5*y^2) = 0 := by
      linear_combination hc - 2*x*(-2*h*x*y+2*x^2-y^2)*hh
    by_cases hx0 : x = 0
    · have hy2 : y ^ 2 = 0 := by
        subst x
        linear_combination (1/3 : ℂ)*hQ
      exact False.elim (hy0 (eq_zero_of_pow_eq_zero hy2))
    · have hR : 8*x^2+4*h*x*y-5*y^2 = 0 :=
        (mul_eq_zero.mp hRprod).resolve_left hx0
      have hxl : x * (19*x+12*h*y) = 0 := by
        linear_combination (-5/4 : ℂ)*hQ - (3/4 : ℂ)*hR
      have hL : 19*x+12*h*y = 0 := (mul_eq_zero.mp hxl).resolve_left hx0
      have hx2 : x ^ 2 = 0 := by
        linear_combination ((115*x-12*h*y)/265)*hL +
          (144*y^2/265)*hh + (96/265 : ℂ)*hQ
      exact False.elim (hx0 (eq_zero_of_pow_eq_zero hx2))

lemma quadrics_and_cubic_zero (h t x y z : ℂ)
    (hh : h ^ 2 = 2)
    (h0 : (y-z)*(y+z) = 0)
    (h1 : (y+z)*(4*h*x+2*t+5*y+z) = 0)
    (h2 : (y-z)*(4*h*x-2*t-5*y+z) = 0)
    (hq : -3*t^2-12*t*y+4*x^2-9*y^2+3*z^2 = 0)
    (hc : -h*t^2*z-5*h*t*y*z+4*h*x^2*z-6*h*y^2*z+
      t^2*x+2*t*x*y-2*x*y^2-2*x*z^2 = 0) :
    t = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  rcases mul_eq_zero.mp h0 with hm | hp
  · have hz : z = y := (sub_eq_zero.mp hm).symm
    subst z
    have hy : y*(2*h*x+t+3*y) = 0 := by linear_combination (1/4 : ℂ)*h1
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -h*t^2*y-5*h*t*y^2+4*h*x^2*y-6*h*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero h t x y hh hy hq' hc' with ⟨ht, hx, hy0⟩
    exact ⟨ht, hx, hy0, hy0⟩
  · have hz : z = -y := by linear_combination hp
    rw [hz] at h2 hq hc
    have hh' : (-h)^2 = 2 := by linear_combination hh
    have hy : y*(2*(-h)*x+t+3*y) = 0 := by linear_combination (-1/4 : ℂ)*h2
    have hq' : -3*t^2-12*t*y+4*x^2-6*y^2 = 0 := by linear_combination hq
    have hc' : -(-h)*t^2*y-5*(-h)*t*y^2+4*(-h)*x^2*y-6*(-h)*y^3+
        t^2*x+2*t*x*y-4*x*y^2 = 0 := by linear_combination hc
    rcases branch_zero (-h) t x y hh' hy hq' hc' with ⟨ht, hx, hy0⟩
    refine ⟨ht, hx, hy0, ?_⟩
    simpa only [hy0, neg_zero] using hz


namespace MatrixBridge

lemma sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.permanent M =
    (M 0 0 * M 1 1 + M 0 1 * M 1 0) * (M 2 2 * M 3 3 + M 2 3 * M 3 2) + (M 0 0 * M 1 2 + M 0 2 * M 1 0) * (M 2 1 * M 3 3 + M 2 3 * M 3 1) + (M 0 0 * M 1 3 + M 0 3 * M 1 0) * (M 2 1 * M 3 2 + M 2 2 * M 3 1) + (M 0 1 * M 1 2 + M 0 2 * M 1 1) * (M 2 0 * M 3 3 + M 2 3 * M 3 0) + (M 0 1 * M 1 3 + M 0 3 * M 1 1) * (M 2 0 * M 3 2 + M 2 2 * M 3 0) + (M 0 2 * M 1 3 + M 0 3 * M 1 2) * (M 2 0 * M 3 1 + M 2 1 * M 3 0) := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


def blockA (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![((-1) + h), 1, 0, 0], ![1, ((-1) + ((-1) * h)), 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

def blockB (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, ((-1) + h), 1], ![0, 0, 1, ((-1) + ((-1) * h))]]

def extension (h t x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![(((-2) * z) + (t * ((-1) + h)) + (x * ((-2) + h)) + (y * ((-4) + (2 * h)))), 0, (x + z), (x + y)], ![0, ((2 * z) + (t * (1 + h)) + (y * (4 + (2 * h))) + ((-1) * x * (2 + h))), (x + ((-1) * y)), (x + ((-1) * z))], ![(x + z), (x + ((-1) * y)), (((-2) * z) + (t * (1 + ((-1) * h))) + (x * ((-2) + h)) + (y * (4 + ((-2) * h)))), 0], ![(x + y), (x + ((-1) * z)), 0, ((2 * z) + (t * ((-1) + ((-1) * h))) + ((-1) * x * (2 + h)) + ((-1) * y * (4 + (2 * h))))]]

def coefficient2 (h t x y z U V : ℂ) : ℂ :=
  (((-36) * (y ^ 2)) + ((-12) * (t ^ 2)) + (12 * (z ^ 2)) + (16 * (x ^ 2)) + (h * (((-16) * U * x * y) + ((-16) * U * x * z) + ((-16) * V * x * z) + (16 * V * x * y))) + ((-48) * t * y) + ((-20) * U * (y ^ 2)) + ((-20) * V * (y ^ 2)) + ((-4) * U * (z ^ 2)) + ((-4) * V * (z ^ 2)) + ((-36) * U * V * (y ^ 2)) + ((-24) * U * y * z) + ((-8) * U * t * y) + ((-8) * U * t * z) + ((-8) * V * t * y) + (8 * V * t * z) + (24 * V * y * z) + (36 * U * V * (z ^ 2)))

def coefficient3 (h t x y z U V : ℂ) : ℂ :=
  ((h * (((-36) * U * (y ^ 3)) + ((-32) * z * (x ^ 2)) + ((-20) * U * (z ^ 3)) + ((-20) * V * (z ^ 3)) + (8 * z * (t ^ 2)) + (36 * V * (y ^ 3)) + (48 * z * (y ^ 2)) + ((-60) * V * y * (z ^ 2)) + ((-20) * V * t * (z ^ 2)) + ((-16) * V * y * (x ^ 2)) + ((-4) * V * y * (t ^ 2)) + (4 * U * y * (t ^ 2)) + (4 * U * z * (t ^ 2)) + (4 * V * z * (t ^ 2)) + (16 * U * y * (x ^ 2)) + (16 * U * z * (x ^ 2)) + (16 * V * z * (x ^ 2)) + (20 * U * t * (z ^ 2)) + (40 * t * y * z) + (44 * U * z * (y ^ 2)) + (44 * V * z * (y ^ 2)) + (60 * U * y * (z ^ 2)) + (20 * U * t * y * z) + (20 * V * t * y * z))) + ((-8) * x * (t ^ 2)) + (16 * x * (y ^ 2)) + (16 * x * (z ^ 2)) + ((-16) * t * x * y) + (16 * U * x * (y ^ 2)) + (16 * V * x * (y ^ 2)) + (40 * U * x * (z ^ 2)) + (40 * V * x * (z ^ 2)) + ((-56) * V * x * y * z) + ((-24) * V * t * x * z) + (24 * U * t * x * y) + (24 * U * t * x * z) + (24 * V * t * x * y) + (56 * U * x * y * z))

def coefficient4 (h t x y z U V : ℂ) : ℂ :=
  ((t ^ 4) + (24 * (x ^ 4)) + (25 * (z ^ 4)) + (81 * (y ^ 4)) + (h * (((-40) * x * (z ^ 3)) + (32 * z * (x ^ 3)) + ((-152) * x * z * (y ^ 2)) + ((-16) * x * z * (t ^ 2)) + ((-128) * t * x * y * z))) + ((-246) * (y ^ 2) * (z ^ 2)) + ((-96) * (x ^ 2) * (y ^ 2)) + ((-30) * (t ^ 2) * (z ^ 2)) + ((-18) * (t ^ 2) * (y ^ 2)) + ((-12) * (t ^ 2) * (x ^ 2)) + ((-8) * (x ^ 2) * (z ^ 2)) + ((-160) * t * y * (z ^ 2)) + ((-32) * t * y * (x ^ 2)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma permanent_expansion (h t x y z U V W : ℂ) (hh : h^2 = 2) :
    Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + U*blockA h r s + V*blockB h r s + W*extension h t x y z r s) - 24 =
    W^2*(coefficient2 h t x y z U V + W*coefficient3 h t x y z U V +
      W^2*coefficient4 h t x y z U V) := by
  simp [perm4, Matrix.of_apply, blockA, blockB, extension, coefficient2, coefficient3, coefficient4]
  linear_combination (((-2) * (U ^ 2)) + ((-2) * (V ^ 2)) + (W * (((-4) * U * x) + ((-4) * V * x) + (4 * x * (U ^ 2)) + (4 * x * (V ^ 2)) + ((-4) * U * x * (V ^ 2)) + ((-4) * V * x * (U ^ 2)) + ((-4) * h * y * (V ^ 2)) + ((-2) * h * t * (V ^ 2)) + (2 * h * t * (U ^ 2)) + (4 * h * y * (U ^ 2)) + ((-4) * U * h * y * (V ^ 2)) + ((-4) * U * h * z * (V ^ 2)) + ((-4) * V * h * z * (U ^ 2)) + (2 * U * x * (V ^ 2) * (h ^ 2)) + (2 * V * x * (U ^ 2) * (h ^ 2)) + (4 * V * h * y * (U ^ 2)))) + ((W ^ 2) * (((-16) * (y ^ 2)) + ((-4) * (t ^ 2)) + ((-4) * (x ^ 2)) + ((U ^ 2) * (t ^ 2)) + ((V ^ 2) * (t ^ 2)) + ((-16) * t * y) + ((-8) * U * (y ^ 2)) + ((-8) * V * (y ^ 2)) + ((-4) * (U ^ 2) * (x ^ 2)) + ((-4) * (V ^ 2) * (x ^ 2)) + (4 * (U ^ 2) * (z ^ 2)) + (4 * (V ^ 2) * (z ^ 2)) + (8 * U * (x ^ 2)) + (8 * V * (x ^ 2)) + (16 * (U ^ 2) * (y ^ 2)) + (16 * (V ^ 2) * (y ^ 2)) + ((U ^ 2) * (h ^ 2) * (x ^ 2)) + ((V ^ 2) * (h ^ 2) * (x ^ 2)) + ((-1) * (U ^ 2) * (h ^ 2) * (t ^ 2)) + ((-1) * (V ^ 2) * (h ^ 2) * (t ^ 2)) + ((-18) * U * V * (y ^ 2)) + ((-16) * y * z * (U ^ 2)) + ((-8) * U * V * (x ^ 2)) + ((-8) * U * y * z) + ((-4) * U * t * y) + ((-4) * U * t * z) + ((-4) * V * t * y) + ((-4) * t * z * (U ^ 2)) + ((-4) * (U ^ 2) * (h ^ 2) * (y ^ 2)) + ((-4) * (V ^ 2) * (h ^ 2) * (y ^ 2)) + (4 * V * t * z) + (4 * t * z * (V ^ 2)) + (8 * V * y * z) + (8 * t * y * (U ^ 2)) + (8 * t * y * (V ^ 2)) + (16 * y * z * (V ^ 2)) + (18 * U * V * (z ^ 2)) + ((-8) * V * h * x * y) + ((-4) * V * h * t * x) + ((-4) * h * x * z * (U ^ 2)) + ((-4) * h * x * z * (V ^ 2)) + ((-4) * t * y * (U ^ 2) * (h ^ 2)) + ((-4) * t * y * (V ^ 2) * (h ^ 2)) + ((-2) * h * t * x * (U ^ 2)) + (2 * h * t * x * (V ^ 2)) + (4 * U * V * (h ^ 2) * (x ^ 2)) + (4 * U * h * t * x) + (8 * U * h * x * y) + ((-16) * U * V * h * x * z))) + ((W ^ 3) * ((8 * (x ^ 3)) + ((-48) * x * (y ^ 2)) + ((-8) * U * (x ^ 3)) + ((-8) * V * (x ^ 3)) + ((-8) * x * (t ^ 2)) + ((-40) * t * x * y) + ((-16) * V * h * (y ^ 3)) + (2 * U * x * (t ^ 2)) + (2 * U * (h ^ 2) * (x ^ 3)) + (2 * V * x * (t ^ 2)) + (2 * V * (h ^ 2) * (x ^ 3)) + (16 * U * h * (y ^ 3)) + (26 * U * x * (z ^ 2)) + (26 * V * x * (z ^ 2)) + (38 * U * x * (y ^ 2)) + (38 * V * x * (y ^ 2)) + ((-16) * V * h * t * (y ^ 2)) + ((-12) * U * h * z * (x ^ 2)) + ((-12) * V * h * z * (x ^ 2)) + ((-8) * U * x * y * z) + ((-8) * U * x * (h ^ 2) * (y ^ 2)) + ((-8) * V * x * (h ^ 2) * (y ^ 2)) + ((-4) * U * h * t * (x ^ 2)) + ((-4) * U * h * y * (x ^ 2)) + ((-4) * V * h * y * (t ^ 2)) + ((-4) * V * t * x * z) + ((-2) * U * x * (h ^ 2) * (t ^ 2)) + ((-2) * V * x * (h ^ 2) * (t ^ 2)) + (4 * U * h * y * (t ^ 2)) + (4 * U * h * z * (t ^ 2)) + (4 * U * t * x * z) + (4 * V * h * t * (x ^ 2)) + (4 * V * h * y * (x ^ 2)) + (4 * V * h * z * (t ^ 2)) + (8 * V * x * y * z) + (16 * U * h * t * (y ^ 2)) + (16 * U * h * z * (y ^ 2)) + (16 * V * h * z * (y ^ 2)) + (28 * U * t * x * y) + (28 * V * t * x * y) + ((-8) * U * t * x * y * (h ^ 2)) + ((-8) * V * t * x * y * (h ^ 2)) + (16 * U * h * t * y * z) + (16 * V * h * t * y * z))) + ((W ^ 4) * (((-104) * (y ^ 4)) + ((-6) * (x ^ 4)) + ((h ^ 2) * (t ^ 4)) + ((h ^ 2) * (x ^ 4)) + ((-136) * t * (y ^ 3)) + ((-58) * (t ^ 2) * (y ^ 2)) + ((-40) * (y ^ 2) * (z ^ 2)) + ((-10) * (t ^ 2) * (z ^ 2)) + ((-8) * y * (t ^ 3)) + ((-2) * (t ^ 2) * (x ^ 2)) + (16 * (h ^ 2) * (y ^ 4)) + (26 * (x ^ 2) * (z ^ 2)) + (46 * (x ^ 2) * (y ^ 2)) + ((-40) * t * y * (z ^ 2)) + ((-8) * h * z * (x ^ 3)) + ((-8) * (h ^ 2) * (x ^ 2) * (y ^ 2)) + ((-2) * (h ^ 2) * (t ^ 2) * (x ^ 2)) + (8 * y * (h ^ 2) * (t ^ 3)) + (24 * t * y * (x ^ 2)) + (24 * (h ^ 2) * (t ^ 2) * (y ^ 2)) + (32 * t * (h ^ 2) * (y ^ 3)) + ((-8) * t * y * (h ^ 2) * (x ^ 2)) + (8 * h * x * z * (t ^ 2)) + (32 * h * x * z * (y ^ 2)) + (32 * h * t * x * y * z))) + ((-2) * (U ^ 2) * (V ^ 2)) + ((U ^ 2) * (V ^ 2) * (h ^ 2)))*hh

lemma factor_coefficients (a b c : ℂ)
    (hp : ∀ W : ℂ, W^2*(a+W*b+W^2*c)=0) : a=0 ∧ b=0 := by
  have h1 := hp 1
  have hm := hp (-1)
  have h2 := hp 2
  constructor
  · linear_combination h1+(1/3:ℂ)*hm-(1/12:ℂ)*h2
  · linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*hm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_extension_zero (h t x y z : ℂ) (hh : h^2 = 2)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ) + U*blockA h r s + V*blockB h r s + W*extension h t x y z r s) = 24) :
    t = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  have he (U V : ℂ) : coefficient2 h t x y z U V=0 ∧ coefficient3 h t x y z U V=0 := by
    apply factor_coefficients
    intro W
    rw [← permanent_expansion h t x y z U V W hh, hp U V W]
    ring
  have h00 := (he 0 0).1
  have h10 := (he 1 0).1
  have h01 := (he 0 1).1
  have h11 := (he 1 1).1
  have hccc := (he 0 0).2
  simp only [coefficient2, coefficient3] at h00 h10 h01 h11 hccc
  apply quadrics_and_cubic_zero h t x y z hh
  · linear_combination (-1/36:ℂ)*(h11-h10-h01+h00)
  · linear_combination (-1/4:ℂ)*(h10-h00)
  · linear_combination (1/4:ℂ)*(h01-h00)
  · linear_combination (1/4:ℂ)*h00
  · linear_combination (-1/8:ℂ)*hccc

end MatrixBridge

end PEqualNP.Outside.L_gct_231.TwoBlock
