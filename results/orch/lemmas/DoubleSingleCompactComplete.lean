import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases



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

def gauged (a b c d u v w k : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a, 0, u, v], ![0, b, w, k], ![u, w, c, 0], ![v, k, 0, d]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma gauged_first_order (h a b c d u v w k U V : ℂ) (hh : h^2=2)
    (hp : ∀ W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*gauged a b c d u v w k r s)=24) :
    ((6 * a) + (6 * b) + (6 * c) + (6 * d) + (12 * k) + (12 * u) + (12 * v) + (12 * w) + (h * (((-4) * U * u) + ((-4) * U * v) + ((-4) * V * u) + ((-4) * V * w) + ((-2) * U * a) + ((-2) * V * c) + (2 * U * b) + (2 * V * d) + (4 * U * k) + (4 * U * w) + (4 * V * k) + (4 * V * v))) + ((-2) * U * a) + ((-2) * U * b) + ((-2) * V * c) + ((-2) * V * d) + ((-4) * U * V * v) + ((-4) * U * V * w) + (4 * U * V * k) + (4 * U * V * u)) = 0 := by
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  simp [perm4, Matrix.of_apply, blockA, blockB, gauged] at h1 hm1 h2 hm2
  linear_combination (2/3:ℂ)*h1-(2/3:ℂ)*hm1-(1/12:ℂ)*h2+(1/12:ℂ)*hm2+(((a * (V ^ 2)) + (b * (V ^ 2)) + (c * (U ^ 2)) + (d * (U ^ 2)) + ((-1) * U * a * (V ^ 2)) + ((-1) * U * b * (V ^ 2)) + ((-1) * V * c * (U ^ 2)) + ((-1) * V * d * (U ^ 2)) + ((-2) * U * V * k) + ((-2) * U * V * u) + (2 * U * V * v) + (2 * U * V * w) + (U * b * h * (V ^ 2)) + (V * d * h * (U ^ 2)) + ((-1) * U * a * h * (V ^ 2)) + ((-1) * V * c * h * (U ^ 2))))*hh

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma gauged_zero (h a b c d u v w k : ℂ) (hh : h^2=2)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*gauged a b c d u v w k r s)=24) :
    gauged a b c d u v w k = 0 := by
  have h00 := gauged_first_order h a b c d u v w k 0 0 hh (hp 0 0)
  have h10 := gauged_first_order h a b c d u v w k 1 0 hh (hp 1 0)
  have h01 := gauged_first_order h a b c d u v w k 0 1 hh (hp 0 1)
  have h11 := gauged_first_order h a b c d u v w k 1 1 hh (hp 1 1)
  have l0 : (k + u + ((-1) * v) + ((-1) * w))=0 := by linear_combination (1/4:ℂ)*(h11-h10-h01+h00)
  have l1 : (a + b + c + d + (4 * v) + (4 * w))=0 := by linear_combination (1/6:ℂ)*h00-2*l0
  have l2 : ((a * ((-1) + ((-1) * h))) + (b * ((-1) + h)) + ((-4) * h * (u + ((-1) * w))))=0 := by linear_combination (1/2:ℂ)*(h10-h00)-2*h*l0
  have l3 : ((c * ((-1) + ((-1) * h))) + (d * ((-1) + h)) + ((-4) * h * (u + ((-1) * v))))=0 := by linear_combination (1/2:ℂ)*(h01-h00)-2*h*l0
  have heq : gauged a b c d u v w k = extension h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [gauged, extension] <;> try ring
    · linear_combination ((-1 / 2 : ℂ) * (v + ((-3) * w) + (2 * a) + (4 * u)))*hh
    · linear_combination (1 + h)*l2 + ((1 / 2 : ℂ) * (((-1) * v) + ((-5) * w) + ((-2) * b) + (4 * u)))*hh
    · linear_combination 1*l0
    · linear_combination ((1 / 2 : ℂ) + ((-1 / 4 : ℂ) * h))*l1 + ((-1 / 4 : ℂ) * h)*l2 + ((-1 / 4 : ℂ) * h)*l3 + ((1 / 4 : ℂ) * (b + d + ((-1) * c) + ((-2) * w) + (3 * a) + (6 * v)))*hh
    · linear_combination 1*l0
    · linear_combination ((1 / 2 : ℂ) + ((1 / 4 : ℂ) * h))*l1 + ((-1) + ((-3 / 4 : ℂ) * h))*l2 + ((1 / 4 : ℂ) * h)*l3 + ((-1 / 4 : ℂ) * (d + ((-1) * a) + ((-1) * c) + ((-6) * w) + ((-3) * b) + (2 * v)))*hh
  have hpE : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
    (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*extension h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) r s)=24 := by
    intro U V W
    rw [← heq]
    exact hp U V W
  obtain ⟨ht,hx,hy,hz⟩ := normalized_extension_zero h (((a * (1 + h)) + (u * (2 + (2 * h))) + ((-1) * (2 + h) * (((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) + (2 * h * (((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))))) ((((1 / 2 : ℂ) * v) + ((1 / 2 : ℂ) * w))) ((((1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) ((u + ((-1 / 2 : ℂ) * v) + ((-1 / 2 : ℂ) * w))) hh hpE
  rw [heq, ht, hx, hy, hz]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [extension]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_blocks_maximal (h : ℂ) (hh : h^2=2)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*blockA h r s+q*blockB h r s := by
  let G := gauged (C 0 0-(h-1)*C 0 1) (C 1 1-(-h-1)*C 0 1)
    (C 2 2-(h-1)*C 2 3) (C 3 3-(-h-1)*C 2 3) (C 0 2) (C 0 3) (C 1 2) (C 1 3)
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  have heq : C=Matrix.of fun (r s : Fin 4) =>
      C 0 1*blockA h r s+C 2 3*blockB h r s+G r s := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [G, gauged, blockA, blockB, Matrix.of_apply, h10, h20, h30, h21, h31, h32] <;> ring
  have hG : G=0 := by
    apply gauged_zero h _ _ _ _ _ _ _ _ hh
    intro U V W
    have he := hp (U-W*C 0 1) (V-W*C 2 3) W
    convert he using 1
    congr 1
    ext r s
    have hr := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M r s) heq
    simp only [Matrix.of_apply] at hr ⊢
    change (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*G r s = _
    linear_combination (-W)*hr
  refine ⟨C 0 1,C 2 3,heq.trans ?_⟩
  ext r s
  simp only [Matrix.of_apply, hG, Matrix.zero_apply, add_zero]

lemma block_root (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_roots_maximal (h k : ℂ) (hh : h^2=2) (hk : k^2=2)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB k r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*blockA h r s+q*blockB k r s := by
  by_cases hkh : k=h
  · subst k
    exact two_blocks_maximal h hh C hs hp
  have hprod : (k-h)*(k+h)=0 := by linear_combination hk-hh
  have hsum : k+h=0 := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hkh)
  have hkh : k= -h := by linear_combination hsum
  subst k
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  let C' : Matrix (Fin 4) (Fin 4) ℂ := C.submatrix σ σ
  have hs' (r s : Fin 4) : C' r s=C' s r := hs _ _
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C' r s)=24 := by
    let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s =>
      (1 : ℂ)+U*blockA h r s+V*blockB (-h) r s+W*C r s
    have heq : M.submatrix σ σ=Matrix.of (fun (r s : Fin 4) =>
        (1 : ℂ)+U*blockA h r s+V*blockB h r s+W*C' r s) := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp [M,C',σ,Matrix.submatrix_apply,Matrix.of_apply,blockA,blockB,Equiv.swap_apply_def] <;> ring
    have hinv : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
      change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
      rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
    rw [← heq]
    exact hinv.trans (hp U V W)
  obtain ⟨p,q,hC⟩ := two_blocks_maximal h hh C' hs' hp'
  refine ⟨p,q,?_⟩
  have heq := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.submatrix σ σ) hC
  have hCinv : C'.submatrix σ σ=C := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [C',σ,Matrix.submatrix_apply,Equiv.swap_apply_def]
  rw [hCinv] at heq
  apply heq.trans
  ext r s
  change p*blockA h (σ r) (σ s)+q*blockB h (σ r) (σ s)=_
  fin_cases r <;> fin_cases s <;> simp [σ,blockA,blockB,Equiv.swap_apply_def] <;> ring

def topBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![a,b,0,0],![b,c,0,0],![0,0,0,0],![0,0,0,0]]

def bottomBlock (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,0],![0,0,0,0],![0,0,a,b],![0,0,b,c]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma disjoint_blocks_maximal (a b c d e f : ℂ)
    (hA : a≠0 ∨ b≠0 ∨ c≠0) (hB : d≠0 ∨ e≠0 ∨ f≠0)
    (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ r s : Fin 4, C r s=C s r)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock a b c r s+V*bottomBlock d e f r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*topBlock a b c r s+q*bottomBlock d e f r s := by
  have hA1 := hp 1 0 0
  have hAm := hp (-1) 0 0
  have hB1 := hp 0 1 0
  have hBm := hp 0 (-1) 0
  simp [perm4,Matrix.of_apply,topBlock,bottomBlock] at hA1 hAm hB1 hBm
  have hAS : a+c+2*b=0 := by linear_combination (1/12:ℂ)*(hA1-hAm)
  have hAQ : a*c+b^2=0 := by linear_combination (1/4:ℂ)*(hA1+hAm)
  have hBS : d+f+2*e=0 := by linear_combination (1/12:ℂ)*(hB1-hBm)
  have hBQ : d*f+e^2=0 := by linear_combination (1/4:ℂ)*(hB1+hBm)
  obtain ⟨hb,h,hh,ha,hc⟩ := block_root a b c hAS hAQ hA
  obtain ⟨he,k,hk,hd,hf⟩ := block_root d e f hBS hBQ hB
  have heqA : topBlock a b c=Matrix.of (fun (r s : Fin 4) => b*blockA h r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,blockA,ha,hc] <;> ring_nf <;> simp
  have heqB : bottomBlock d e f=Matrix.of (fun (r s : Fin 4) => e*blockB k r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottomBlock,blockB,hd,hf] <;> ring_nf <;> simp
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*blockA h r s+V*blockB k r s+W*C r s)=24 := by
    have hp0 := hp (U/b) (V/e) W
    rw [heqA,heqB] at hp0
    simpa only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ U hb,div_mul_cancel₀ V he] using hp0
  obtain ⟨p,q,hC⟩ := two_roots_maximal h k hh hk C hs hp'
  refine ⟨p/b,q/e,hC.trans ?_⟩
  ext r s
  rw [heqA,heqB]
  simp only [Matrix.of_apply,← mul_assoc,div_mul_cancel₀ p hb,div_mul_cancel₀ q he]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma two_double_kernel_rows_maximal (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s : Fin 4, A r s=A s r)
    (hsB : ∀ r s : Fin 4, B r s=B s r)
    (hsC : ∀ r s : Fin 4, C r s=C s r)
    (hA2 : ∀ j : Fin 4, A 2 j=0) (hA3 : ∀ j : Fin 4, A 3 j=0)
    (hB0 : ∀ j : Fin 4, B 0 j=0) (hB1 : ∀ j : Fin 4, B 1 j=0)
    (hA : A≠0) (hB : B≠0)
    (hp : ∀ U V W : ℂ, Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*A r s+V*B r s+W*C r s)=24) :
    ∃ p q : ℂ, C=Matrix.of fun (r s : Fin 4) => p*A r s+q*B r s := by
  have heqA : A=topBlock (A 0 0) (A 0 1) (A 1 1) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [topBlock,hA2,hA3,hsA 0 2,hsA 0 3,hsA 1 2,hsA 1 3,hsA 1 0]
  have heqB : B=bottomBlock (B 2 2) (B 2 3) (B 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [bottomBlock,hB0,hB1,hsB 2 0,hsB 3 0,hsB 2 1,hsB 3 1,hsB 3 2]
  have hAne : A 0 0≠0 ∨ A 0 1≠0 ∨ A 1 1≠0 := by
    by_contra hn
    have ha : A 0 0=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : A 0 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : A 1 1=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hA
    apply heqA.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [topBlock,ha,hb,hc]
  have hBne : B 2 2≠0 ∨ B 2 3≠0 ∨ B 3 3≠0 := by
    by_contra hn
    have ha : B 2 2=0 := Classical.not_not.mp (fun h => hn (Or.inl h))
    have hb : B 2 3=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inl h)))
    have hc : B 3 3=0 := Classical.not_not.mp (fun h => hn (Or.inr (Or.inr h)))
    apply hB
    apply heqB.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottomBlock,ha,hb,hc]
  have hp' (U V W : ℂ) : Matrix.permanent (Matrix.of fun (r s : Fin 4) =>
      (1 : ℂ)+U*topBlock (A 0 0) (A 0 1) (A 1 1) r s+
      V*bottomBlock (B 2 2) (B 2 3) (B 3 3) r s+W*C r s)=24 := by
    have hc := hp U V W
    rw [heqA,heqB] at hc
    exact hc
  obtain ⟨p,q,hC⟩ := disjoint_blocks_maximal (A 0 0) (A 0 1) (A 1 1)
    (B 2 2) (B 2 3) (B 3 3) hAne hBne C hsC hp'
  refine ⟨p,q,hC.trans ?_⟩
  rw [← heqA,← heqB]

end MatrixBridge

end PEqualNP.Outside.L_gct_231.TwoBlock


namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate

def ca (x y : ℂ) : ℂ := x + y
def cm (x y : ℂ) : ℂ := x * y
def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n
def cz (z : ℤ) : ℂ := z

def coeff0 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (cz (-311313128810047156336526740557679240108508827091132262748278977062207624025388)) (ca (cm (cz (-286351355579144035443790177534212101710614324232003829220578735052897960417240)) (a)) (cm (cz (-286351355579144035443790177534212101710614324232003829220578735052897960417240)) (c)))) (ca (ca (cm (cz (-54928594602952607926580102302937282905217326600492585468079032422803082210792)) (d)) (cm (cz (-19323000402455513947683811882090627990528128137916547152151628017568147679144)) (b))) (ca (cm (i) (ca (cz (-50740589771513313322342701084494075146901954428673113063618900535322817498512)) (ca (cm (cz (-59191945923049332811759399982574766939624839481469743922216323868399965228728)) (a)) (cm (cz (-59191945923049332811759399982574766939624839481469743922216323868399965228728)) (c))))) (cm (j) (ca (ca (cz (6959303398381142769539594587135296385282056778130747127832671588013500878676)) (cm (cz (-59191945923049332811759399982574766939624839481469743922216323868399965228728)) (b))) (ca (cm (cz (-59191945923049332811759399982574766939624839481469743922216323868399965228728)) (d)) (cm (cz (177575837769147998435278199947724300818874518444409231766648971605199895686184)) (i)))))))

def coeff1 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-94443696649974074764053127839984204662010772959130917499187609771909075223732)) (cm (cz (-178171634280127912726992098680874070137333065317997779442462941351147960611388)) (i))) (ca (cm (cz (-52213632645606554665921627959932068566702162698778286852755963803619197004768)) (c)) (cm (cz (-48400908773071325687346572784727180227833540783604178849719495962311500888480)) (a)))) (ca (ca (cm (cz (4618316774020583697790756623466222941073239006018431227256982586310209742256)) (d)) (cm (cz (38440314232044503121562593033703146001216785940307715625413508072551560084208)) (b))) (ca (cm (cz (83266116207469490685308522567099783391493721363948193652236875225556840058464)) (j)) (cm (rr) (ca (ca (cz (201688564519269233205306387870921907557746496211937034803006140877138545874544)) (cm (cz (16490032859944971168233703275257992806610864011017295732712921965882084221440)) (d))) (ca (cm (cz (88719646779088197141880226869807288031674310405117744870491049455060843134600)) (i)) (cm (cz (92768447161282789614526410482231347936023530553216122860819324791194569157448)) (j)))))))

def coeff2 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-831430430139819775351419597903705210018628051233146725610390296141032660395192)) (cm (a) (ca (cz (806252079938511032866892857793761120654120512999349217656212056303419667825522)) (cm (cz (222190177201134664759990367603095665725137762376336323772605338683526859787880)) (a))))) (ca (cm (b) (ca (cz (94753908228382438150916146125445577905417060793791725652764958772996192249490)) (ca (cm (cz (5085577709058938559764029893048814091724011161273255615226863877010525984072)) (a)) (cm (cz (33668768948778876660309631477664157286878212508094215161186039243722285171824)) (b))))) (cm (c) (ca (ca (cz (1111410895721950293196203166677185290222531872300464936927719999546253355547862)) (cm (cz (-138408117794862551446366545320836975584386408739457979535024052859717058933888)) (c))) (ca (cm (cz (36799858993534040315701373758455326978030580790530678700761062168700904476384)) (b)) (cm (cz (404314052299504381543004774790037393667082418503187370534944879463972515388904)) (a))))))) (ca (ca (cm (d) (ca (ca (cz (382002723202467759571263315295034488144920591339961225805997408461897993744174)) (cm (cz (-88867637115331051873387852175307504232475364798151599852808149700820326838064)) (c))) (ca (cm (cz (-33668768948778876660309631477664157286878212508094215161186039243722285171824)) (d)) (ca (cm (cz (13437598527348784780802646443796238988610547781501109539958463488401351678616)) (a)) (cm (cz (67337537897557753320619262955328314573756425016188430322372078487444570343648)) (b)))))) (cm (i) (ca (ca (cz (1946683099015352296832871620707556956405128550505607207400041919933588894121419)) (ca (cm (cz (-446968439604423632906156487885650471036508574900492341592138329785115990357252)) (b)) (cm (cz (-313178892452698198058920901765438404771209247722430705533861285360608821264180)) (d)))) (ca (cm (a) (ca (cz (-155781328862311342365671623583965772216470065052645263165438275947298079765056)) (cm (cz (7279484125134573974490064016575373515024420708940476589779181962534756686504)) (a)))) (ca (cm (c) (ca (cz (-64980179144157145431983100645441054836162792302490805691870488136919033279396)) (ca (cm (cz (-91061543531406687288113886298834063655775774345818820827360467786344557540496)) (c)) (cm (cz (54625270353034095925956088449304684813241947667366230189824161828150717559864)) (a))))) (cm (i) (ca (ca (cz (491688640855633729296291521363510783605919941003242538947151359239066526173046)) (ca (cm (cz (-140279182682804802614934690932978401786251035939534218685365172254289032513674)) (b)) (cm (cz (-18667955186469184651216921788461780248251088762238123451562497427887907906002)) (d)))) (ca (cm (cz (46680055940695480498986281822120229419819801876413596426872781661127711358438)) (a)) (ca (cm (cz (78633340534461578381395668160471724212198402448404552051146547391317029097566)) (c)) (cm (cz (374230238988247155991363831575919896152171714165893522121501794363699379254155)) (i))))))))))) (ca (cm (j) (ca (ca (cz (1041194197917331334693416015847502237965708522492330363136459651870758706861747)) (ca (cm (cz (-336450479883227487488653277902535434268224019279093986468028813821691899466880)) (a)) (cm (b) (ca (cz (469032577030311406136998294235403477801689334885346305414957828190999972865612)) (cm (cz (61924180754518530645299891349206313961972229943181810623923541863445502520424)) (a)))))) (ca (ca (cm (c) (ca (cz (-207649847191659035349077343863997573698401675090117069329748567623460834168896)) (cm (cz (21857878651753582668323930933052376178779123693696533613657743960364298333568)) (b)))) (cm (d) (ca (cz (611643589555510379320385594838948886017532543180140586969696628522203680981704)) (ca (cm (cz (21857878651753582668323930933052376178779123693696533613657743960364298333568)) (c)) (cm (cz (61924180754518530645299891349206313961972229943181810623923541863445502520424)) (a)))))) (ca (cm (i) (ca (ca (cz (3797046398444786466101045741307912016586344136430995833505533609047845111425302)) (cm (cz (-57946247548418835573354948685252672035373945613403320262009698244895279959093)) (i))) (ca (cm (cz (84718706051894993584608971248904213326474965879949171597243955919171684316632)) (a)) (cm (cz (163934089888151870012429481997892821340843427702724002102433079702732237501760)) (c))))) (cm (j) (ca (ca (cz (983604539328911220074576891987356928045060566216344012614598478216393425010560)) (cm (cz (-163934089888151870012429481997892821340843427702724002102433079702732237501760)) (b))) (ca (cm (cz (-163934089888151870012429481997892821340843427702724002102433079702732237501760)) (d)) (cm (cz (1180325447194693464089492270384828313654072679459612815137518173859672110012672)) (i))))))))) (cm (rr) (ca (ca (cz (954198820906788476135216131709857569349558382860502398324649851874349310440964)) (ca (cm (a) (ca (cz (-175592386229050141548651771672783858803818732351278179796270044738611575210364)) (cm (cz (-39571064894786590181935387631432512784350047700258905132608434413961265004096)) (a)))) (cm (b) (ca (cz (-259449539674241910328765146150953617916906459997136026585906547234832226236232)) (ca (cm (cz (-33559116442534358509302574209331181554632942137609268901823240916878747463776)) (b)) (cm (cz (34427812032105071205956936150956204726584571562818189649687312450188562581824)) (a))))))) (ca (ca (cm (c) (ca (ca (cz (-74383567744103011491129333632319579595002766963481958789261004533980153988508)) (cm (cz (-79142129789573180363870775262865025568700095400517810265216868827922530008192)) (a))) (ca (cm (cz (39571064894786590181935387631432512784350047700258905132608434413961265004096)) (c)) (cm (cz (43642243414911876235029167960766720226606298152463257126507154938920725321784)) (b))))) (cm (d) (ca (ca (cz (-244167553067670993451159718067778295453280030658413425547069339651548453529784)) (cm (cz (-67118232885068717018605148418662363109265884275218537803646481833757494927552)) (b))) (ca (cm (cz (-34427812032105071205956936150956204726584571562818189649687312450188562581824)) (c)) (ca (cm (cz (25213380649298266176884704341145689226562844973173122172867469961456399841864)) (a)) (cm (cz (33559116442534358509302574209331181554632942137609268901823240916878747463776)) (d))))))) (ca (cm (i) (ca (ca (cz (2368084918263129738460587065526637914908068874229740022434378839427877248901768)) (ca (cm (cz (-643314508931157692251280576619282403280054037848148867835921194896300543251428)) (i)) (cm (cz (-405042695070891174302321824520252339895377827871991087480353248129445904502940)) (c)))) (ca (cm (cz (-351254388202852772105116833104806171620646290236514536072117720227616885038304)) (a)) (ca (cm (cz (-84837683731731263390061963439905958758075367672325621420736572723940104381860)) (d)) (cm (cz (51232883999114628855444829217722818530797192819585323373287850279416629324976)) (b)))))) (cm (j) (ca (ca (cz (1071731321475008676557189478892334509461691821161563895040683236673738219049208)) (cm (cz (-214737313563140035710413045916875162944351563109056437868492986441765832336972)) (a))) (ca (cm (cz (-29947980925479349827695891196588397971375397722472084988475916768521117725968)) (b)) (ca (cm (cz (69688928183307320972805609653219153910852465487828050673275123272087720932532)) (d)) (cm (cz (3151216596576579434103562025864756424073995076666451789339624235990517214180640)) (i))))))))))))

def coeff3 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-111260092565267347705629626732584737428811680220196396964495364116087674095924)) (cm (cz (-62043325320121407962137236015528727495509560142705734645267647597843628133516)) (j))) (ca (cm (cz (-53940193713853319012564094131049061586246345337501000216284514443756274050448)) (i)) (cm (cz (-30788302107273089442972282507744375439264159097184261130783803136790081203056)) (a)))) (ca (ca (cm (cz (-30282811342523306786523758993281145344649028862740556775570749801381422452400)) (c)) (cm (cz (-17439287111104004239100853599556646149485722435725662458881818432527062592896)) (rr))) (ca (cm (cz (45313736972621666824431249428206275127639192751222348605060153127479828156032)) (d)) (cm (cz (71025676906064070811355637910474478664453673694516168501241198978976068728256)) (b))))

def coeff4 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-5627193850839047085276560894836294927469005273558933179455241225164679409660092)) (cm (a) (ca (cz (251150489345290174289673298993167146265198771839485529706354276396791962393796)) (cm (cz (-61642978278170456835748096491710342928389342759419023066367510255453625832144)) (a))))) (ca (cm (b) (ca (cz (-423252293913203386451845414577845182760839561850877677542195096723936301573340)) (ca (cm (cz (-27429331980788747900170337387564503641588427134292129734171773286129217041360)) (b)) (cm (cz (130967212278551205545058205193935308064254517925391079380229477509779379198144)) (a))))) (cm (c) (ca (ca (cz (61185724461295298488155098701308485152452744428424768156506537172932331588844)) (cm (cz (-203418560761870809625448113815728561423164898017808600153266616317069660038000)) (a))) (ca (cm (cz (139432115945293181749633556338689156511485002708078643500708354745359520505152)) (b)) (cm (cz (229207097090714683462995741056227723209892050033175711541530081903073227540128)) (c))))))) (ca (ca (cm (d) (ca (ca (cz (-109512502940319191664149228410756572554536085910342772920582745774317414343444)) (cm (cz (-130967212278551205545058205193935308064254517925391079380229477509779379198144)) (c))) (ca (cm (cz (-43164584185194083454523918142097446031279254234304833013060164284866035014512)) (b)) (ca (cm (cz (104011605775858452375933562142675150033480175829740273995783129521729691718048)) (d)) (cm (cz (122502308611809229340482854049181459617024033142703515259750600274199237891136)) (a)))))) (cm (i) (ca (ca (cz (-291245251184031462655174417034033521346062941543925281777826740504557282212022)) (ca (cm (cz (-128663163800740530182868270454624804949348661458673740901684698040652568105868)) (c)) (cm (cz (-106146597004920433919798849039040636956885486711669561084845568177263830206796)) (a)))) (ca (cm (b) (ca (cz (6487678425730822498944090145354347473366914600983622965210758271111110650476)) (cm (cz (-55172720982158198013487488367588879777368342956079731698059211576870546090560)) (b)))) (ca (cm (d) (ca (cz (208777738796030070928817611457658406696343316570866392281269602571014649391652)) (ca (cm (cz (-122039521740699808372791733368209320806634285946438889851401805441133491249328)) (b)) (cm (cz (-21409552812911506462275736387521766614523405739368412563552144658729928586128)) (d))))) (cm (i) (ca (ca (cz (1952973104645668393710405701394995502698445312676419065318100479765904067560366)) (cm (cz (397243591071539025697109916246639934397052069283774068226026323353467931852032)) (d))) (ca (cm (cz (438623131808157674207225532522331594230078326500833866999570732036120841419952)) (b)) (cm (cz (695176284375193294969942353431619885194841121246604619395546065868568880741056)) (i)))))))))) (ca (cm (j) (ca (ca (cz (-3684387127397297722638802633256180528518705629262802042450405990724975892412806)) (ca (cm (cz (-464983491653151657709976837930767096127727095957839365952101944075825119549644)) (b)) (cm (cz (-135377531129736520182663895659778622727910318620830604467081420392309306458156)) (d)))) (ca (ca (cm (a) (ca (cz (-220793993652972673538899882307616247367695858217342237268341121733084081591668)) (cm (cz (-54644696629383956670809827332630940446947809234241334034144359900910745833920)) (a)))) (cm (c) (ca (cz (-416366224142132506863376935398775822907046440916185065461383003876114049541916)) (ca (cm (cz (-112919422183160269956437817231886439834554898039515354441018211746708855874064)) (c)) (cm (cz (-29156789053238017387667733832954005327509405969512114047757123995659083294128)) (a)))))) (ca (cm (i) (ca (ca (cz (428455822214846121874762680921355555982179401705573251082234278254334427680952)) (ca (cm (cz (-280558365365609605229869381865956803572502071879068437370730344508578065027348)) (b)) (cm (cz (-37335910372938369302433843576923560496502177524476246903124994855775815812004)) (d)))) (ca (cm (cz (93360111881390960997972563644240458839639603752827192853745563322255422716876)) (a)) (ca (cm (cz (157266681068923156762791336320943448424396804896809104102293094782634058195132)) (c)) (cm (cz (748460477976494311982727663151839792304343428331787044243003588727398758508310)) (i)))))) (cm (j) (ca (ca (cz (1191118243670697026073057571043870757672832736383216591001190664647557409853830)) (cm (cz (-115892495096837671146709897370505344070747891226806640524019396489790559918186)) (i))) (ca (cm (cz (393441815731564488029830756794942771218024226486537605045839391286557370004224)) (c)) (ca (cm (cz (434425338203602455532938127294415976553235083412218605571447661212240429379664)) (a)) (cm (cz (688523177530237854052203824391149849631542396351440808830218934751475397507392)) (j)))))))))) (cm (rr) (ca (ca (cz (-961842125980109893971299400736268208889343779929600097953347535282988587953808)) (ca (cm (a) (ca (cz (1149613301236242224678288440083760445618242980162538055293619264036038731740608)) (cm (cz (13687595904578046292098591989376659999059903387708678533083845166742608951504)) (a)))) (cm (b) (ca (cz (-564831015462081954599839825666864869106245149986565050635588857899758073515152)) (ca (cm (cz (-63543487831826446345421799576661165185484902285878329336386403191999879480976)) (b)) (cm (cz (51911587566312496229713515648117114226151901208913233916980254779636238899136)) (a))))))) (ca (ca (cm (c) (ca (ca (cz (705215228094649465725409018988721164977386028918250177795970452664461528634512)) (cm (cz (-13687595904578046292098591989376659999059903387708678533083845166742608951504)) (c))) (ca (cm (cz (27375191809156092584197183978753319998119806775417357066167690333485217903008)) (a)) (cm (cz (72827534866934724939392846982569127441634035265940885970441060106422226221072)) (b))))) (cm (d) (ca (ca (cz (-360781675544463042433775618868517604445102439238784955889860537685576163833152)) (cm (cz (-127086975663652892690843599153322330370969804571756658672772806383999758961952)) (b))) (ca (cm (cz (-51911587566312496229713515648117114226151901208913233916980254779636238899136)) (c)) (ca (cm (cz (30995640265690267520034184313665101010669767151885581863519449452850251577200)) (a)) (cm (cz (63543487831826446345421799576661165185484902285878329336386403191999879480976)) (d))))))) (ca (cm (i) (ca (ca (cz (1280188062406890281980063680313878678941636372644026078193484401414073373639960)) (cm (cz (-111069294252883990268546479999578883160052585521645100742049490181270089852024)) (c))) (ca (cm (cz (20381627333802999993458598582712952189602623874741939296958233862627907616280)) (d)) (cm (cz (41515555496364587487161546383215746291026024436335405885619339270279635956480)) (a))))) (cm (j) (ca (ca (cz (-1854702900591354352179883131462997914754488957955539950210473171230268155326520)) (cm (cz (-455629933394869427768878035711628816524149513443629842244656656775083880770664)) (c))) (ca (cm (cz (-371450445331425018732925161238531382045260446308179533437647053907712027867184)) (b)) (ca (cm (cz (-177555892617272959249004452311558676881837838349346114863756774209423877509512)) (d)) (cm (cz (280520071140158347247992290070076161848040098919502922722892263014978457162352)) (i))))))))))))

def coeff5 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (cz (-393853214658303865753169498025084206874429653531321041258206995245791758380188)) (ca (cm (cz (-127761596999131284198148350120303653965023192714092058276739802536872575155992)) (b)) (cm (cz (-127761596999131284198148350120303653965023192714092058276739802536872575155992)) (d)))) (ca (ca (cm (cz (-3294906595908533165124455856078481332237439924949237386728123620269516056744)) (a)) (cm (cz (15978780984391490200795993580654164564240948662629027655914893916448262310424)) (c))) (ca (cm (i) (ca (cz (-66179788218749586063166171681092442333930559029546371618642423379550187351348)) (ca (cm (cz (-13463412455563663131812242612140327296130120017488192866679032908208491597592)) (a)) (cm (cz (-13463412455563663131812242612140327296130120017488192866679032908208491597592)) (c))))) (cm (j) (ca (ca (cz (-173765323881610377053385974813213110870862991780006939418982993651376012249144)) (cm (cz (-13463412455563663131812242612140327296130120017488192866679032908208491597592)) (b))) (ca (cm (cz (-13463412455563663131812242612140327296130120017488192866679032908208491597592)) (d)) (cm (cz (40390237366690989395436727836420981888390360052464578600037098724625474792776)) (i)))))))

def coeff6 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-1172915178199935308380839085968723869773233832817453956946980982925081794173244)) (cm (a) (ca (cz (-39120542608943075159323368251774113788255254563659755223751730880406042427470)) (cm (cz (-73686848080143998814237682261515208707245823453488129547094756931873093632560)) (a))))) (ca (cm (b) (ca (cz (645006402362424665081830597703070177244759907640223666889442945788081707464178)) (ca (cm (cz (40327289334411055657132417711448644382291925246080380717794805860241628486280)) (a)) (cm (cz (84693203285555493155826010219510249103053529679060472140989826551729568583368)) (b))))) (cm (c) (ca (ca (cz (220030982776773849954670506791698049413974015425620732114514694824787975486414)) (cm (cz (-147373696160287997628475364523030417414491646906976259094189513863746187265120)) (a))) (ca (cm (cz (60414158861039813900513943913071970710599986858720221151618124290253473914456)) (b)) (cm (cz (73686848080143998814237682261515208707245823453488129547094756931873093632560)) (c))))))) (ca (ca (cm (d) (ca (ca (cz (436103222141411517847803361962857484446320575361204004142280618156220172013942)) (cm (cz (-78618426231945907895014030089003967578237799593804452848600483978041865824624)) (c))) (ca (cm (cz (-46402066388020640917944397841954925907107655331336400010184148433929331245024)) (d)) (ca (cm (cz (14393379919590591240842513193309537428035063616300827056329796286533583524000)) (a)) (cm (cz (175233446459302692484560398755536278832055859375260657509621344247155336700840)) (b)))))) (cm (i) (ca (ca (cz (640533148146427373157329650214422498706524477772710091821171428117668355337035)) (ca (cm (cz (-265028385710613292957851930670693671133224922593883431327023337528054182876660)) (a)) (cm (b) (ca (cz (-204792800159383362073934551246191838355149917058875379184633579917533690331728)) (cm (cz (16222048504671573032486617030519771284998537165292179451581993487052018902120)) (a)))))) (ca (cm (c) (ca (cz (12144424305188500165529315556278820665475616817035645391102615224486206931768)) (cm (cz (16222048504671573032486617030519771284998537165292179451581993487052018902120)) (b)))) (ca (cm (d) (ca (cz (-209656339732201152451252455796837743153999703233102980452625003992108075144128)) (ca (cm (cz (22069088392863279205394995347035551910947337182431892679223684630748218436224)) (a)) (cm (cz (22069088392863279205394995347035551910947337182431892679223684630748218436224)) (c))))) (cm (i) (ca (cz (993108977678847564242774790616599835992630173209435170565065808383669829630080)) (ca (cm (cz (-165518162946474594040462465102766639332105028868239195094177634730611638271680)) (a)) (cm (cz (-165518162946474594040462465102766639332105028868239195094177634730611638271680)) (c)))))))))) (ca (cm (j) (ca (ca (cz (504378389559546914053998087817489445199286655594929123414264514808879021806539)) (ca (cm (cz (-171469398521199765251561173278676499279978679249290265790235599816483377411604)) (c)) (cm (cz (-102447974235758856836965413284226265197161100715734519710062478761594357066484)) (a)))) (ca (ca (cm (b) (ca (cz (441240527018229647883011613698795333134005326171893568887407532548063346579136)) (cm (cz (-38950672477486624981000871337069108492369805790787552246477218089818527188440)) (b)))) (cm (d) (ca (cz (187018447908468359931553478846563666087576882896011317139966341658489280763148)) (ca (cm (cz (-83748384843164956134910120990653997610688411598714817720596127323333253910984)) (b)) (cm (cz (659535579951772743119258959513785296423931443063480115671539972018289850096)) (d)))))) (ca (cm (i) (ca (ca (cz (2677603778238227802969616046732968782633250317305597176943288237987899529170926)) (cm (cz (165518162946474594040462465102766639332105028868239195094177634730611638271680)) (d))) (ca (cm (cz (224438823347668361069303216328005641042977686136718133550647116844353146441912)) (b)) (cm (cz (1191730773214617077091329748739919803191156207851322204678078970060403795556096)) (i))))) (cm (j) (ca (ca (cz (-11004745848841177551977514194315708257443116264397277976696960122672649570502)) (ca (cm (cz (-140279182682804802614934690932978401786251035939534218685365172254289032513674)) (b)) (cm (cz (-57946247548418835573354948685252672035373945613403320262009698244895279959093)) (j)))) (ca (ca (cm (cz (-18667955186469184651216921788461780248251088762238123451562497427887907906002)) (d)) (cm (cz (46680055940695480498986281822120229419819801876413596426872781661127711358438)) (a))) (ca (cm (cz (78633340534461578381395668160471724212198402448404552051146547391317029097566)) (c)) (cm (cz (374230238988247155991363831575919896152171714165893522121501794363699379254155)) (i)))))))))) (cm (rr) (ca (ca (cz (-279976819533117607183130090537090026736137093388224800724374556121227803895632)) (ca (cm (a) (ca (cz (261593830199318695596377658009777394970679861314288997442094475406742151428376)) (cm (cz (23824258455452755625386235094285608413951482051116705529793530555058795504672)) (a)))) (cm (b) (ca (cz (176538104946376897504634017502155163033570901754582013015907489903480852240212)) (ca (cm (cz (-140581207953184692012367782982280799312007582616428099751352343865136976784064)) (a)) (cm (cz (18240669271604601936252970135378408962153908704795706871623330775551260831872)) (b))))))) (ca (ca (cm (c) (ca (ca (cz (-24678296692621842148691580682754058816235670020071954583414346450134405460200)) (cm (cz (-123191913966385547438876654907165151351508255502471976303000397418802617977544)) (b))) (ca (cm (cz (-23824258455452755625386235094285608413951482051116705529793530555058795504672)) (c)) (cm (cz (47648516910905511250772470188571216827902964102233411059587061110117591009344)) (a))))) (cm (d) (ca (ca (cz (78761870703637271537674102598910330348286552692609868885267316276510762059268)) (cm (cz (-157970501939983836585858911057396447272506909730384223199704290311471335590584)) (a))) (ca (cm (cz (-18240669271604601936252970135378408962153908704795706871623330775551260831872)) (d)) (ca (cm (cz (36481338543209203872505940270756817924307817409591413743246661551102521663744)) (b)) (cm (cz (140581207953184692012367782982280799312007582616428099751352343865136976784064)) (c))))))) (ca (cm (i) (ca (ca (cz (242473277722367436063825993795298766901813561722350482285702685372563815610592)) (cm (cz (-49642760056908319746810458183676260820501255273844890888381933746298437665036)) (c))) (ca (cm (cz (155109874315600732308776997355347633156606955880654314237351658985655730892900)) (b)) (cm (cz (185776228070510291519332125423432572893170228185199226904114149387049881268624)) (a))))) (cm (j) (ca (ca (cz (-1131398292770886915734039899932352823207974755606739825279740134806242872673160)) (cm (cz (-1081880954964941660337700147620315498884797193703418191050140333265777618234520)) (i))) (ca (cm (cz (-148184816673966203193036396976876085307602214703866809276659390635692377851364)) (c)) (ca (cm (cz (229191450440209201476779059763621626053991670170657104462570171209838454813876)) (d)) (cm (cz (263136450727422936320250720380139240716469685228902370086600690415382319362032)) (b))))))))))))

def coeff8 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (cz (218202458731672615763947798840653262573272020762949810482775405089648681770968)) (ca (cm (cz (-839904608255633912551609171745580720724180782651985815136880606807618851296)) (b)) (cm (cz (15450412081828212322461028487555097515076417644619515084116155927551324064000)) (d)))) (ca (ca (cm (cz (91483526692701349019204723597431906208950466472788172465045576319826473546320)) (a)) (cm (cz (91483526692701349019204723597431906208950466472788172465045576319826473546320)) (c))) (ca (cm (i) (ca (cz (-33437406578474840544095830095671101720886306053580085146755325836249067676660)) (ca (cm (cz (24590113483222780501864422299683923201126514155408600315364961955409835625264)) (a)) (cm (cz (24590113483222780501864422299683923201126514155408600315364961955409835625264)) (c))))) (cm (j) (ca (ca (cz (124573564124656507203576830818034111206887677872558236712154792605263101711004)) (cm (cz (-73770340449668341505593266899051769603379542466225800946094885866229506875792)) (i))) (ca (cm (cz (24590113483222780501864422299683923201126514155408600315364961955409835625264)) (b)) (cm (cz (24590113483222780501864422299683923201126514155408600315364961955409835625264)) (d)))))))

def coeff9 (a b c d i j rr : ℂ) : ℂ :=
  cz (83206468512539223883559538744238707809346388706164097524806910436341504261680)

def coeff10 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-95261738023247279292082829388693002315778550422928471221138316462915943753784)) (cm (cz (-25790630572340859524748304558180262189150177657549908957670642326115823728196)) (i))) (ca (cm (cz (-15434875459328507447209996831581686996482435523087902082365354902244171728708)) (j)) (cm (cz (16844107184939955659150103425897678329137555225602226638775355096217451901776)) (rr)))) (ca (ca (cm (cz (20510570021940246865355408860808056803892522224888583845140713074820705166784)) (d)) (cm (cz (22884763822962743173908975614178216988297310456664680695546560739086595599792)) (c))) (ca (cm (cz (26118555444239009452825095747357875319745443179844357958208500153298457075408)) (a)) (cm (cz (34319567968958420418630009048631732435214454486433968605552578993044093176064)) (b))))

def coeff11 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-801794087585063105487508714046881893601570937642795770161686618543710060488320)) (cm (cz (656067779936063887200058011883642497250303636186983099289617733881830000406304)) (a))) (ca (cm (b) (ca (cz (201840495455466075941661355905933720515647216244177396214669225431695861414752)) (ca (cm (cz (-22445051805912836736020967167516518237520045896935424456128414122429940878352)) (a)) (cm (cz (-926965879141075274045080179180330270814583026746445316128669866277440372288)) (b))))) (cm (c) (ca (cz (620687561645045985348372564183407345686991059397328965782841562102552613625488)) (cm (cz (-22445051805912836736020967167516518237520045896935424456128414122429940878352)) (b)))))) (ca (ca (cm (d) (ca (ca (cz (116532486353736657408497829735270616497091851157109328551154225479081598846096)) (cm (cz (-22445051805912836736020967167516518237520045896935424456128414122429940878352)) (a))) (ca (cm (cz (-1853931758282150548090160358360660541629166053492890632257339732554880744576)) (b)) (ca (cm (cz (926965879141075274045080179180330270814583026746445316128669866277440372288)) (d)) (cm (cz (22445051805912836736020967167516518237520045896935424456128414122429940878352)) (c)))))) (cm (i) (ca (ca (cz (-2002729942727607096586940752494216548072674316087536563283621620059612604129312)) (ca (cm (cz (-35529058814303311745609295007677490694085861181433474930284007398353842848864)) (d)) (cm (cz (45689101570586960269155416534105817168310221848254833567550873217050952174720)) (b)))) (ca (cm (cz (184969369221498838854917374844211758997095537569811191433606814566930447875568)) (c)) (ca (cm (cz (220349587512516740706602822544446910560408114359465324940382986346207834656384)) (a)) (cm (cz (318645342606294100453547340939755351793322913518397198071658144929694082407088)) (i))))))) (ca (cm (j) (ca (ca (cz (-1376908901722835550218641259146505490420418898363219442370306493836024138778048)) (ca (cm (cz (167266130920850352413490370825539726394769232060314663979336843972753966755584)) (b)) (cm (cz (173124620344045680501231027055983859100364673513884973212941206032831146578576)) (d)))) (ca (ca (cm (cz (207649847191659035349077343863997573698401675090117069329748567623460834168896)) (a)) (cm (cz (207649847191659035349077343863997573698401675090117069329748567623460834168896)) (c))) (ca (cm (i) (ca (cz (-2916333427587507805647115086863977020672135101366509094871565295977235639003952)) (ca (cm (cz (98360453932891122007457689198735692804506056621634401261459847821639342501056)) (a)) (cm (cz (98360453932891122007457689198735692804506056621634401261459847821639342501056)) (c))))) (cm (j) (ca (ca (cz (-360654997753934114027344860395364206949855540945992804625352775346010922503872)) (cm (cz (-295081361798673366022373067596207078413518169864903203784379543464918027503168)) (i))) (ca (cm (cz (98360453932891122007457689198735692804506056621634401261459847821639342501056)) (b)) (cm (cz (98360453932891122007457689198735692804506056621634401261459847821639342501056)) (d))))))))) (cm (rr) (ca (ca (cz (541213574567531389917218151853325691065797277164240129532994181829375918513248)) (ca (cm (cz (-873639335601573363471877752664239973803336433719938766795750927593054172401952)) (a)) (cm (cz (-837101252808037536220874434879954362225182878546295771808225698959585116339792)) (c)))) (ca (ca (cm (cz (-127136810748877936115052724796093763161634063112371515352613036871469335839776)) (b)) (cm (cz (-116265440310572600483310548178469075073374742657897057662638140652528695199888)) (d))) (ca (cm (i) (ca (cz (68334107524125584409216786678661237335937616309093491877740836751526279411760)) (ca (cm (cz (36538082793535827251003317784285611578153555173642994987525228633469056062160)) (c)) (cm (cz (105580826235108312706758384699235706371790609227849793069872999777064498754048)) (d))))) (cm (j) (ca (cz (473890448572905370820898412203590913919089921324034046365679451748666956602800)) (ca (cm (cz (-386150992952182826132088704450955866792835848621317651660082595402027014191344)) (d)) (cm (cz (-341779427762023186350377664861842244991311675894228860220068644760626741469376)) (b)))))))))))

def coeff13 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (-36136784299142834262096181880617261865136360030861912174279510582945145315896)) (cm (cz (-63544971128848602047550003698378819797130393150588708472836893586120729136144)) (d))) (ca (cm (cz (-38773209829427715186306538591537965456059681816589351920122398732068334294768)) (b)) (cm (cz (-22017956805627710484336008208778032047903065161088718906865563909879386450128)) (rr)))) (ca (ca (cm (cz (-18879133376472510929545493410259137508671567914360962478362413024873062300900)) (j)) (cm (cz (-7618409439626557976073548056759936165844426036697440445854728060130933372928)) (c))) (ca (cm (cz (-1953500962364711943292268790739451576799470384163508714273566240654763596480)) (a)) (cm (cz (53974810166650008041979856625976782639710574229597610761429085282468884411612)) (i))))

def coeff14 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (1533363332949046272664782423628415340138391950590741329405803844656919572525888)) (cm (a) (ca (cz (159432362859199087711861902345356799489533298532000503186690731059667775302400)) (cm (cz (22445051805912836736020967167516518237520045896935424456128414122429940878352)) (a))))) (ca (cm (b) (ca (cz (-701777141829118118650310399568607289867095951524781933355928442932014313884160)) (cm (cz (121054271992355339939717233379841442084078446167226193331614399841109116255376)) (b)))) (cm (c) (ca (cz (138107034752737099993394376916450657031506045075637514344644990133666730726624)) (ca (cm (cz (-22445051805912836736020967167516518237520045896935424456128414122429940878352)) (c)) (cm (cz (44890103611825673472041934335033036475040091793870848912256828244859881756704)) (a))))))) (ca (ca (cm (d) (ca (cz (-664119690282312273615756678595735268436226336208318301022493328832711130989344)) (ca (cm (cz (-121054271992355339939717233379841442084078446167226193331614399841109116255376)) (d)) (cm (cz (242108543984710679879434466759682884168156892334452386663228799682218232510752)) (b))))) (cm (i) (ca (ca (cz (2606141923169278273617242813653722954197122522423430730601147340550036546698112)) (ca (cm (cz (-232077934792104313199850110322546294736760908735907189682027413760435232243392)) (b)) (cm (cz (-206602345250881913687374078419217744210023478825461295507719944693891919425568)) (c)))) (ca (cm (cz (-119451182831542688005765181622149841066699565491134537548149039484510586570112)) (a)) (ca (cm (cz (-118586305255564149916398852117127653455172398617625161647106787125298723237568)) (d)) (cm (cz (888648605159688509542143043931734815707105822458238789601806513426272140503856)) (i))))))) (ca (cm (j) (ca (ca (cz (328837467810196986443379816924516582348667535526906702209702928473573167550592)) (ca (cm (cz (170202252781385192138245609674871780609040612480138956892681443511478842526768)) (j)) (cm (cz (188841958432222182335242128367827727544637924195679549072803794204165726707296)) (i)))) (ca (ca (cm (cz (256879484458681013502344641912621748514221648102285924439903594537422143417152)) (a)) (cm (cz (312756980631523776859346542421459580337763584469299625158144277423515784328768)) (c))) (ca (cm (cz (357996103586462279308781265715858598905366624191018200349867979231322818260192)) (d)) (cm (cz (378379718884292355808467103685288087934019438309298216678381141503625223206784)) (b)))))) (cm (rr) (ca (ca (cz (-844053165746787538304198947468302841996739884053514446940846236146314157154816)) (ca (cm (cz (-6104609297207465730139274581149896086275928567038106196142667942265355621696)) (a)) (cm (cz (56406048492742148863921565772822669926220004368921783128735041675148132566656)) (c)))) (ca (ca (cm (cz (123863111821849574697051842049296016718768614975855423972054106039451629585920)) (d)) (cm (cz (386269667881791003374188342103277868350632293427065898221142068141777823396544)) (b))) (ca (cm (i) (ca (cz (-764322385068715424551033253466861826710848566469880677394917700732383274137472)) (cm (cz (12172767183306277300755671861475169530488816889673345384993556700689902796160)) (c)))) (cm (j) (ca (cz (-79730780678072113753165694001441015285891317583633769545928535413930883017344)) (ca (cm (cz (223017855795652551593067515986278578596887078066331575549341382918722897527296)) (d)) (cm (cz (422006741082562899705828613523274821809979479632357816304093825772161992239232)) (b)))))))))))

def coeff15 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (cz (149260565473868310595386047230827071098878651812646043051198796002228357695240)) (ca (cm (cz (-55546267667037877427351294265416050170072233040198766860689260435672919624160)) (c)) (cm (cz (-50024138878018241770676629416089553811380301051720987755306420772934922934464)) (a)))) (ca (ca (cm (cz (70654754204654890049066084084587844750653834513071451984779581773578279617904)) (b)) (cm (cz (70654754204654890049066084084587844750653834513071451984779581773578279617904)) (d))) (ca (cm (i) (ca (cz (64074884695039705586522641548825981523949190003122756935553959883819329843476)) (ca (cm (cz (24827724441971189106069369765414995899815754330235879264126645209591745740752)) (a)) (cm (cz (24827724441971189106069369765414995899815754330235879264126645209591745740752)) (c))))) (cm (j) (ca (ca (cz (-50620090199475840853643088151083094474644578755829829192004807308420791103996)) (cm (cz (-74483173325913567318208109296244987699447262990707637792379935628775237222256)) (i))) (ca (cm (cz (24827724441971189106069369765414995899815754330235879264126645209591745740752)) (b)) (cm (cz (24827724441971189106069369765414995899815754330235879264126645209591745740752)) (d)))))))

def coeff16 (a b c d i j rr : ℂ) : ℂ :=
  ca (ca (ca (cz (90745476869902555289545286436731208586594788486386499331173468578191057539584)) (cm (a) (ca (cz (-200761069255047273509508895143313625705157121764857568943799790770843515230624)) (cm (cz (926965879141075274045080179180330270814583026746445316128669866277440372288)) (a))))) (ca (cm (b) (ca (cz (327575830250979999886893661667035483397962050176867886417894861652244583581984)) (cm (cz (-121054271992355339939717233379841442084078446167226193331614399841109116255376)) (a)))) (cm (c) (ca (ca (cz (-336984277208294268784353894994623765627520912100868525304526681676488956023792)) (cm (cz (-121054271992355339939717233379841442084078446167226193331614399841109116255376)) (b))) (ca (cm (cz (-926965879141075274045080179180330270814583026746445316128669866277440372288)) (c)) (cm (cz (1853931758282150548090160358360660541629166053492890632257339732554880744576)) (a))))))) (ca (ca (cm (d) (ca (cz (107434513060941112502202567859830623949600758673644266875422482394925887961104)) (ca (cm (cz (-121054271992355339939717233379841442084078446167226193331614399841109116255376)) (a)) (cm (cz (121054271992355339939717233379841442084078446167226193331614399841109116255376)) (c))))) (cm (i) (ca (ca (cz (6658478628750092733165982560500976166480958500059514471268788915804577761088)) (ca (cm (cz (55709898808544901051468622232696963532025027443306807824728959535446744457616)) (c)) (cm (cz (209656339732201152451252455796837743153999703233102980452625003992108075144128)) (b)))) (ca (cm (cz (209656339732201152451252455796837743153999703233102980452625003992108075144128)) (d)) (ca (cm (cz (268409861904175361911849027310306982892868510020268611371282503812845282697856)) (a)) (cm (i) (ca (cz (-364139958482244106889017423226086606530631063510126229207190796407345604197696)) (ca (cm (cz (99310897767884756424277479061659983599263017320943517056506580838366982963008)) (a)) (cm (cz (99310897767884756424277479061659983599263017320943517056506580838366982963008)) (c)))))))))) (ca (cm (j) (ca (ca (cz (-858649378702701814003658936648929304642825932452616834091661921758402355088032)) (ca (cm (cz (-166160585554494014305249370089063167368264733495765463833608942610033788624208)) (j)) (cm (cz (-160901690418807204517048901505336183876149913685941782175999400049006576288144)) (d)))) (ca (ca (cm (cz (-145758333136160582906559692717003853608987982194076891728901908095243805730176)) (a)) (cm (cz (-124732140685681359070235986753821104992574370636664423916047604987021629447520)) (c))) (ca (cm (cz (59239626771231682867642192301868675572211377817281837366472979208312119332736)) (b)) (cm (i) (ca (ca (cz (-1048425744665142891496780479965250363557443993449950787332756560423358903547696)) (cm (cz (-297932693303654269272832437184979950797789051962830551169519742515100948889024)) (i))) (ca (cm (cz (99310897767884756424277479061659983599263017320943517056506580838366982963008)) (b)) (cm (cz (99310897767884756424277479061659983599263017320943517056506580838366982963008)) (d))))))))) (cm (rr) (ca (ca (cz (-24165055567551502474669609541367068929658867218722723078636225596030739981920)) (ca (cm (cz (-208964685829749190674497160194766047155941315711139092329625228289822633805856)) (a)) (cm (cz (-92169599700181062075659145875997948385280629082209318245842301807809672663088)) (c)))) (ca (ca (cm (cz (274566955828398652063749381357671530937451802095721566864518386998895143324048)) (d)) (cm (cz (496588630286480573699802321915731088777300632817534113093923868251101530406624)) (b))) (ca (cm (i) (ca (cz (-176707428456273581934632253321242678976881593599074959756240299310147348413872)) (cm (cz (53377415356537048034462611801782490351889409743745540589447407233125862044080)) (c)))) (cm (j) (ca (cz (253166433524659860643973723150865441780731548270965396939342968618363477558736)) (ca (cm (cz (-164521769221030920256923842908597147172681708140095326757574914985814581664784)) (d)) (cm (cz (57499905237051001379129097649462410667167122581717219471830566266391805417792)) (b)))))))))))

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma reduced_same_obstruction (a b c d i j rr : ℂ)
    (e0 : ca (ca (cz (2)) (cm (cz (-7)) (a))) (ca (cm (cz (2)) (c)) (ca (cm (j) (ca (ca (cz (2)) (cm (cz (-16)) (a))) (ca (cm (cz (-2)) (c)) (cm (cz (-9)) (cm (a) (j)))))) (cm (rr) (ca (cm (a) (ca (cz (-5)) (cm (cz (2)) (a)))) (ca (cm (c) (ca (cz (-2)) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a))))) (cm (j) (ca (cm (a) (ca (cz (-8)) (cm (cz (2)) (a)))) (ca (cm (c) (ca (cz (2)) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a))))) (cm (cz (-3)) (cm (a) (j))))))))))) = (0 : ℂ))
    (e1 : ca (ca (ca (cz (-2)) (cm (cz (-7)) (b))) (ca (cm (cz (-4)) (c)) (cm (cz (2)) (d)))) (ca (ca (cm (cz (14)) (a)) (cm (i) (ca (cz (-6)) (ca (cm (cz (2)) (c)) (cm (cz (16)) (a)))))) (ca (cm (j) (ca (ca (cz (4)) (ca (cm (cz (-16)) (b)) (cm (cz (-2)) (d)))) (ca (ca (cm (cz (2)) (c)) (cm (cz (16)) (a))) (ca (cm (cz (-9)) (cm (b) (j))) (cm (cz (18)) (cm (a) (i))))))) (cm (rr) (ca (ca (cz (8)) (ca (cm (cz (-2)) (cp (a) 2)) (cm (b) (ca (cz (-5)) (cm (cz (4)) (a)))))) (ca (ca (cm (c) (ca (cm (cz (-4)) (a)) (ca (cm (cz (2)) (c)) (cm (cz (4)) (b))))) (cm (d) (ca (cz (-2)) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a)))))) (ca (cm (i) (ca (cz (4)) (ca (cm (cz (-2)) (cp (a) 2)) (cm (c) (ca (cm (cz (-4)) (a)) (cm (cz (2)) (c))))))) (cm (j) (ca (ca (cz (4)) (cm (b) (ca (cz (-8)) (cm (cz (4)) (a))))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a))))) (ca (cm (cz (-3)) (cm (b) (j))) (cm (cz (4)) (cm (b) (c))))))))))))) = (0 : ℂ))
    (e2 : ca (cz (-1)) (ca (cm (j) (ca (cz (-10)) (cm (cz (-9)) (j)))) (cm (rr) (ca (ca (cz (1)) (cm (cz (-2)) (a))) (ca (cm (cz (-2)) (c)) (cm (j) (ca (ca (cz (-2)) (cm (cz (-3)) (j))) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c))))))))) = (0 : ℂ))
    (e3 : ca (ca (ca (cz (-2)) (cm (cz (-7)) (a))) (ca (cm (cz (-4)) (d)) (cm (cz (2)) (c)))) (ca (ca (cm (cz (14)) (b)) (cm (i) (ca (ca (cz (4)) (ca (cm (cz (-16)) (a)) (cm (cz (-2)) (c)))) (ca (cm (cz (2)) (d)) (ca (cm (cz (16)) (b)) (cm (cz (-9)) (cm (a) (i)))))))) (ca (cm (j) (ca (ca (cz (-6)) (cm (cz (2)) (d))) (ca (cm (cz (16)) (b)) (cm (cz (18)) (cm (b) (i)))))) (cm (rr) (ca (ca (cz (-8)) (ca (cm (cz (5)) (a)) (cm (b) (ca (cm (cz (-4)) (a)) (cm (cz (2)) (b)))))) (ca (ca (cm (c) (ca (cz (2)) (cm (cz (-4)) (b)))) (cm (d) (ca (ca (cm (cz (-4)) (a)) (cm (cz (-2)) (d))) (ca (cm (cz (4)) (b)) (cm (cz (4)) (c)))))) (ca (cm (i) (ca (ca (cz (-4)) (ca (cm (cz (8)) (a)) (cm (c) (ca (cz (-2)) (cm (cz (-4)) (b)))))) (ca (cm (d) (ca (cm (cz (-4)) (a)) (cm (cz (4)) (c)))) (ca (cm (cz (-4)) (cm (a) (b))) (cm (cz (3)) (cm (a) (i))))))) (cm (j) (ca (cz (-4)) (ca (cm (cz (2)) (cp (b) 2)) (cm (d) (ca (cm (cz (-2)) (d)) (cm (cz (4)) (b))))))))))))) = (0 : ℂ))
    (e4 : ca (ca (cz (1)) (cm (cz (5)) (i))) (ca (cm (j) (ca (cz (5)) (cm (cz (9)) (i)))) (cm (rr) (ca (ca (a) (ca (c) (cm (cz (-1)) (b)))) (ca (cm (cz (-1)) (d)) (ca (cm (i) (ca (cz (2)) (ca (cm (cz (-1)) (a)) (cm (cz (-1)) (c))))) (cm (j) (ca (cz (-2)) (ca (b) (d))))))))) = (0 : ℂ))
    (e5 : ca (ca (cz (2)) (cm (cz (-7)) (b))) (ca (cm (cz (2)) (d)) (ca (cm (i) (ca (ca (cz (2)) (cm (cz (-16)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (-9)) (cm (b) (i)))))) (cm (rr) (ca (cm (b) (ca (cz (5)) (cm (cz (-2)) (b)))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-4)) (b)) (cm (cz (2)) (d))))) (cm (i) (ca (cm (b) (ca (cz (8)) (cm (cz (-2)) (b)))) (ca (cm (d) (ca (cz (-2)) (ca (cm (cz (-4)) (b)) (cm (cz (2)) (d))))) (cm (cz (3)) (cm (b) (i))))))))))) = (0 : ℂ))
    (e6 : ca (cz (-1)) (ca (cm (i) (ca (cz (-10)) (cm (cz (-9)) (i)))) (cm (rr) (ca (ca (cz (-1)) (cm (cz (2)) (b))) (ca (cm (cz (2)) (d)) (cm (i) (ca (ca (cz (2)) (cm (cz (-2)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (3)) (i))))))))) = (0 : ℂ))
    (e7 : ca (ca (cm (a) (ca (cz (10)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c)))))) (ca (cm (i) (ca (cm (a) (ca (cz (10)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c))))))) (ca (cm (j) (ca (ca (cm (a) (ca (cz (16)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (-4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c)))))) (ca (cm (i) (ca (cm (a) (ca (cz (16)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (-4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c))))))) (cm (j) (ca (cm (cz (6)) (a)) (cm (cz (6)) (cm (a) (i)))))))) (cm (rr) (ca (ca (cz (-2)) (cm (cz (-2)) (c))) (ca (cm (cz (7)) (a)) (ca (cm (i) (ca (cz (-2)) (ca (cm (cz (-2)) (c)) (cm (cz (7)) (a))))) (cm (j) (ca (ca (cz (-2)) (cm (cz (2)) (c))) (ca (cm (cz (16)) (a)) (ca (cm (i) (ca (cz (-2)) (ca (cm (cz (2)) (c)) (cm (cz (16)) (a))))) (cm (j) (ca (cm (cz (9)) (a)) (cm (cz (9)) (cm (a) (i))))))))))))))) = (0 : ℂ))
    (e8 : ca (ca (cz (2)) (cm (a) (ca (cz (-17)) (cm (cz (4)) (a))))) (ca (cm (c) (ca (cz (-2)) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a))))) (ca (cm (j) (ca (ca (cz (2)) (cm (a) (ca (cz (-32)) (cm (cz (4)) (a))))) (ca (cm (c) (ca (cz (2)) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a))))) (cm (cz (-15)) (cm (a) (j)))))) (cm (rr) (ca (ca (cz (2)) (cm (a) (ca (cz (-12)) (cm (cz (2)) (a))))) (ca (cm (c) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a)))) (cm (j) (ca (ca (cz (2)) (cm (a) (ca (cz (-24)) (cm (cz (2)) (a))))) (ca (cm (c) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a)))) (cm (cz (-12)) (cm (a) (j))))))))))) = (0 : ℂ))
    (e9 : ca (ca (ca (cz (-32)) (cm (cz (20)) (a))) (ca (cm (b) (ca (cz (20)) (cm (cz (-16)) (a)))) (cm (c) (ca (cz (8)) (cm (cz (-16)) (b)))))) (ca (ca (cm (d) (ca (cz (8)) (ca (cm (cz (-16)) (a)) (cm (cz (16)) (c))))) (cm (i) (ca (ca (cz (-32)) (ca (cm (cz (32)) (a)) (cm (b) (ca (cz (20)) (cm (cz (-16)) (a)))))) (ca (cm (c) (ca (cz (-8)) (cm (cz (-16)) (b)))) (ca (cm (d) (ca (cz (8)) (ca (cm (cz (-16)) (a)) (cm (cz (16)) (c))))) (cm (i) (ca (cz (-15)) (cm (cz (12)) (a))))))))) (ca (cm (j) (ca (ca (cz (-32)) (ca (cm (cz (20)) (a)) (cm (b) (ca (cz (32)) (cm (cz (-16)) (a)))))) (ca (ca (cm (c) (ca (cz (8)) (cm (cz (-16)) (b)))) (cm (d) (ca (cz (-8)) (ca (cm (cz (-16)) (a)) (cm (cz (16)) (c)))))) (ca (cm (i) (ca (ca (cz (2)) (ca (cm (cz (32)) (a)) (cm (b) (ca (cz (32)) (cm (cz (-16)) (a)))))) (ca (cm (c) (ca (cz (-8)) (cm (cz (-16)) (b)))) (ca (cm (d) (ca (cz (-8)) (ca (cm (cz (-16)) (a)) (cm (cz (16)) (c))))) (cm (cz (12)) (cm (a) (i))))))) (cm (j) (ca (cz (-15)) (ca (cm (cz (12)) (b)) (cm (cz (12)) (cm (b) (i)))))))))) (cm (rr) (ca (ca (cm (cz (-14)) (a)) (ca (cm (cz (-4)) (d)) (cm (cz (4)) (c)))) (ca (cm (cz (14)) (b)) (ca (cm (i) (ca (ca (cz (24)) (ca (cm (cz (-32)) (a)) (cm (cz (-4)) (c)))) (ca (cm (cz (-4)) (d)) (ca (cm (cz (14)) (b)) (cm (i) (ca (cz (12)) (cm (cz (-18)) (a)))))))) (cm (j) (ca (ca (cz (-24)) (ca (cm (cz (-14)) (a)) (cm (cz (4)) (c)))) (ca (ca (cm (cz (4)) (d)) (cm (cz (32)) (b))) (ca (cm (i) (ca (ca (cm (cz (-32)) (a)) (cm (cz (-4)) (c))) (ca (cm (cz (4)) (d)) (ca (cm (cz (32)) (b)) (cm (cz (-18)) (cm (a) (i))))))) (cm (j) (ca (cz (-12)) (ca (cm (cz (18)) (b)) (cm (cz (18)) (cm (b) (i)))))))))))))))) = (0 : ℂ))
    (e10 : ca (ca (ca (cz (-14)) (cm (a) (ca (cz (14)) (cm (cz (4)) (a))))) (ca (cm (b) (ca (cz (-17)) (cm (cz (8)) (a)))) (cm (c) (ca (ca (cz (12)) (cm (cz (-4)) (c))) (ca (cm (cz (8)) (a)) (cm (cz (8)) (b))))))) (ca (ca (cm (d) (ca (cz (-2)) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a))))) (cm (i) (ca (cz (16)) (ca (cm (cz (4)) (cp (a) 2)) (cm (c) (ca (cz (2)) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a))))))))) (ca (cm (j) (ca (ca (cz (-34)) (ca (cm (b) (ca (cz (-32)) (cm (cz (8)) (a)))) (cm (c) (ca (cz (2)) (cm (cz (8)) (b)))))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a))))) (ca (cm (i) (ca (cz (26)) (ca (cm (cz (-16)) (c)) (cm (cz (-14)) (a))))) (cm (j) (ca (cz (-18)) (ca (cm (cz (-15)) (b)) (cm (cz (12)) (i))))))))) (cm (rr) (ca (ca (cz (-12)) (ca (cm (cz (-2)) (cp (a) 2)) (cm (b) (ca (cz (-12)) (cm (cz (4)) (a)))))) (ca (ca (cm (c) (ca (cm (cz (-4)) (a)) (ca (cm (cz (2)) (c)) (cm (cz (4)) (b))))) (cm (d) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a))))) (ca (cm (i) (ca (cz (8)) (ca (cm (a) (ca (cz (-8)) (cm (cz (-2)) (a)))) (cm (c) (ca (cz (-8)) (ca (cm (cz (-4)) (a)) (cm (cz (2)) (c)))))))) (cm (j) (ca (ca (cz (-16)) (ca (cm (cz (8)) (a)) (cm (cz (28)) (i)))) (ca (ca (cm (b) (ca (cz (-24)) (cm (cz (4)) (a)))) (cm (c) (ca (cz (8)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a)))) (cm (j) (ca (cz (-6)) (ca (cm (cz (-12)) (b)) (cm (cz (18)) (i))))))))))))))) = (0 : ℂ))
    (e11 : ca (ca (cz (-11)) (cm (cz (-1)) (cp (a) 2))) (ca (cm (c) (ca (cz (-2)) (ca (c) (cm (cz (-2)) (a))))) (ca (cm (j) (ca (ca (cz (-26)) (cm (cz (-15)) (j))) (ca (cm (cz (2)) (c)) (cm (cz (4)) (a))))) (cm (rr) (ca (cz (-8)) (ca (cm (cz (2)) (a)) (cm (j) (ca (cz (-20)) (ca (cm (cz (-12)) (j)) (cm (cz (2)) (a)))))))))) = (0 : ℂ))
    (e12 : ca (ca (cm (b) (ca (cz (10)) (cm (cz (-4)) (b)))) (cm (d) (ca (cz (4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d)))))) (ca (cm (i) (ca (cm (b) (ca (cz (16)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (-4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (cz (6)) (cm (b) (i)))))) (ca (cm (j) (ca (cm (b) (ca (cz (10)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (i) (ca (cm (b) (ca (cz (16)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (-4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (cz (6)) (cm (b) (i))))))))) (cm (rr) (ca (ca (cz (2)) (cm (cz (-7)) (b))) (ca (cm (cz (2)) (d)) (ca (cm (i) (ca (ca (cz (2)) (cm (cz (-16)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (-9)) (cm (b) (i)))))) (cm (j) (ca (ca (cz (2)) (cm (cz (-7)) (b))) (ca (cm (cz (2)) (d)) (cm (i) (ca (ca (cz (2)) (cm (cz (-16)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (-9)) (cm (b) (i))))))))))))))) = (0 : ℂ))
    (e13 : ca (ca (ca (cz (-14)) (cm (cz (-17)) (a))) (ca (cm (b) (ca (cz (14)) (ca (cm (cz (4)) (b)) (cm (cz (8)) (a))))) (cm (c) (ca (cz (-2)) (cm (cz (8)) (b)))))) (ca (ca (cm (d) (ca (ca (cz (12)) (cm (cz (-8)) (c))) (ca (cm (cz (-4)) (d)) (ca (cm (cz (8)) (a)) (cm (cz (8)) (b)))))) (cm (i) (ca (ca (cz (-34)) (ca (cm (cz (-32)) (a)) (cm (c) (ca (cz (2)) (cm (cz (8)) (b)))))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a))))) (ca (cm (i) (ca (cz (-18)) (cm (cz (-15)) (a)))) (cm (cz (8)) (cm (a) (b)))))))) (ca (cm (j) (ca (ca (cz (16)) (cm (cz (4)) (cp (b) 2))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b))))) (cm (i) (ca (ca (cz (26)) (cm (cz (-16)) (d))) (ca (cm (cz (-14)) (b)) (cm (cz (12)) (i)))))))) (cm (rr) (ca (ca (cz (12)) (ca (cm (cz (12)) (a)) (cm (b) (ca (cm (cz (-4)) (a)) (cm (cz (2)) (b)))))) (ca (ca (cm (d) (ca (ca (cm (cz (-4)) (a)) (cm (cz (-2)) (d))) (ca (cm (cz (4)) (b)) (cm (cz (4)) (c))))) (cm (i) (ca (ca (cz (16)) (ca (cm (cz (24)) (a)) (cm (b) (ca (cz (-8)) (cm (cz (-4)) (a)))))) (ca (cm (d) (ca (cz (-8)) (ca (cm (cz (-4)) (a)) (cm (cz (4)) (c))))) (ca (cm (i) (ca (cz (6)) (cm (cz (12)) (a)))) (cm (cz (-4)) (cm (b) (c)))))))) (ca (cm (j) (ca (ca (cz (-8)) (cm (b) (ca (cz (8)) (cm (cz (2)) (b))))) (ca (cm (d) (ca (cz (8)) (ca (cm (cz (-2)) (d)) (cm (cz (4)) (b))))) (cm (i) (ca (cz (-28)) (cm (cz (-18)) (i))))))) (cm (cz (-4)) (cm (b) (c))))))))) = (0 : ℂ))
    (e14 : ca (ca (cz (1)) (ca (cm (c) (ca (cz (-1)) (cm (cz (-1)) (b)))) (cm (d) (ca (cz (-1)) (ca (c) (cm (cz (-1)) (a))))))) (ca (ca (cm (i) (ca (c) (cm (cz (2)) (a)))) (cm (j) (ca (d) (ca (cm (cz (-3)) (i)) (cm (cz (2)) (b)))))) (ca (cm (rr) (ca (ca (b) (cm (cz (-1)) (a))) (ca (cm (i) (ca (cz (-2)) (cm (cz (-1)) (a)))) (cm (j) (ca (cz (2)) (b)))))) (cm (cz (-1)) (cm (a) (b))))) = (0 : ℂ))
    (e15 : ca (ca (cz (2)) (cm (b) (ca (cz (-17)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cz (-2)) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b))))) (ca (cm (i) (ca (ca (cz (2)) (cm (b) (ca (cz (-32)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b))))) (cm (cz (-15)) (cm (b) (i)))))) (cm (rr) (ca (ca (cz (-2)) (cm (b) (ca (cz (12)) (cm (cz (-2)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (b)) (cm (cz (2)) (d)))) (cm (i) (ca (ca (cz (-2)) (cm (b) (ca (cz (24)) (cm (cz (-2)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (b)) (cm (cz (2)) (d)))) (cm (cz (12)) (cm (b) (i))))))))))) = (0 : ℂ))
    (e16 : ca (ca (cz (-11)) (cm (cz (-1)) (cp (b) 2))) (ca (cm (d) (ca (cz (-2)) (ca (d) (cm (cz (-2)) (b))))) (ca (cm (i) (ca (ca (cz (-26)) (cm (cz (-15)) (i))) (ca (cm (cz (2)) (d)) (cm (cz (4)) (b))))) (cm (rr) (ca (cz (8)) (ca (cm (cz (-2)) (b)) (cm (i) (ca (cz (20)) (ca (cm (cz (-2)) (b)) (cm (cz (12)) (i)))))))))) = (0 : ℂ))
    (e17 : ca (cz (-2)) (cp (rr) 2) = (0 : ℂ))
    : False := by
  have hrr : rr^2=2 := by
    simp only [ca,cm,cp,cz] at e17
    linear_combination e17
  have impossible : cz (640672357364423102294657004927734576330613051275734005774736988194912881016512) = 0 := by
    linear_combination (norm := skip) (coeff0 a b c d i j rr) * e0 + (coeff1 a b c d i j rr) * e1 + (coeff2 a b c d i j rr) * e2 + (coeff3 a b c d i j rr) * e3 + (coeff4 a b c d i j rr) * e4 + (coeff5 a b c d i j rr) * e5 + (coeff6 a b c d i j rr) * e6 + (coeff8 a b c d i j rr) * e8 + (coeff9 a b c d i j rr) * e9 + (coeff10 a b c d i j rr) * e10 + (coeff11 a b c d i j rr) * e11 + (coeff13 a b c d i j rr) * e13 + (coeff14 a b c d i j rr) * e14 + (coeff15 a b c d i j rr) * e15 + (coeff16 a b c d i j rr) * e16
    simp only [coeff0, coeff1, coeff2, coeff3, coeff4, coeff5, coeff6, coeff8, coeff9, coeff10, coeff11, coeff13, coeff14, coeff15, coeff16, ca, cm, cp, cz]
    ring_nf
    simp only [hrr]
    ring
  norm_num [cz] at impossible

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma normalized_same_obstruction (a b c d g k i j rr : ℂ)
    (e0 : ca (ca (cm (g) (ca (ca (cz (-1)) (cm (a) (g))) (ca (cm (a) (ca (cz (2)) (a))) (cm (c) (ca (c) (cm (cz (2)) (a))))))) (cm (j) (ca (cm (c) (ca (cz (-2)) (cm (cz (2)) (c)))) (ca (cm (cz (-1)) (cm (a) (j))) (cm (cz (2)) (cm (a) (g))))))) (ca (cm (rr) (ca (cm (g) (ca (ca (cz (1)) (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a))))) (ca (cm (c) (ca (cm (cz (-1)) (c)) (cm (cz (-2)) (a)))) (cm (cz (-1)) (cm (a) (g)))))) (ca (cm (j) (ca (cm (a) (j)) (ca (cm (c) (ca (cz (2)) (cm (cz (-2)) (c)))) (cm (cz (-2)) (cm (a) (g)))))) (cm (cp (c) 2) (ca (cz (-2)) (ca (cm (cz (-1)) (a)) (cm (cz (-2)) (c)))))))) (cm (cp (c) 2) (ca (cz (2)) (ca (a) (cm (cz (2)) (c)))))) = (0 : ℂ))
    (e1 : ca (ca (cm (g) (ca (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (b) (g)))) (ca (cm (b) (ca (cz (2)) (cm (cz (2)) (a)))) (ca (cm (d) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c)))) (cm (cz (2)) (cm (b) (c))))))) (ca (cm (i) (ca (cm (c) (ca (cz (2)) (cm (cz (2)) (c)))) (cm (cz (2)) (cm (a) (g))))) (cm (j) (ca (ca (cm (cz (2)) (c)) (ca (cm (d) (ca (cz (-2)) (cm (cz (4)) (c)))) (cm (cz (-1)) (cm (b) (j))))) (ca (cm (cz (2)) (cm (a) (i))) (ca (cm (cz (2)) (cm (a) (k))) (cm (cz (2)) (cm (b) (g))))))))) (ca (ca (cm (k) (ca (ca (cz (-1)) (cm (a) (ca (cz (2)) (a)))) (ca (cm (c) (ca (c) (cm (cz (2)) (a)))) (cm (cz (2)) (cm (a) (g)))))) (cm (rr) (ca (ca (cm (g) (ca (ca (cm (cz (-2)) (b)) (cm (cz (2)) (a))) (ca (cm (d) (ca (cm (cz (-2)) (c)) (cm (cz (2)) (a)))) (ca (cm (cz (-1)) (cm (b) (g))) (cm (cz (-2)) (cm (b) (c))))))) (ca (cm (i) (ca (cm (cz (2)) (cp (c) 2)) (cm (cz (2)) (cm (a) (g))))) (cm (j) (ca (ca (cm (b) (j)) (cm (d) (ca (cz (2)) (cm (cz (-4)) (c))))) (ca (cm (cz (-2)) (cm (a) (k))) (cm (cz (-2)) (cm (b) (g)))))))) (ca (cm (k) (ca (cz (1)) (ca (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a)))) (cm (c) (ca (c) (cm (cz (-2)) (a))))))) (ca (cm (cp (c) 2) (ca (cz (2)) (b))) (cm (c) (cm (d) (ca (cz (-4)) (ca (cm (cz (-2)) (a)) (cm (cz (-2)) (c))))))))))) (ca (cm (cp (c) 2) (ca (cz (2)) (b))) (cm (c) (cm (d) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (cz (6)) (c)))))))) = (0 : ℂ))
    (e2 : ca (ca (cz (-1)) (ca (cm (a) (ca (cz (2)) (a))) (cm (c) (ca (cz (4)) (ca (cm (cz (4)) (a)) (cm (cz (4)) (c))))))) (ca (cm (g) (ca (ca (cz (2)) (g)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c))))) (ca (cm (j) (ca (ca (cz (-2)) (cm (cz (-1)) (j))) (ca (cm (cz (2)) (a)) (ca (cm (cz (2)) (g)) (cm (cz (4)) (c)))))) (cm (rr) (ca (ca (cz (1)) (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a))))) (ca (cm (c) (ca (cz (-2)) (ca (cm (cz (-4)) (a)) (cm (cz (-4)) (c))))) (ca (cm (g) (ca (cm (cz (-1)) (g)) (ca (cm (cz (-4)) (c)) (cm (cz (-2)) (a))))) (cm (j) (ca (ca (cz (2)) (j)) (ca (cm (cz (-2)) (c)) (cm (cz (-2)) (g))))))))))) = (0 : ℂ))
    (e3 : ca (ca (cm (d) (ca (cm (c) (ca (cz (4)) (cm (cz (2)) (b)))) (cm (d) (ca (cz (2)) (ca (a) (cm (cz (6)) (c))))))) (ca (cm (g) (ca (cz (-1)) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (d) (cm (cz (2)) (b))))))) (cm (i) (ca (ca (cm (cz (-2)) (c)) (cm (d) (ca (cz (2)) (cm (cz (4)) (c))))) (ca (cm (cz (-1)) (cm (a) (i))) (ca (cm (cz (2)) (cm (a) (k))) (cm (cz (2)) (cm (b) (g))))))))) (ca (cm (j) (ca (cm (d) (ca (cz (2)) (cm (cz (2)) (d)))) (ca (cm (cz (2)) (cm (b) (i))) (cm (cz (2)) (cm (b) (k)))))) (ca (cm (k) (ca (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (a) (k)))) (ca (ca (cm (b) (ca (cz (2)) (cm (cz (2)) (a)))) (cm (d) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c))))) (ca (cm (cz (2)) (cm (b) (c))) (cm (cz (2)) (cm (b) (g))))))) (cm (rr) (ca (ca (cm (d) (ca (cm (c) (ca (cz (4)) (cm (cz (2)) (b)))) (cm (d) (ca (cz (-2)) (ca (cm (cz (-1)) (a)) (cm (cz (2)) (c))))))) (cm (g) (ca (cz (-1)) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (cm (cz (-1)) (d)) (cm (cz (2)) (b)))))))) (ca (cm (i) (ca (ca (cm (cz (-2)) (c)) (cm (cz (-1)) (cm (a) (i)))) (ca (cm (cz (2)) (cm (a) (k))) (ca (cm (cz (2)) (cm (b) (g))) (cm (cz (4)) (cm (c) (d))))))) (ca (cm (j) (ca (cm (cz (-2)) (cp (d) 2)) (cm (cz (-2)) (cm (b) (k))))) (cm (k) (ca (ca (cm (cz (-2)) (b)) (cm (cz (2)) (a))) (ca (cm (a) (k)) (ca (cm (d) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c)))) (cm (cz (-2)) (cm (b) (c))))))))))))) = (0 : ℂ))
    (e4 : ca (ca (ca (cz (1)) (a)) (ca (cm (b) (ca (cz (1)) (a))) (ca (cm (c) (ca (cz (2)) (cm (cz (2)) (b)))) (cm (d) (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c)))))))) (ca (ca (cm (g) (ca (cz (1)) (ca (b) (cm (cz (2)) (d))))) (cm (i) (ca (ca (cz (1)) (a)) (ca (g) (cm (cz (2)) (c)))))) (ca (cm (j) (ca (ca (cz (1)) (b)) (ca (i) (ca (k) (cm (cz (2)) (d)))))) (ca (cm (k) (ca (ca (cz (1)) (a)) (ca (g) (cm (cz (2)) (c))))) (cm (rr) (ca (ca (a) (ca (c) (cm (cz (-1)) (b)))) (ca (cm (cz (-1)) (d)) (ca (cm (i) (ca (c) (g))) (cm (j) (ca (cm (cz (-1)) (d)) (cm (cz (-1)) (k))))))))))) = (0 : ℂ))
    (e5 : ca (ca (cz (2)) (ca (a) (g))) (ca (cm (cz (2)) (c)) (ca (cm (cz (2)) (j)) (cm (rr) (ca (cm (cz (-1)) (a)) (ca (cm (cz (-1)) (g)) (cm (cz (-2)) (c))))))) = (0 : ℂ))
    (e6 : ca (ca (cm (i) (ca (cm (d) (ca (cz (-2)) (cm (cz (2)) (d)))) (ca (cm (cz (-1)) (cm (b) (i))) (cm (cz (2)) (cm (b) (k)))))) (cm (k) (ca (ca (cz (-1)) (cm (b) (k))) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (d) (cm (cz (2)) (b)))))))) (ca (cm (rr) (ca (cm (i) (ca (cm (d) (ca (cz (-2)) (cm (cz (2)) (d)))) (ca (cm (cz (-1)) (cm (b) (i))) (cm (cz (2)) (cm (b) (k)))))) (ca (cm (k) (ca (ca (cz (-1)) (cm (b) (k))) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (d) (cm (cz (2)) (b))))))) (cm (cp (d) 2) (ca (cz (2)) (ca (b) (cm (cz (2)) (d)))))))) (cm (cp (d) 2) (ca (cz (2)) (ca (b) (cm (cz (2)) (d)))))) = (0 : ℂ))
    (e7 : ca (ca (cz (-1)) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (cz (4)) (ca (cm (cz (4)) (b)) (cm (cz (4)) (d))))))) (ca (cm (i) (ca (ca (cz (-2)) (cm (cz (-1)) (i))) (ca (cm (cz (2)) (b)) (ca (cm (cz (2)) (k)) (cm (cz (4)) (d)))))) (ca (cm (k) (ca (ca (cz (2)) (k)) (ca (cm (cz (2)) (b)) (cm (cz (4)) (d))))) (cm (rr) (ca (ca (cz (-1)) (cm (b) (ca (cz (2)) (b)))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (4)) (b)) (cm (cz (4)) (d))))) (ca (cm (i) (ca (ca (cz (-2)) (cm (cz (-1)) (i))) (ca (cm (cz (2)) (d)) (cm (cz (2)) (k))))) (cm (k) (ca (k) (ca (cm (cz (2)) (b)) (cm (cz (4)) (d))))))))))) = (0 : ℂ))
    (e8 : ca (ca (cz (2)) (ca (b) (k))) (ca (cm (cz (2)) (d)) (ca (cm (cz (2)) (i)) (cm (rr) (ca (b) (ca (k) (cm (cz (2)) (d))))))) = (0 : ℂ))
    (e9 : ca (ca (cm (g) (ca (ca (cz (-2)) (ca (cm (a) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (b) (ca (cz (-1)) (cm (a) (ca (cz (2)) (a))))))) (ca (cm (c) (ca (cm (cz (4)) (a)) (ca (cm (c) (ca (cz (2)) (b))) (cm (cz (2)) (cm (a) (b)))))) (ca (cm (d) (ca (cz (-2)) (ca (cm (a) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (c) (ca (cm (cz (2)) (c)) (cm (cz (4)) (a))))))) (cm (g) (ca (cm (cz (2)) (a)) (ca (cm (a) (b)) (cm (cz (2)) (cm (a) (d)))))))))) (ca (cm (i) (ca (cm (g) (ca (ca (cz (-2)) (cm (a) (ca (cz (4)) (cm (cz (2)) (a))))) (ca (cm (c) (ca (cm (cz (2)) (c)) (cm (cz (4)) (a)))) (cm (cz (2)) (cm (a) (g)))))) (cm (cp (c) 2) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c))))))) (cm (j) (ca (ca (cm (c) (ca (cz (-4)) (ca (cm (cz (-2)) (b)) (cm (c) (ca (cz (4)) (cm (cz (2)) (b))))))) (ca (cm (g) (ca (cm (cz (4)) (a)) (ca (cm (cz (2)) (cm (a) (b))) (cm (cz (4)) (cm (a) (d)))))) (cm (i) (ca (cm (c) (ca (cz (-4)) (cm (cz (4)) (c)))) (cm (cz (4)) (cm (a) (g))))))) (ca (cm (j) (ca (ca (cm (cz (-2)) (a)) (cm (cz (-1)) (cm (a) (b)))) (ca (cm (cz (-1)) (cm (a) (k))) (ca (cm (cz (-2)) (cm (a) (d))) (cm (cz (-2)) (cm (a) (i))))))) (ca (cm (k) (ca (cm (c) (ca (cz (-2)) (cm (cz (2)) (c)))) (cm (cz (2)) (cm (a) (g))))) (cm (c) (cm (d) (ca (cz (-4)) (cm (cz (4)) (c))))))))))) (ca (cm (k) (ca (cm (g) (ca (ca (cz (-1)) (cm (a) (g))) (ca (cm (a) (ca (cz (2)) (a))) (cm (c) (ca (c) (cm (cz (2)) (a))))))) (cm (cp (c) 2) (ca (cz (2)) (ca (a) (cm (cz (2)) (c))))))) (ca (cm (cp (c) 2) (ca (ca (cz (4)) (cm (cz (2)) (a))) (ca (cm (b) (ca (cz (2)) (a))) (cm (c) (ca (cz (4)) (cm (cz (2)) (b))))))) (cm (d) (cm (cp (c) 2) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c)))))))) = (0 : ℂ))
    (e10 : ca (cm (g) (ca (ca (cz (1)) (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a))))) (ca (cm (c) (ca (cm (cz (-1)) (c)) (cm (cz (-2)) (a)))) (cm (cz (-1)) (cm (a) (g)))))) (ca (cm (j) (ca (cm (a) (j)) (ca (cm (c) (ca (cz (2)) (cm (cz (-2)) (c)))) (cm (cz (-2)) (cm (a) (g)))))) (cm (cp (c) 2) (ca (cz (-2)) (ca (cm (cz (-1)) (a)) (cm (cz (-2)) (c)))))) = (0 : ℂ))
    (e11 : ca (ca (cm (d) (ca (cm (c) (ca (ca (cz (8)) (cm (cz (4)) (a))) (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (c) (ca (cz (8)) (cm (cz (4)) (b))))))) (cm (c) (cm (d) (ca (cz (8)) (ca (cm (cz (4)) (a)) (cm (cz (8)) (c)))))))) (cm (g) (ca (ca (cz (-2)) (ca (cm (cz (-1)) (a)) (cm (b) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (b) (ca (cz (2)) (a)))))))) (ca (cm (c) (ca (cz (-2)) (cm (b) (ca (cz (4)) (cm (cz (2)) (b)))))) (ca (cm (d) (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (a)))) (ca (cm (c) (ca (cz (4)) (cm (cz (6)) (b)))) (cm (cz (4)) (cm (c) (d)))))) (cm (g) (ca (cz (-1)) (ca (cm (b) (ca (cz (2)) (b))) (cm (cz (2)) (cm (b) (d))))))))))) (ca (cm (i) (ca (ca (cm (c) (ca (cz (-4)) (ca (cm (cz (-4)) (c)) (cm (cz (-2)) (a))))) (cm (g) (ca (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (c) (ca (cz (-2)) (cm (cz (4)) (b))))) (ca (cm (cz (2)) (cm (b) (g))) (cm (cz (4)) (cm (c) (d))))))) (ca (cm (i) (ca (ca (cz (1)) (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a))))) (ca (cm (cz (-1)) (cm (a) (g))) (cm (cz (-2)) (cm (a) (c)))))) (ca (cm (k) (ca (ca (cz (-2)) (cm (a) (ca (cz (4)) (cm (cz (2)) (a))))) (ca (cm (cz (2)) (cm (a) (g))) (cm (cz (4)) (cm (a) (c)))))) (cm (c) (cm (d) (ca (cz (8)) (ca (cm (cz (4)) (a)) (cm (cz (8)) (c)))))))))) (ca (cm (j) (ca (ca (cm (d) (ca (ca (cz (-4)) (cm (cz (-2)) (b))) (ca (cm (c) (ca (cz (8)) (cm (cz (4)) (b)))) (cm (d) (ca (cz (-4)) (cm (cz (8)) (c))))))) (cm (g) (ca (cz (-2)) (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (b)))) (cm (cz (4)) (cm (b) (d))))))) (ca (cm (i) (ca (ca (cz (2)) (ca (cm (cz (-4)) (c)) (cm (d) (ca (cz (-4)) (cm (cz (8)) (c)))))) (ca (cm (cz (-2)) (cm (a) (i))) (ca (cm (cz (4)) (cm (a) (k))) (cm (cz (4)) (cm (b) (g))))))) (ca (cm (j) (ca (ca (cz (1)) (cm (b) (ca (cz (-2)) (cm (cz (-1)) (b))))) (ca (cm (cz (-1)) (cm (b) (k))) (ca (cm (cz (-2)) (cm (b) (d))) (cm (cz (-2)) (cm (b) (i))))))) (cm (k) (ca (ca (cm (cz (4)) (a)) (cm (d) (ca (cz (-2)) (ca (cm (cz (4)) (a)) (cm (cz (4)) (c)))))) (ca (cm (cz (2)) (cm (a) (b))) (ca (cm (cz (2)) (cm (a) (k))) (cm (cz (2)) (cm (b) (g))))))))))) (cm (k) (ca (ca (cz (-2)) (ca (cm (a) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (b) (ca (cz (-1)) (cm (a) (ca (cz (2)) (a))))))) (ca (ca (cm (c) (ca (cm (cz (4)) (a)) (cm (cz (2)) (cm (a) (b))))) (cm (d) (ca (cz (-2)) (ca (cm (a) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (c) (ca (cz (4)) (ca (cm (cz (4)) (c)) (cm (cz (6)) (a))))))))) (ca (cm (g) (ca (ca (cm (cz (2)) (a)) (cm (b) (g))) (ca (cm (b) (ca (cz (2)) (cm (cz (2)) (a)))) (ca (cm (d) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c)))) (cm (cz (2)) (cm (b) (c))))))) (cm (k) (ca (ca (cz (-1)) (cm (a) (g))) (ca (cm (a) (ca (cz (2)) (a))) (cm (cz (2)) (cm (a) (c)))))))))))) = (0 : ℂ))
    (e12 : ca (ca (ca (cz (-2)) (cm (a) (ca (cz (4)) (cm (cz (2)) (a))))) (ca (cm (b) (ca (cz (-1)) (cm (a) (ca (cz (2)) (a))))) (cm (c) (ca (cm (cz (6)) (a)) (ca (cm (b) (ca (cz (2)) (cm (cz (4)) (a)))) (cm (c) (ca (cz (2)) (cm (cz (3)) (b))))))))) (ca (ca (cm (d) (ca (cz (-2)) (ca (cm (a) (ca (cz (4)) (cm (cz (2)) (a)))) (cm (c) (ca (cm (cz (2)) (c)) (cm (cz (6)) (a))))))) (cm (g) (ca (ca (cz (-2)) (cm (cz (-2)) (b))) (ca (cm (c) (ca (cz (2)) (cm (cz (2)) (b)))) (ca (cm (d) (ca (cm (cz (2)) (a)) (cm (cz (6)) (c)))) (cm (cz (2)) (cm (d) (g)))))))) (ca (cm (i) (ca (cm (c) (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (cz (2)) (c))))) (cm (g) (ca (cm (cz (2)) (g)) (cm (cz (6)) (c)))))) (ca (cm (j) (ca (ca (ca (cz (-2)) (cm (cz (-2)) (b))) (ca (cm (cz (-2)) (d)) (cm (c) (ca (cz (2)) (cm (cz (2)) (b)))))) (ca (ca (cm (i) (ca (cz (-2)) (ca (cm (cz (-2)) (a)) (cm (cz (4)) (g))))) (cm (j) (ca (cm (cz (-1)) (k)) (ca (cm (cz (-2)) (d)) (cm (cz (-2)) (i)))))) (ca (cm (k) (ca (ca (cz (-2)) (cm (cz (-2)) (a))) (ca (cm (cz (2)) (c)) (cm (cz (2)) (g))))) (cm (cz (4)) (cm (d) (g))))))) (cm (k) (ca (cm (c) (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (cz (3)) (c))))) (cm (g) (ca (g) (cm (cz (4)) (c))))))))) = (0 : ℂ))
    (e13 : ca (ca (cz (1)) (cm (a) (ca (cz (-2)) (cm (cz (-1)) (a))))) (ca (cm (c) (ca (cz (-2)) (ca (cm (cz (-4)) (a)) (cm (cz (-3)) (c))))) (ca (cm (g) (ca (cm (cz (-1)) (a)) (ca (cm (cz (-1)) (g)) (cm (cz (-4)) (c))))) (cm (j) (ca (ca (cz (2)) (j)) (ca (cm (cz (-2)) (c)) (cm (cz (-2)) (g))))))) = (0 : ℂ))
    (e14 : ca (ca (cm (i) (ca (ca (cm (d) (ca (ca (cz (-4)) (cm (cz (-4)) (c))) (ca (cm (cz (-2)) (a)) (cm (d) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c)))))))) (cm (i) (ca (cm (b) (ca (cz (-2)) (cm (cz (-1)) (a)))) (ca (cm (cz (-1)) (cm (b) (g))) (cm (cz (-2)) (cm (b) (c))))))) (ca (cm (k) (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (a)))) (ca (cm (cz (2)) (cm (b) (g))) (cm (cz (4)) (cm (b) (c)))))) (cm (d) (cm (g) (ca (cz (-2)) (cm (cz (2)) (d)))))))) (cm (j) (ca (cm (i) (ca (cm (d) (ca (cz (-4)) (cm (cz (4)) (d)))) (ca (cm (cz (-2)) (cm (b) (i))) (cm (cz (4)) (cm (b) (k)))))) (ca (cm (k) (ca (ca (cz (-2)) (cm (b) (ca (cz (4)) (cm (cz (2)) (b))))) (ca (cm (d) (ca (cm (cz (2)) (d)) (cm (cz (4)) (b)))) (cm (cz (2)) (cm (b) (k)))))) (cm (cp (d) 2) (ca (cz (4)) (ca (cm (cz (2)) (b)) (cm (cz (4)) (d))))))))) (ca (cm (k) (ca (ca (cz (-2)) (ca (cm (cz (-1)) (a)) (cm (b) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (b) (ca (cz (2)) (a)))))))) (ca (ca (cm (c) (ca (cz (-2)) (cm (b) (ca (cz (4)) (cm (cz (2)) (b)))))) (cm (d) (ca (cm (b) (ca (cz (4)) (cm (cz (2)) (a)))) (ca (cm (d) (ca (cz (2)) (ca (a) (cm (cz (2)) (c))))) (cm (cz (4)) (cm (b) (c))))))) (ca (cm (g) (ca (cz (-1)) (ca (cm (b) (ca (cz (2)) (b))) (cm (d) (ca (d) (cm (cz (2)) (b))))))) (cm (k) (ca (cm (b) (g)) (ca (cm (b) (ca (cz (2)) (a))) (cm (cz (2)) (cm (b) (c)))))))))) (ca (cm (cp (d) 2) (ca (ca (cz (4)) (cm (cz (2)) (a))) (ca (cm (b) (ca (cz (2)) (a))) (ca (cm (c) (ca (cz (4)) (cm (cz (2)) (b)))) (cm (d) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (cz (4)) (c))))))))) (cm (g) (cm (cp (d) 2) (ca (cz (2)) (ca (b) (cm (cz (2)) (d)))))))) = (0 : ℂ))
    (e15 : ca (ca (ca (cz (-2)) (cm (cz (-1)) (a))) (ca (cm (b) (ca (cz (4)) (ca (cm (cz (2)) (a)) (cm (b) (ca (cz (2)) (a)))))) (cm (c) (ca (cz (-2)) (cm (b) (ca (cz (4)) (cm (cz (2)) (b)))))))) (ca (ca (cm (d) (ca (ca (cm (cz (2)) (a)) (cm (b) (ca (cz (6)) (cm (cz (4)) (a))))) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (2)) (c)) (cm (cz (3)) (a))))) (cm (cz (6)) (cm (b) (c)))))) (cm (i) (ca (ca (cz (-2)) (ca (cm (cz (-2)) (a)) (cm (cz (-2)) (c)))) (ca (ca (cm (d) (ca (cz (2)) (cm (cz (2)) (a)))) (cm (g) (ca (cz (-2)) (ca (cm (cz (-2)) (b)) (cm (cz (2)) (d)))))) (ca (cm (i) (ca (cm (cz (-1)) (g)) (cm (cz (-2)) (c)))) (cm (k) (ca (cm (cz (2)) (g)) (cm (cz (4)) (c))))))))) (ca (cm (j) (ca (cm (d) (ca (cz (2)) (ca (cm (cz (2)) (b)) (cm (cz (2)) (d))))) (ca (cm (i) (ca (ca (cz (-2)) (cm (cz (-2)) (b))) (ca (cm (cz (-2)) (i)) (cm (cz (4)) (k))))) (cm (k) (ca (cm (cz (2)) (k)) (cm (cz (6)) (d))))))) (ca (cm (k) (ca (ca (cz (-2)) (ca (cm (cz (-2)) (a)) (cm (d) (ca (cz (2)) (ca (cm (cz (2)) (a)) (cm (cz (6)) (c))))))) (ca (cm (k) (ca (g) (cm (cz (2)) (c)))) (ca (cm (cz (2)) (cm (b) (c))) (cm (cz (4)) (cm (d) (g))))))) (cm (d) (cm (g) (ca (cz (2)) (ca (cm (cz (2)) (b)) (cm (cz (3)) (d))))))))) = (0 : ℂ))
    (e16 : ca (ca (ca (cz (-2)) (cm (cz (-2)) (a))) (ca (cm (b) (ca (cz (-2)) (cm (cz (-1)) (a)))) (cm (c) (ca (cz (-2)) (cm (cz (-2)) (b)))))) (ca (ca (cm (d) (ca (cz (-2)) (ca (cm (cz (-2)) (a)) (cm (cz (-2)) (c))))) (cm (i) (ca (cm (cz (-2)) (c)) (cm (cz (-2)) (g))))) (ca (cm (j) (ca (cm (cz (-2)) (d)) (ca (cm (cz (-2)) (i)) (cm (cz (-2)) (k))))) (ca (cm (k) (ca (cm (cz (-1)) (g)) (cm (cz (-2)) (c)))) (cm (cz (-2)) (cm (d) (g)))))) = (0 : ℂ))
    (e17 : ca (cm (i) (ca (cm (b) (i)) (ca (cm (d) (ca (cz (2)) (cm (cz (-2)) (d)))) (cm (cz (-2)) (cm (b) (k)))))) (ca (cm (k) (ca (ca (cz (1)) (cm (b) (ca (cz (-2)) (cm (cz (-1)) (b))))) (ca (cm (d) (ca (cm (cz (-1)) (d)) (cm (cz (-2)) (b)))) (cm (cz (-1)) (cm (b) (k)))))) (cm (cp (d) 2) (ca (cz (-2)) (ca (cm (cz (-1)) (b)) (cm (cz (-2)) (d)))))) = (0 : ℂ))
    (e18 : ca (ca (cz (1)) (cm (b) (ca (cz (-2)) (cm (cz (-1)) (b))))) (ca (cm (d) (ca (cz (-2)) (ca (cm (cz (-4)) (b)) (cm (cz (-3)) (d))))) (ca (cm (i) (ca (ca (cz (2)) (i)) (ca (cm (cz (-2)) (d)) (cm (cz (-2)) (k))))) (cm (k) (ca (cm (cz (-1)) (b)) (ca (cm (cz (-1)) (k)) (cm (cz (-4)) (d))))))) = (0 : ℂ))
    (e19 : ca (cz (-2)) (cp (rr) 2) = (0 : ℂ))
    : False := by
  simp only [ca, cm, cp, cz] at *
  have hg : g = 2 * (rr + 1) * (1 + j) - a - 2 * c := by
    linear_combination -(rr + 1) * e5 - (a + 2 * c + g) * e19
  have hk : k = -2 * (rr - 1) * (1 + i) - b - 2 * d := by
    linear_combination (rr - 1) * e8 - (b + 2 * d + k) * e19
  subst g
  subst k
  apply reduced_same_obstruction a b c d i j rr
  · linear_combination (norm := skip) e0 - (ca (ca (cz (2)) (cm (a) (ca (cz (-8)) (cm (cz (2)) (a))))) (ca (cm (c) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a)))) (ca (cm (j) (ca (ca (cz (2)) (cm (a) (ca (cz (-16)) (cm (cz (2)) (a))))) (ca (cm (c) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a)))) (cm (cz (-8)) (cm (a) (j)))))) (cm (rr) (ca (cm (cz (-4)) (a)) (cm (j) (ca (cm (cz (-8)) (a)) (cm (cz (-4)) (cm (a) (j)))))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e1 - (ca (ca (ca (cz (-2)) (cm (cz (2)) (cp (a) 2))) (ca (cm (b) (ca (cz (-8)) (cm (cz (4)) (a)))) (cm (c) (ca (cm (cz (-2)) (c)) (ca (cm (cz (4)) (a)) (cm (cz (4)) (b))))))) (ca (ca (cm (d) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a)))) (cm (i) (ca (cz (-2)) (ca (cm (cz (2)) (cp (a) 2)) (cm (c) (ca (cm (cz (-2)) (c)) (cm (cz (4)) (a)))))))) (ca (cm (j) (ca (ca (cm (b) (ca (cz (-16)) (cm (cz (4)) (a)))) (cm (d) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a))))) (ca (cm (cz (-8)) (cm (b) (j))) (cm (cz (4)) (cm (b) (c)))))) (cm (rr) (ca (cm (cz (-4)) (b)) (cm (j) (ca (cm (cz (-8)) (b)) (cm (cz (-4)) (cm (b) (j)))))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e2 - (ca (cz (-4)) (ca (cm (j) (ca (cz (-12)) (cm (cz (-8)) (j)))) (cm (rr) (ca (cz (-4)) (cm (j) (ca (cz (-8)) (cm (cz (-4)) (j)))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e3 - (ca (ca (ca (cz (-2)) (cm (cz (-8)) (a))) (ca (cm (b) (ca (cm (cz (2)) (b)) (cm (cz (4)) (a)))) (cm (d) (ca (ca (cm (cz (-4)) (c)) (cm (cz (-2)) (d))) (ca (cm (cz (4)) (a)) (cm (cz (4)) (b))))))) (ca (ca (cm (i) (ca (ca (cm (cz (-16)) (a)) (cm (d) (ca (cm (cz (-4)) (c)) (cm (cz (4)) (a))))) (ca (cm (cz (-8)) (cm (a) (i))) (ca (cm (cz (4)) (cm (a) (b))) (cm (cz (4)) (cm (b) (c))))))) (cm (j) (ca (cz (-2)) (ca (cm (cz (2)) (cp (b) 2)) (cm (d) (ca (cm (cz (-2)) (d)) (cm (cz (4)) (b)))))))) (ca (cm (rr) (ca (cm (cz (4)) (a)) (cm (i) (ca (cm (cz (8)) (a)) (cm (cz (4)) (cm (a) (i))))))) (cm (cz (4)) (cm (b) (c)))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e4 - (ca (cz (-4)) (ca (cm (cz (-2)) (i)) (cm (cz (-2)) (j)))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e6 - (ca (ca (cz (2)) (cm (b) (ca (cz (-8)) (cm (cz (2)) (b))))) (ca (cm (d) (ca (cm (cz (-2)) (d)) (cm (cz (4)) (b)))) (ca (cm (i) (ca (ca (cz (2)) (cm (b) (ca (cz (-16)) (cm (cz (2)) (b))))) (ca (cm (d) (ca (cm (cz (-2)) (d)) (cm (cz (4)) (b)))) (cm (cz (-8)) (cm (b) (i)))))) (cm (rr) (ca (cm (cz (4)) (b)) (cm (i) (ca (cm (cz (8)) (b)) (cm (cz (4)) (cm (b) (i)))))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e7 - (ca (cz (-4)) (ca (cm (i) (ca (cz (-12)) (cm (cz (-8)) (i)))) (cm (rr) (ca (cz (4)) (cm (i) (ca (cz (8)) (cm (cz (4)) (i)))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · have hm : cz (2) * (ca (ca (cm (a) (ca (cz (10)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c)))))) (ca (cm (i) (ca (cm (a) (ca (cz (10)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c))))))) (ca (cm (j) (ca (ca (cm (a) (ca (cz (16)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (-4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c)))))) (ca (cm (i) (ca (cm (a) (ca (cz (16)) (cm (cz (-4)) (a)))) (cm (c) (ca (cz (-4)) (ca (cm (cz (-8)) (a)) (cm (cz (4)) (c))))))) (cm (j) (ca (cm (cz (6)) (a)) (cm (cz (6)) (cm (a) (i)))))))) (cm (rr) (ca (ca (cz (-2)) (cm (cz (-2)) (c))) (ca (cm (cz (7)) (a)) (ca (cm (i) (ca (cz (-2)) (ca (cm (cz (-2)) (c)) (cm (cz (7)) (a))))) (cm (j) (ca (ca (cz (-2)) (cm (cz (2)) (c))) (ca (cm (cz (16)) (a)) (ca (cm (i) (ca (cz (-2)) (ca (cm (cz (2)) (c)) (cm (cz (16)) (a))))) (cm (j) (ca (cm (cz (9)) (a)) (cm (cz (9)) (cm (a) (i)))))))))))))))) = 0 := by
      linear_combination (norm := skip) e9 - (ca (ca (cz (4)) (ca (cm (a) (ca (cz (-8)) (cm (cz (4)) (a)))) (cm (c) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a)))))) (ca (cm (i) (ca (cz (4)) (ca (cm (a) (ca (cz (-8)) (cm (cz (4)) (a)))) (cm (c) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a))))))) (ca (cm (j) (ca (ca (cz (4)) (cm (a) (ca (cz (-16)) (cm (cz (4)) (a))))) (ca (cm (c) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a)))) (ca (cm (i) (ca (cz (4)) (ca (cm (a) (ca (cz (-16)) (cm (cz (4)) (a)))) (cm (c) (ca (cm (cz (-4)) (c)) (cm (cz (8)) (a))))))) (cm (j) (ca (cm (cz (-8)) (a)) (cm (cz (-8)) (cm (a) (i))))))))) (cm (rr) (ca (cm (cz (-8)) (a)) (ca (cm (j) (ca (cm (cz (-16)) (a)) (ca (cm (j) (ca (cm (cz (-8)) (a)) (cm (cz (-8)) (cm (a) (i))))) (cm (cz (-16)) (cm (a) (i)))))) (cm (cz (-8)) (cm (a) (i))))))))) * e19
      simp only [ca, cm, cp, cz]
      ring
    have hc : cz (2) ≠ 0 := by norm_num [cz]
    exact (mul_eq_zero.mp hm).resolve_left hc
  · linear_combination (norm := skip) e10 - (ca (cm (cz (-4)) (a)) (cm (j) (ca (cm (cz (-8)) (a)) (cm (cz (-4)) (cm (a) (j)))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e11 - (ca (ca (ca (cz (-8)) (cm (cz (-8)) (a))) (ca (cm (b) (ca (cz (-8)) (cm (cz (8)) (a)))) (cm (d) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a)))))) (ca (ca (cm (i) (ca (ca (cz (-8)) (ca (cm (cz (-16)) (a)) (cm (b) (ca (cz (-8)) (cm (cz (8)) (a)))))) (ca (cm (d) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a)))) (ca (cm (i) (ca (cz (-4)) (cm (cz (-8)) (a)))) (cm (cz (8)) (cm (b) (c))))))) (cm (j) (ca (ca (cz (-8)) (ca (cm (cz (-8)) (a)) (cm (b) (ca (cz (-16)) (cm (cz (8)) (a)))))) (ca (ca (cm (d) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a)))) (cm (i) (ca (ca (cm (cz (-16)) (a)) (cm (b) (ca (cz (-16)) (cm (cz (8)) (a))))) (ca (cm (d) (ca (cm (cz (-8)) (c)) (cm (cz (8)) (a)))) (ca (cm (cz (-8)) (cm (a) (i))) (cm (cz (8)) (cm (b) (c)))))))) (ca (cm (j) (ca (cz (-4)) (ca (cm (cz (-8)) (b)) (cm (cz (-8)) (cm (b) (i)))))) (cm (cz (8)) (cm (b) (c)))))))) (ca (cm (rr) (ca (ca (cm (cz (-8)) (b)) (cm (cz (8)) (a))) (ca (cm (i) (ca (cm (cz (-8)) (b)) (ca (cm (cz (16)) (a)) (cm (cz (8)) (cm (a) (i)))))) (cm (j) (ca (ca (cm (cz (-16)) (b)) (cm (cz (8)) (a))) (ca (cm (i) (ca (cm (cz (-16)) (b)) (ca (cm (cz (16)) (a)) (cm (cz (8)) (cm (a) (i)))))) (cm (j) (ca (cm (cz (-8)) (b)) (cm (cz (-8)) (cm (b) (i))))))))))) (cm (cz (8)) (cm (b) (c)))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e12 - (ca (ca (cz (-8)) (ca (cm (cz (-4)) (b)) (cm (cz (8)) (a)))) (ca (cm (j) (ca (ca (cz (-24)) (cm (cz (-8)) (b))) (ca (cm (cz (8)) (a)) (ca (cm (i) (ca (cz (-8)) (cm (cz (8)) (a)))) (cm (j) (ca (cz (-16)) (ca (cm (cz (-8)) (i)) (cm (cz (-4)) (b))))))))) (ca (cm (rr) (ca (cz (-8)) (ca (cm (cz (-8)) (i)) (cm (j) (ca (cz (-16)) (ca (cm (cz (-16)) (i)) (cm (j) (ca (cz (-8)) (cm (cz (-8)) (i)))))))))) (cm (cz (8)) (cm (a) (i)))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e13 - (ca (cz (-4)) (cm (j) (ca (cz (-8)) (cm (cz (-4)) (j))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · have hm : cz (2) * (ca (ca (cm (b) (ca (cz (10)) (cm (cz (-4)) (b)))) (cm (d) (ca (cz (4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d)))))) (ca (cm (i) (ca (cm (b) (ca (cz (16)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (-4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (cz (6)) (cm (b) (i)))))) (ca (cm (j) (ca (cm (b) (ca (cz (10)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (i) (ca (cm (b) (ca (cz (16)) (cm (cz (-4)) (b)))) (ca (cm (d) (ca (cz (-4)) (ca (cm (cz (-8)) (b)) (cm (cz (4)) (d))))) (cm (cz (6)) (cm (b) (i))))))))) (cm (rr) (ca (ca (cz (2)) (cm (cz (-7)) (b))) (ca (cm (cz (2)) (d)) (ca (cm (i) (ca (ca (cz (2)) (cm (cz (-16)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (-9)) (cm (b) (i)))))) (cm (j) (ca (ca (cz (2)) (cm (cz (-7)) (b))) (ca (cm (cz (2)) (d)) (cm (i) (ca (ca (cz (2)) (cm (cz (-16)) (b))) (ca (cm (cz (-2)) (d)) (cm (cz (-9)) (cm (b) (i)))))))))))))))) = 0 := by
      linear_combination (norm := skip) e14 - (ca (ca (cz (4)) (ca (cm (b) (ca (cz (-8)) (cm (cz (4)) (b)))) (cm (d) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b)))))) (ca (cm (i) (ca (ca (cz (4)) (cm (b) (ca (cz (-16)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b)))) (cm (cz (-8)) (cm (b) (i)))))) (ca (cm (j) (ca (ca (cz (4)) (cm (b) (ca (cz (-8)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b)))) (cm (i) (ca (ca (cz (4)) (cm (b) (ca (cz (-16)) (cm (cz (4)) (b))))) (ca (cm (d) (ca (cm (cz (-4)) (d)) (cm (cz (8)) (b)))) (cm (cz (-8)) (cm (b) (i))))))))) (cm (rr) (ca (cm (cz (8)) (b)) (ca (cm (i) (ca (cm (cz (16)) (b)) (cm (cz (8)) (cm (b) (i))))) (cm (j) (ca (cm (cz (8)) (b)) (cm (i) (ca (cm (cz (16)) (b)) (cm (cz (8)) (cm (b) (i))))))))))))) * e19
      simp only [ca, cm, cp, cz]
      ring
    have hc : cz (2) ≠ 0 := by norm_num [cz]
    exact (mul_eq_zero.mp hm).resolve_left hc
  · linear_combination (norm := skip) e15 - (ca (ca (cz (-8)) (ca (cm (cz (-4)) (a)) (cm (cz (8)) (b)))) (ca (cm (i) (ca (ca (cz (-24)) (cm (cz (-8)) (a))) (ca (cm (cz (8)) (b)) (cm (i) (ca (cz (-16)) (cm (cz (-4)) (a))))))) (ca (cm (j) (ca (cm (cz (8)) (b)) (cm (i) (ca (cz (-8)) (ca (cm (cz (-8)) (i)) (cm (cz (8)) (b))))))) (cm (rr) (ca (cz (8)) (ca (cm (i) (ca (cz (16)) (cm (cz (8)) (i)))) (cm (j) (ca (cz (8)) (cm (i) (ca (cz (16)) (cm (cz (8)) (i)))))))))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · have hm : cz (2) * (ca (ca (cz (1)) (ca (cm (c) (ca (cz (-1)) (cm (cz (-1)) (b)))) (cm (d) (ca (cz (-1)) (ca (c) (cm (cz (-1)) (a))))))) (ca (ca (cm (i) (ca (c) (cm (cz (2)) (a)))) (cm (j) (ca (d) (ca (cm (cz (-3)) (i)) (cm (cz (2)) (b)))))) (ca (cm (rr) (ca (ca (b) (cm (cz (-1)) (a))) (ca (cm (i) (ca (cz (-2)) (cm (cz (-1)) (a)))) (cm (j) (ca (cz (2)) (b)))))) (cm (cz (-1)) (cm (a) (b)))))) = 0 := by
      linear_combination (norm := skip) e16 - (ca (cz (4)) (ca (cm (cz (4)) (i)) (cm (j) (ca (cz (4)) (cm (cz (4)) (i)))))) * e19
      simp only [ca, cm, cp, cz]
      ring
    have hc : cz (2) ≠ 0 := by norm_num [cz]
    exact (mul_eq_zero.mp hm).resolve_left hc
  · linear_combination (norm := skip) e17 - (ca (cm (cz (-4)) (b)) (cm (i) (ca (cm (cz (-8)) (b)) (cm (cz (-4)) (cm (b) (i)))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · linear_combination (norm := skip) e18 - (ca (cz (-4)) (cm (i) (ca (cz (-8)) (cm (cz (-4)) (i))))) * e19
    simp only [ca, cm, cp, cz]
    ring
  · exact e19

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate


namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

def ca (x y : ℂ) : ℂ := x + y
def cm (x y : ℂ) : ℂ := x * y
def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n
def cz (z : ℤ) : ℂ := z

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

def model (a b c d e f g k i j rr x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![ca (cm (cz (1)) (cm (a) (y))) (cm (cz (1)) (cm (b) (z))), ca (cm (cz (1)) (cm (c) (y))) (cm (cz (1)) (cm (d) (z))), cm (cz (1)) (cm (e) (z)), cm (cz (1)) (cm (f) (y))], ![ca (cm (cz (1)) (cm (c) (y))) (cm (cz (1)) (cm (d) (z))), ca (cm (cz (1)) (cm (g) (y))) (cm (cz (1)) (cm (k) (z))), cm (cz (1)) (cm (i) (z)), cm (cz (1)) (cm (j) (y))], ![cm (cz (1)) (cm (e) (z)), cm (cz (1)) (cm (i) (z)), ca (ca (cm (cz (-1)) (cm (b) (z))) (ca (cm (cz (-2)) (cm (d) (z))) (cm (cz (-2)) (cm (e) (z))))) (ca (ca (cm (cz (-1)) (cm (k) (z))) (cm (cz (-2)) (cm (i) (z)))) (ca (cm (cz (1)) (cm (rr) (x))) (cm (cz (-1)) (x)))), cm (cz (1)) (x)], ![cm (cz (1)) (cm (f) (y)), cm (cz (1)) (cm (j) (y)), cm (cz (1)) (x), ca (ca (cm (cz (-1)) (cm (a) (y))) (ca (cm (cz (-2)) (cm (c) (y))) (cm (cz (-2)) (cm (f) (y))))) (ca (ca (cm (cz (-1)) (cm (g) (y))) (cm (cz (-2)) (cm (j) (y)))) (ca (cm (cz (-1)) (cm (rr) (x))) (cm (cz (-1)) (x))))]]

def coefficients (a b c d e f g k i j rr : ℂ) : Fin 19 → ℂ :=
  ![ca (ca (ca (ca (cm (cm (cz (-1)) (cp a 2)) (cm (g) (rr))) (ca (cm (cz (1)) (cm (cp a 2) (g))) (cm (cm (cz (-1)) (a)) (cm (cp c 2) (rr))))) (ca (cm (cz (1)) (cm (a) (cp c 2))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (c) (g)))))) (ca (ca (cm (cm (cz (-2)) (a)) (cm (f) (cm (g) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (f) (g))) (cm (cm (cz (-1)) (a)) (cm (cp g 2) (rr))))) (ca (ca (cm (cz (1)) (cm (a) (cp g 2))) (cm (cm (cz (-2)) (a)) (cm (g) (cm (j) (rr))))) (ca (cm (cm (cz (2)) (a)) (cm (g) (j))) (cm (cm (cz (1)) (a)) (cm (cp j 2) (rr))))))) (ca (ca (ca (cm (cz (-1)) (cm (a) (cp j 2))) (ca (cm (cz (-2)) (cm (cp c 3) (rr))) (cm (cz (2)) (cp c 3)))) (ca (cm (cm (cz (-2)) (cp c 2)) (cm (f) (rr))) (ca (cm (cz (2)) (cm (cp c 2) (f))) (cm (cm (cz (-1)) (cp c 2)) (cm (g) (rr)))))) (ca (ca (cm (cz (1)) (cm (cp c 2) (g))) (ca (cm (cm (cz (-2)) (cp c 2)) (cm (j) (rr))) (cm (cz (2)) (cm (cp c 2) (j))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (f) (cm (j) (rr)))) (cm (cm (cz (-2)) (c)) (cm (f) (j)))) (ca (cm (cm (cz (1)) (cp f 2)) (cm (g) (rr))) (cm (cz (-1)) (cm (cp f 2) (g))))))),
    ca (ca (ca (ca (ca (cm (cm (cz (-1)) (cp a 2)) (cm (k) (rr))) (ca (cm (cz (1)) (cm (cp a 2) (k))) (cm (cm (cz (2)) (a)) (cm (b) (g))))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (d) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (c) (d))) (cm (cm (cz (-2)) (a)) (cm (c) (cm (k) (rr))))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (c) (k))) (ca (cm (cm (cz (2)) (a)) (cm (d) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (d) (g))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (cm (g) (rr)))) (cm (cm (cz (2)) (a)) (cm (e) (g)))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (cm (k) (rr)))) (cm (cm (cz (2)) (a)) (cm (f) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (g) (k))) (ca (cm (cm (cz (2)) (a)) (cm (g) (cm (i) (rr)))) (cm (cm (cz (2)) (a)) (cm (g) (i))))) (ca (cm (cm (cz (-2)) (a)) (cm (k) (cm (j) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (k) (j))) (cm (cm (cz (2)) (a)) (cm (i) (j)))))) (ca (ca (cm (cm (cz (1)) (b)) (cm (cp c 2) (rr))) (ca (cm (cz (1)) (cm (b) (cp c 2))) (cm (cm (cz (-2)) (b)) (cm (c) (cm (g) (rr)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (c) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (cm (g) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (f) (g))) (cm (cm (cz (-1)) (b)) (cm (cp g 2) (rr)))))))) (ca (ca (ca (ca (cm (cz (1)) (cm (b) (cp g 2))) (ca (cm (cm (cz (-2)) (b)) (cm (g) (cm (j) (rr)))) (cm (cm (cz (2)) (b)) (cm (g) (j))))) (ca (cm (cm (cz (1)) (b)) (cm (cp j 2) (rr))) (ca (cm (cz (-1)) (cm (b) (cp j 2))) (cm (cm (cz (-2)) (cp c 2)) (cm (d) (rr)))))) (ca (ca (cm (cz (6)) (cm (cp c 2) (d))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (e) (rr))) (cm (cz (2)) (cm (cp c 2) (e))))) (ca (ca (cm (cm (cz (1)) (cp c 2)) (cm (k) (rr))) (cm (cz (1)) (cm (cp c 2) (k)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (i) (rr))) (cm (cz (2)) (cm (cp c 2) (i))))))) (ca (ca (ca (cm (cm (cz (-4)) (c)) (cm (d) (cm (f) (rr)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (f))) (cm (cm (cz (-2)) (c)) (cm (d) (cm (g) (rr)))))) (ca (cm (cm (cz (2)) (c)) (cm (d) (g))) (ca (cm (cm (cz (-4)) (c)) (cm (d) (cm (j) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (j)))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (e) (j))) (ca (cm (cm (cz (2)) (c)) (cm (f) (i))) (cm (cm (cz (2)) (d)) (cm (f) (cm (j) (rr)))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (f) (j))) (cm (cm (cz (2)) (e)) (cm (f) (g)))) (ca (cm (cm (cz (1)) (cp f 2)) (cm (k) (rr))) (cm (cz (-1)) (cm (cp f 2) (k)))))))),
    ca (ca (ca (ca (cm (cz (-1)) (cm (cp a 2) (rr))) (ca (cm (cz (1)) (cp a 2)) (cm (cm (cz (-4)) (a)) (cm (c) (rr))))) (ca (ca (cm (cz (4)) (cm (a) (c))) (cm (cm (cz (-2)) (a)) (cm (f) (rr)))) (ca (cm (cz (2)) (cm (a) (f))) (cm (cm (cz (-2)) (a)) (cm (g) (rr)))))) (ca (ca (cm (cz (2)) (cm (a) (g))) (ca (cm (cz (2)) (cm (a) (j))) (cm (cz (-4)) (cm (cp c 2) (rr))))) (ca (ca (cm (cz (4)) (cp c 2)) (cm (cm (cz (-2)) (c)) (cm (f) (rr)))) (ca (cm (cz (4)) (cm (c) (f))) (cm (cm (cz (-4)) (c)) (cm (g) (rr))))))) (ca (ca (ca (cm (cz (4)) (cm (c) (g))) (ca (cm (cm (cz (-2)) (c)) (cm (j) (rr))) (cm (cz (4)) (cm (c) (j))))) (ca (ca (cm (cz (1)) (cm (cp f 2) (rr))) (cm (cz (-1)) (cp f 2))) (ca (cm (cz (2)) (cm (f) (g))) (cm (cm (cz (2)) (f)) (cm (j) (rr)))))) (ca (ca (cm (cz (-2)) (cm (f) (j))) (ca (cm (cz (-1)) (cm (cp g 2) (rr))) (cm (cz (1)) (cp g 2)))) (ca (ca (cm (cm (cz (-2)) (g)) (cm (j) (rr))) (cm (cz (2)) (cm (g) (j)))) (ca (cm (cz (1)) (cm (cp j 2) (rr))) (cm (cz (-1)) (cp j 2)))))),
    ca (ca (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (k))) (ca (cm (cm (cz (-1)) (a)) (cm (cp d 2) (rr))) (cm (cz (1)) (cm (a) (cp d 2))))) (ca (cm (cm (cz (2)) (a)) (cm (d) (cm (k) (rr)))) (ca (cm (cm (cz (2)) (a)) (cm (d) (k))) (cm (cm (cz (2)) (a)) (cm (e) (cm (k) (rr))))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (k))) (ca (cm (cm (cz (1)) (a)) (cm (cp k 2) (rr))) (cm (cz (1)) (cm (a) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (k) (cm (i) (rr)))) (cm (cm (cz (2)) (a)) (cm (k) (i)))) (ca (cm (cm (cz (-1)) (a)) (cm (cp i 2) (rr))) (cm (cz (-1)) (cm (a) (cp i 2))))))) (ca (ca (ca (cm (cm (cz (1)) (cp b 2)) (cm (g) (rr))) (ca (cm (cz (1)) (cm (cp b 2) (g))) (cm (cm (cz (2)) (b)) (cm (c) (cm (d) (rr)))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (d))) (ca (cm (cm (cz (-2)) (b)) (cm (c) (cm (k) (rr)))) (cm (cm (cz (2)) (b)) (cm (c) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (d) (cm (g) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (d) (g))) (cm (cm (cz (2)) (b)) (cm (e) (cm (g) (rr)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (cm (k) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (f) (k))) (cm (cm (cz (2)) (b)) (cm (g) (k)))))))) (ca (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (i) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (g) (i))) (cm (cm (cz (-2)) (b)) (cm (k) (cm (j) (rr)))))) (ca (cm (cm (cz (2)) (b)) (cm (k) (j))) (ca (cm (cm (cz (2)) (b)) (cm (i) (j))) (cm (cm (cz (2)) (c)) (cm (cp d 2) (rr)))))) (ca (ca (cm (cz (6)) (cm (c) (cp d 2))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (e) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (e))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (d) (cm (k) (rr)))) (cm (cm (cz (2)) (c)) (cm (d) (k)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (i) (rr)))) (cm (cm (cz (4)) (c)) (cm (d) (i))))))) (ca (ca (ca (cm (cm (cz (-2)) (c)) (cm (e) (cm (i) (rr)))) (ca (cm (cm (cz (-2)) (c)) (cm (e) (i))) (cm (cm (cz (-2)) (cp d 2)) (cm (f) (rr))))) (ca (cm (cz (2)) (cm (cp d 2) (f))) (ca (cm (cm (cz (-1)) (cp d 2)) (cm (g) (rr))) (cm (cz (1)) (cm (cp d 2) (g)))))) (ca (ca (cm (cm (cz (-2)) (cp d 2)) (cm (j) (rr))) (ca (cm (cz (2)) (cm (cp d 2) (j))) (cm (cm (cz (2)) (d)) (cm (e) (j))))) (ca (ca (cm (cm (cz (2)) (d)) (cm (f) (i))) (cm (cm (cz (-1)) (cp e 2)) (cm (g) (rr)))) (ca (cm (cz (-1)) (cm (cp e 2) (g))) (cm (cm (cz (2)) (e)) (cm (f) (k)))))))),
    ca (ca (ca (ca (ca (cm (cz (2)) (cm (a) (b))) (cm (cz (4)) (cm (a) (d)))) (ca (cm (cm (cz (2)) (a)) (cm (e) (rr))) (cm (cz (2)) (cm (a) (e))))) (ca (ca (cm (cz (2)) (cm (a) (k))) (cm (cz (2)) (cm (a) (i)))) (ca (cm (cz (4)) (cm (b) (c))) (cm (cm (cz (-2)) (b)) (cm (f) (rr)))))) (ca (ca (ca (cm (cz (2)) (cm (b) (f))) (cm (cz (2)) (cm (b) (g)))) (ca (cm (cz (2)) (cm (b) (j))) (cm (cz (8)) (cm (c) (d))))) (ca (ca (cm (cm (cz (2)) (c)) (cm (e) (rr))) (cm (cz (4)) (cm (c) (e)))) (ca (cm (cz (4)) (cm (c) (k))) (cm (cm (cz (2)) (c)) (cm (i) (rr))))))) (ca (ca (ca (ca (cm (cz (4)) (cm (c) (i))) (cm (cm (cz (-2)) (d)) (cm (f) (rr)))) (ca (cm (cz (4)) (cm (d) (f))) (cm (cz (4)) (cm (d) (g))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (j) (rr))) (cm (cz (4)) (cm (d) (j)))) (ca (cm (cz (2)) (cm (e) (f))) (cm (cz (2)) (cm (e) (g)))))) (ca (ca (ca (cm (cz (2)) (cm (e) (j))) (cm (cz (2)) (cm (f) (k)))) (ca (cm (cz (2)) (cm (f) (i))) (cm (cz (2)) (cm (g) (k))))) (ca (ca (cm (cm (cz (2)) (g)) (cm (i) (rr))) (cm (cz (2)) (cm (g) (i)))) (ca (cm (cm (cz (-2)) (k)) (cm (j) (rr))) (ca (cm (cz (2)) (cm (k) (j))) (cm (cz (2)) (cm (i) (j)))))))),
    ca (ca (ca (cm (cz (-2)) (cm (a) (rr))) (cm (cz (2)) (a))) (ca (cm (cz (-4)) (cm (c) (rr))) (cm (cz (4)) (c)))) (ca (ca (cm (cz (4)) (f)) (cm (cz (-2)) (cm (g) (rr)))) (ca (cm (cz (2)) (g)) (cm (cz (4)) (j)))),
    ca (ca (ca (ca (cm (cm (cz (1)) (cp b 2)) (cm (k) (rr))) (ca (cm (cz (1)) (cm (cp b 2) (k))) (cm (cm (cz (1)) (b)) (cm (cp d 2) (rr))))) (ca (cm (cz (1)) (cm (b) (cp d 2))) (ca (cm (cm (cz (2)) (b)) (cm (d) (cm (k) (rr)))) (cm (cm (cz (2)) (b)) (cm (d) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (cm (k) (rr)))) (ca (cm (cm (cz (2)) (b)) (cm (e) (k))) (cm (cm (cz (1)) (b)) (cm (cp k 2) (rr))))) (ca (ca (cm (cz (1)) (cm (b) (cp k 2))) (cm (cm (cz (2)) (b)) (cm (k) (cm (i) (rr))))) (ca (cm (cm (cz (2)) (b)) (cm (k) (i))) (cm (cm (cz (-1)) (b)) (cm (cp i 2) (rr))))))) (ca (ca (ca (cm (cz (-1)) (cm (b) (cp i 2))) (ca (cm (cz (2)) (cm (cp d 3) (rr))) (cm (cz (2)) (cp d 3)))) (ca (cm (cm (cz (2)) (cp d 2)) (cm (e) (rr))) (ca (cm (cz (2)) (cm (cp d 2) (e))) (cm (cm (cz (1)) (cp d 2)) (cm (k) (rr)))))) (ca (ca (cm (cz (1)) (cm (cp d 2) (k))) (ca (cm (cm (cz (2)) (cp d 2)) (cm (i) (rr))) (cm (cz (2)) (cm (cp d 2) (i))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (e) (cm (i) (rr)))) (cm (cm (cz (-2)) (d)) (cm (e) (i)))) (ca (cm (cm (cz (-1)) (cp e 2)) (cm (k) (rr))) (cm (cz (-1)) (cm (cp e 2) (k))))))),
    ca (ca (ca (ca (cm (cz (1)) (cm (cp b 2) (rr))) (ca (cm (cz (1)) (cp b 2)) (cm (cm (cz (4)) (b)) (cm (d) (rr))))) (ca (ca (cm (cz (4)) (cm (b) (d))) (cm (cm (cz (2)) (b)) (cm (e) (rr)))) (ca (cm (cz (2)) (cm (b) (e))) (cm (cm (cz (2)) (b)) (cm (k) (rr)))))) (ca (ca (cm (cz (2)) (cm (b) (k))) (ca (cm (cz (2)) (cm (b) (i))) (cm (cz (4)) (cm (cp d 2) (rr))))) (ca (ca (cm (cz (4)) (cp d 2)) (cm (cm (cz (2)) (d)) (cm (e) (rr)))) (ca (cm (cz (4)) (cm (d) (e))) (cm (cm (cz (4)) (d)) (cm (k) (rr))))))) (ca (ca (ca (cm (cz (4)) (cm (d) (k))) (ca (cm (cm (cz (2)) (d)) (cm (i) (rr))) (cm (cz (4)) (cm (d) (i))))) (ca (ca (cm (cz (-1)) (cm (cp e 2) (rr))) (cm (cz (-1)) (cp e 2))) (ca (cm (cz (2)) (cm (e) (k))) (cm (cm (cz (-2)) (e)) (cm (i) (rr)))))) (ca (ca (cm (cz (-2)) (cm (e) (i))) (ca (cm (cz (1)) (cm (cp k 2) (rr))) (cm (cz (1)) (cp k 2)))) (ca (ca (cm (cm (cz (2)) (k)) (cm (i) (rr))) (cm (cz (2)) (cm (k) (i)))) (ca (cm (cz (-1)) (cm (cp i 2) (rr))) (cm (cz (-1)) (cp i 2)))))),
    ca (ca (ca (cm (cz (2)) (cm (b) (rr))) (cm (cz (2)) (b))) (ca (cm (cz (4)) (cm (d) (rr))) (cm (cz (4)) (d)))) (ca (ca (cm (cz (4)) (e)) (cm (cz (2)) (cm (k) (rr)))) (ca (cm (cz (2)) (k)) (cm (cz (4)) (i)))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (cp a 2)) (cm (b) (g))) (cm (cm (cz (2)) (cp a 2)) (cm (d) (g)))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (e) (g))) (cm (cm (cz (1)) (cp a 2)) (cm (g) (k))))) (ca (ca (cm (cm (cz (2)) (cp a 2)) (cm (g) (i))) (cm (cm (cz (1)) (a)) (cm (b) (cp c 2)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (g)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (f) (g))))))) (ca (ca (ca (cm (cm (cz (1)) (a)) (cm (b) (cp g 2))) (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (j))))) (ca (cm (cm (cz (-1)) (a)) (cm (b) (cp j 2))) (cm (cm (cz (2)) (a)) (cm (cp c 2) (d))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (cp c 2) (e))) (cm (cm (cz (1)) (a)) (cm (cp c 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp c 2) (i))) (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (g)))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (e) (g)))) (cm (cm (cz (2)) (a)) (cm (c) (cm (g) (k))))) (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (g) (i)))) (cm (cm (cz (4)) (a)) (cm (d) (cm (f) (g)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (d) (cp g 2))) (cm (cm (cz (4)) (a)) (cm (d) (cm (g) (j))))) (ca (cm (cm (cz (-2)) (a)) (cm (d) (cp j 2))) (cm (cm (cz (4)) (a)) (cm (e) (cm (f) (g))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (e) (cp g 2))) (cm (cm (cz (4)) (a)) (cm (e) (cm (g) (j))))) (ca (cm (cm (cz (-2)) (a)) (cm (e) (cp j 2))) (cm (cm (cz (2)) (a)) (cm (f) (cm (g) (k)))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (f) (cm (g) (i)))) (cm (cm (cz (1)) (a)) (cm (cp g 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp g 2) (i))) (cm (cm (cz (2)) (a)) (cm (g) (cm (k) (j))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (g) (cm (i) (j)))) (cm (cm (cz (-1)) (a)) (cm (k) (cp j 2)))) (ca (cm (cm (cz (-2)) (a)) (cm (i) (cp j 2))) (cm (cz (2)) (cm (b) (cp c 3))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (cp c 2) (f))) (cm (cm (cz (1)) (b)) (cm (cp c 2) (g)))) (ca (cm (cm (cz (2)) (b)) (cm (cp c 2) (j))) (cm (cm (cz (-2)) (b)) (cm (c) (cm (f) (j))))))) (ca (ca (ca (cm (cm (cz (-1)) (b)) (cm (cp f 2) (g))) (cm (cz (4)) (cm (cp c 3) (d)))) (ca (cm (cz (4)) (cm (cp c 3) (e))) (cm (cz (2)) (cm (cp c 3) (k))))) (ca (ca (cm (cz (4)) (cm (cp c 3) (i))) (cm (cm (cz (4)) (cp c 2)) (cm (d) (f)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (d) (g))) (cm (cm (cz (4)) (cp c 2)) (cm (d) (j))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (e) (f))) (cm (cm (cz (2)) (cp c 2)) (cm (e) (g)))) (ca (cm (cm (cz (4)) (cp c 2)) (cm (e) (j))) (cm (cm (cz (2)) (cp c 2)) (cm (f) (k))))) (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (f) (i))) (cm (cm (cz (1)) (cp c 2)) (cm (g) (k)))) (ca (cm (cm (cz (2)) (cp c 2)) (cm (g) (i))) (cm (cm (cz (2)) (cp c 2)) (cm (k) (j)))))) (ca (ca (ca (cm (cm (cz (4)) (cp c 2)) (cm (i) (j))) (cm (cm (cz (-4)) (c)) (cm (d) (cm (f) (j))))) (ca (cm (cm (cz (-4)) (c)) (cm (e) (cm (f) (j)))) (cm (cm (cz (-2)) (c)) (cm (f) (cm (k) (j)))))) (ca (ca (cm (cm (cz (-4)) (c)) (cm (f) (cm (i) (j)))) (cm (cm (cz (-2)) (d)) (cm (cp f 2) (g)))) (ca (cm (cm (cz (-2)) (e)) (cm (cp f 2) (g))) (ca (cm (cm (cz (-1)) (cp f 2)) (cm (g) (k))) (cm (cm (cz (-2)) (cp f 2)) (cm (g) (i))))))))),
    ca (ca (ca (cm (cz (-1)) (cm (cp a 2) (g))) (ca (cm (cz (-1)) (cm (a) (cp c 2))) (cm (cm (cz (-2)) (a)) (cm (c) (g))))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (g))) (ca (cm (cz (-1)) (cm (a) (cp g 2))) (cm (cm (cz (-2)) (a)) (cm (g) (j)))))) (ca (ca (cm (cz (1)) (cm (a) (cp j 2))) (ca (cm (cz (-2)) (cp c 3)) (cm (cz (-2)) (cm (cp c 2) (f))))) (ca (ca (cm (cz (-1)) (cm (cp c 2) (g))) (cm (cz (-2)) (cm (cp c 2) (j)))) (ca (cm (cm (cz (2)) (c)) (cm (f) (j))) (cm (cz (1)) (cm (cp f 2) (g)))))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (cp a 2)) (cm (b) (k))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (d) (k))) (cm (cm (cz (2)) (cp a 2)) (cm (e) (k))))) (ca (cm (cz (1)) (cm (cp a 2) (cp k 2))) (ca (cm (cm (cz (2)) (cp a 2)) (cm (k) (i))) (cm (cz (-1)) (cm (cp a 2) (cp i 2)))))) (ca (ca (cm (cm (cz (1)) (a)) (cm (cp b 2) (g))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (d)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (c) (k)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (d) (g)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (e) (g))))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (f) (k)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (k)))))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (g) (i)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (k) (j)))) (cm (cm (cz (4)) (a)) (cm (c) (cp d 2))))) (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (e)))) (ca (cm (cm (cz (6)) (a)) (cm (c) (cm (d) (k)))) (cm (cm (cz (4)) (a)) (cm (c) (cm (d) (i))))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (e) (k)))) (ca (cm (cm (cz (-2)) (a)) (cm (c) (cm (e) (i)))) (cm (cm (cz (2)) (a)) (cm (c) (cp k 2))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (c) (cm (k) (i)))) (cm (cm (cz (-2)) (a)) (cm (c) (cp i 2)))) (ca (cm (cm (cz (4)) (a)) (cm (d) (cm (f) (k)))) (cm (cm (cz (2)) (a)) (cm (d) (cm (g) (k))))))))) (ca (ca (ca (ca (cm (cm (cz (4)) (a)) (cm (d) (cm (k) (j)))) (ca (cm (cm (cz (-1)) (a)) (cm (cp e 2) (g))) (cm (cm (cz (4)) (a)) (cm (e) (cm (f) (k)))))) (ca (cm (cm (cz (2)) (a)) (cm (e) (cm (g) (k)))) (ca (cm (cm (cz (4)) (a)) (cm (e) (cm (k) (j)))) (cm (cm (cz (2)) (a)) (cm (f) (cp k 2)))))) (ca (ca (cm (cm (cz (4)) (a)) (cm (f) (cm (k) (i)))) (ca (cm (cm (cz (-2)) (a)) (cm (f) (cp i 2))) (cm (cm (cz (1)) (a)) (cm (g) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (g) (cm (k) (i)))) (cm (cm (cz (-1)) (a)) (cm (g) (cp i 2)))) (ca (cm (cm (cz (2)) (a)) (cm (cp k 2) (j))) (cm (cm (cz (4)) (a)) (cm (k) (cm (i) (j)))))))) (ca (ca (ca (cm (cm (cz (-2)) (a)) (cm (cp i 2) (j))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (c) (g))) (cm (cm (cz (2)) (cp b 2)) (cm (f) (g))))) (ca (cm (cz (1)) (cm (cp b 2) (cp g 2))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (g) (j))) (cm (cz (-1)) (cm (cp b 2) (cp j 2)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (cp c 2) (d))) (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (f)))) (cm (cm (cz (6)) (b)) (cm (c) (cm (d) (g)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (j)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (e) (g))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (cm (g) (k)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (g) (i)))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (f) (g)))) (ca (cm (cm (cz (-2)) (b)) (cm (d) (cm (f) (j)))) (cm (cm (cz (2)) (b)) (cm (d) (cp g 2))))) (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (g) (j)))) (ca (cm (cm (cz (-2)) (b)) (cm (d) (cp j 2))) (cm (cm (cz (4)) (b)) (cm (e) (cm (f) (g))))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (e) (cp g 2))) (ca (cm (cm (cz (4)) (b)) (cm (e) (cm (g) (j)))) (cm (cm (cz (-2)) (b)) (cm (e) (cp j 2))))) (ca (ca (cm (cm (cz (-1)) (b)) (cm (cp f 2) (k))) (cm (cm (cz (2)) (b)) (cm (f) (cm (g) (k))))) (ca (cm (cm (cz (4)) (b)) (cm (f) (cm (g) (i)))) (cm (cm (cz (1)) (b)) (cm (cp g 2) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (cp g 2) (i))) (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (k) (j)))) (cm (cm (cz (4)) (b)) (cm (g) (cm (i) (j)))))) (ca (cm (cm (cz (-1)) (b)) (cm (k) (cp j 2))) (ca (cm (cm (cz (-2)) (b)) (cm (i) (cp j 2))) (cm (cz (8)) (cm (cp c 2) (cp d 2)))))) (ca (ca (cm (cm (cz (8)) (cp c 2)) (cm (d) (e))) (ca (cm (cm (cz (4)) (cp c 2)) (cm (d) (k))) (cm (cm (cz (8)) (cp c 2)) (cm (d) (i))))) (ca (ca (cm (cm (cz (-4)) (cp c 2)) (cm (e) (i))) (cm (cm (cz (8)) (c)) (cm (cp d 2) (f)))) (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (g))) (cm (cm (cz (8)) (c)) (cm (cp d 2) (j)))))))) (ca (ca (ca (ca (cm (cm (cz (8)) (c)) (cm (d) (cm (e) (f)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (e) (g)))) (cm (cm (cz (8)) (c)) (cm (d) (cm (e) (j)))))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (f) (k)))) (ca (cm (cm (cz (8)) (c)) (cm (d) (cm (f) (i)))) (cm (cm (cz (2)) (c)) (cm (d) (cm (g) (k))))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (g) (i)))) (ca (cm (cm (cz (4)) (c)) (cm (d) (cm (k) (j)))) (cm (cm (cz (8)) (c)) (cm (d) (cm (i) (j)))))) (ca (ca (cm (cm (cz (-2)) (c)) (cm (cp e 2) (g))) (cm (cm (cz (-4)) (c)) (cm (e) (cm (f) (i))))) (ca (cm (cm (cz (-2)) (c)) (cm (e) (cm (g) (i)))) (cm (cm (cz (-4)) (c)) (cm (e) (cm (i) (j)))))))) (ca (ca (ca (cm (cm (cz (-4)) (cp d 2)) (cm (f) (j))) (ca (cm (cm (cz (-4)) (d)) (cm (e) (cm (f) (j)))) (cm (cm (cz (-2)) (d)) (cm (cp f 2) (k))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (f) (cm (k) (j)))) (cm (cm (cz (-4)) (d)) (cm (f) (cm (i) (j))))) (ca (cm (cm (cz (-2)) (cp e 2)) (cm (f) (g))) (cm (cz (-1)) (cm (cp e 2) (cp g 2)))))) (ca (ca (cm (cm (cz (-2)) (cp e 2)) (cm (g) (j))) (ca (cm (cz (1)) (cm (cp e 2) (cp j 2))) (cm (cm (cz (-2)) (e)) (cm (cp f 2) (k))))) (ca (ca (cm (cm (cz (2)) (e)) (cm (f) (cm (i) (j)))) (cm (cz (-1)) (cm (cp f 2) (cp k 2)))) (ca (cm (cm (cz (-2)) (cp f 2)) (cm (k) (i))) (cm (cz (1)) (cm (cp f 2) (cp i 2))))))))),
    ca (ca (ca (ca (ca (cm (cz (1)) (cm (cp a 2) (b))) (ca (cm (cz (2)) (cm (cp a 2) (d))) (cm (cz (2)) (cm (cp a 2) (e))))) (ca (cm (cm (cz (4)) (a)) (cm (b) (c))) (ca (cm (cm (cz (2)) (a)) (cm (b) (f))) (cm (cm (cz (6)) (a)) (cm (c) (d)))))) (ca (ca (cm (cm (cz (6)) (a)) (cm (c) (e))) (ca (cm (cm (cz (2)) (a)) (cm (c) (k))) (cm (cm (cz (2)) (a)) (cm (c) (i))))) (ca (cm (cm (cz (4)) (a)) (cm (d) (f))) (ca (cm (cm (cz (2)) (a)) (cm (d) (g))) (cm (cm (cz (4)) (a)) (cm (e) (f))))))) (ca (ca (ca (cm (cm (cz (-2)) (a)) (cm (k) (j))) (ca (cm (cm (cz (-2)) (a)) (cm (i) (j))) (cm (cz (3)) (cm (b) (cp c 2))))) (ca (cm (cm (cz (2)) (b)) (cm (c) (f))) (ca (cm (cm (cz (2)) (b)) (cm (c) (g))) (cm (cm (cz (2)) (b)) (cm (c) (j)))))) (ca (ca (cm (cz (-1)) (cm (b) (cp f 2))) (ca (cm (cm (cz (-2)) (b)) (cm (f) (g))) (cm (cm (cz (-2)) (b)) (cm (f) (j))))) (ca (cm (cz (2)) (cm (cp c 2) (d))) (ca (cm (cz (2)) (cm (cp c 2) (e))) (cm (cz (3)) (cm (cp c 2) (k)))))))) (ca (ca (ca (ca (cm (cz (2)) (cm (cp c 2) (i))) (ca (cm (cm (cz (6)) (c)) (cm (d) (g))) (cm (cm (cz (2)) (c)) (cm (e) (g))))) (ca (cm (cm (cz (2)) (c)) (cm (e) (j))) (ca (cm (cm (cz (2)) (c)) (cm (f) (k))) (cm (cm (cz (2)) (c)) (cm (f) (i)))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (g) (k))) (ca (cm (cm (cz (6)) (c)) (cm (g) (i))) (cm (cm (cz (2)) (c)) (cm (k) (j))))) (ca (cm (cz (-2)) (cm (d) (cp f 2))) (ca (cm (cm (cz (-2)) (d)) (cm (f) (j))) (cm (cz (2)) (cm (d) (cp g 2))))))) (ca (ca (ca (cm (cm (cz (4)) (d)) (cm (g) (j))) (ca (cm (cz (-2)) (cm (d) (cp j 2))) (cm (cz (-2)) (cm (e) (cp f 2))))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (g))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (j))) (cm (cm (cz (-2)) (f)) (cm (k) (j)))))) (ca (ca (cm (cm (cz (-2)) (f)) (cm (i) (j))) (ca (cm (cz (1)) (cm (cp g 2) (k))) (cm (cz (2)) (cm (cp g 2) (i))))) (ca (ca (cm (cm (cz (2)) (g)) (cm (k) (j))) (cm (cm (cz (4)) (g)) (cm (i) (j)))) (ca (cm (cz (-1)) (cm (k) (cp j 2))) (cm (cz (-2)) (cm (i) (cp j 2)))))))),
    ca (ca (ca (cm (cz (-2)) (cp a 2)) (ca (cm (cz (-8)) (cm (a) (c))) (cm (cz (-4)) (cm (a) (f))))) (ca (cm (cz (-2)) (cm (a) (g))) (ca (cm (cz (-6)) (cp c 2)) (cm (cz (-4)) (cm (c) (f)))))) (ca (ca (cm (cz (-8)) (cm (c) (g))) (ca (cm (cz (-4)) (cm (c) (j))) (cm (cz (2)) (cp f 2)))) (ca (ca (cm (cz (4)) (cm (f) (j))) (cm (cz (-2)) (cp g 2))) (ca (cm (cz (-4)) (cm (g) (j))) (cm (cz (2)) (cp j 2))))),
    ca (ca (ca (ca (ca (ca (cm (cm (cz (1)) (a)) (cm (cp b 2) (k))) (cm (cm (cz (1)) (a)) (cm (b) (cp d 2)))) (ca (cm (cm (cz (2)) (a)) (cm (b) (cm (d) (k)))) (cm (cm (cz (2)) (a)) (cm (b) (cm (e) (k)))))) (ca (ca (cm (cm (cz (1)) (a)) (cm (b) (cp k 2))) (cm (cm (cz (2)) (a)) (cm (b) (cm (k) (i))))) (ca (cm (cm (cz (-1)) (a)) (cm (b) (cp i 2))) (cm (cz (2)) (cm (a) (cp d 3)))))) (ca (ca (ca (cm (cm (cz (2)) (a)) (cm (cp d 2) (e))) (cm (cm (cz (1)) (a)) (cm (cp d 2) (k)))) (ca (cm (cm (cz (2)) (a)) (cm (cp d 2) (i))) (cm (cm (cz (-2)) (a)) (cm (d) (cm (e) (i)))))) (ca (ca (cm (cm (cz (-1)) (a)) (cm (cp e 2) (k))) (cm (cm (cz (2)) (cp b 2)) (cm (c) (k)))) (ca (cm (cm (cz (2)) (cp b 2)) (cm (f) (k))) (cm (cm (cz (1)) (cp b 2)) (cm (g) (k))))))) (ca (ca (ca (ca (cm (cm (cz (2)) (cp b 2)) (cm (k) (j))) (cm (cm (cz (2)) (b)) (cm (c) (cp d 2)))) (ca (cm (cm (cz (4)) (b)) (cm (c) (cm (d) (k)))) (cm (cm (cz (4)) (b)) (cm (c) (cm (e) (k)))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (c) (cp k 2))) (cm (cm (cz (4)) (b)) (cm (c) (cm (k) (i))))) (ca (cm (cm (cz (-2)) (b)) (cm (c) (cp i 2))) (cm (cm (cz (2)) (b)) (cm (cp d 2) (f)))))) (ca (ca (ca (cm (cm (cz (1)) (b)) (cm (cp d 2) (g))) (cm (cm (cz (2)) (b)) (cm (cp d 2) (j)))) (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (f) (k)))) (cm (cm (cz (2)) (b)) (cm (d) (cm (g) (k)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (d) (cm (k) (j)))) (cm (cm (cz (4)) (b)) (cm (e) (cm (f) (k))))) (ca (cm (cm (cz (2)) (b)) (cm (e) (cm (g) (k)))) (cm (cm (cz (4)) (b)) (cm (e) (cm (k) (j))))))))) (ca (ca (ca (ca (ca (cm (cm (cz (2)) (b)) (cm (f) (cp k 2))) (cm (cm (cz (4)) (b)) (cm (f) (cm (k) (i))))) (ca (cm (cm (cz (-2)) (b)) (cm (f) (cp i 2))) (cm (cm (cz (1)) (b)) (cm (g) (cp k 2))))) (ca (ca (cm (cm (cz (2)) (b)) (cm (g) (cm (k) (i)))) (cm (cm (cz (-1)) (b)) (cm (g) (cp i 2)))) (ca (cm (cm (cz (2)) (b)) (cm (cp k 2) (j))) (cm (cm (cz (4)) (b)) (cm (k) (cm (i) (j))))))) (ca (ca (ca (cm (cm (cz (-2)) (b)) (cm (cp i 2) (j))) (cm (cz (4)) (cm (c) (cp d 3)))) (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (e))) (cm (cm (cz (2)) (c)) (cm (cp d 2) (k))))) (ca (ca (cm (cm (cz (4)) (c)) (cm (cp d 2) (i))) (cm (cm (cz (-4)) (c)) (cm (d) (cm (e) (i))))) (ca (cm (cm (cz (-2)) (c)) (cm (cp e 2) (k))) (cm (cz (4)) (cm (cp d 3) (f))))))) (ca (ca (ca (ca (cm (cz (2)) (cm (cp d 3) (g))) (cm (cz (4)) (cm (cp d 3) (j)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (e) (f))) (cm (cm (cz (2)) (cp d 2)) (cm (e) (g))))) (ca (ca (cm (cm (cz (4)) (cp d 2)) (cm (e) (j))) (cm (cm (cz (2)) (cp d 2)) (cm (f) (k)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (f) (i))) (cm (cm (cz (1)) (cp d 2)) (cm (g) (k)))))) (ca (ca (ca (cm (cm (cz (2)) (cp d 2)) (cm (g) (i))) (cm (cm (cz (2)) (cp d 2)) (cm (k) (j)))) (ca (cm (cm (cz (4)) (cp d 2)) (cm (i) (j))) (cm (cm (cz (-4)) (d)) (cm (e) (cm (f) (i)))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (e) (cm (g) (i)))) (cm (cm (cz (-4)) (d)) (cm (e) (cm (i) (j))))) (ca (cm (cm (cz (-2)) (cp e 2)) (cm (f) (k))) (ca (cm (cm (cz (-1)) (cp e 2)) (cm (g) (k))) (cm (cm (cz (-2)) (cp e 2)) (cm (k) (j))))))))),
    ca (ca (ca (ca (ca (cm (cz (1)) (cm (a) (cp b 2))) (ca (cm (cm (cz (4)) (a)) (cm (b) (d))) (cm (cm (cz (2)) (a)) (cm (b) (e))))) (ca (cm (cz (3)) (cm (a) (cp d 2))) (ca (cm (cm (cz (2)) (a)) (cm (d) (e))) (cm (cm (cz (2)) (a)) (cm (d) (k)))))) (ca (ca (cm (cm (cz (2)) (a)) (cm (d) (i))) (ca (cm (cz (-1)) (cm (a) (cp e 2))) (cm (cm (cz (-2)) (a)) (cm (e) (k))))) (ca (cm (cm (cz (-2)) (a)) (cm (e) (i))) (ca (cm (cz (2)) (cm (cp b 2) (c))) (cm (cz (2)) (cm (cp b 2) (f))))))) (ca (ca (ca (cm (cm (cz (6)) (b)) (cm (c) (d))) (ca (cm (cm (cz (4)) (b)) (cm (c) (e))) (cm (cm (cz (2)) (b)) (cm (c) (k))))) (ca (cm (cm (cz (6)) (b)) (cm (d) (f))) (ca (cm (cm (cz (2)) (b)) (cm (d) (g))) (cm (cm (cz (2)) (b)) (cm (d) (j)))))) (ca (ca (cm (cm (cz (4)) (b)) (cm (e) (f))) (ca (cm (cm (cz (-2)) (b)) (cm (g) (i))) (cm (cm (cz (-2)) (b)) (cm (i) (j))))) (ca (cm (cz (2)) (cm (c) (cp d 2))) (ca (cm (cm (cz (6)) (c)) (cm (d) (k))) (cm (cz (-2)) (cm (c) (cp e 2)))))))) (ca (ca (ca (ca (cm (cm (cz (-2)) (c)) (cm (e) (i))) (ca (cm (cz (2)) (cm (c) (cp k 2))) (cm (cm (cz (4)) (c)) (cm (k) (i))))) (ca (cm (cz (-2)) (cm (c) (cp i 2))) (ca (cm (cz (2)) (cm (cp d 2) (f))) (cm (cz (3)) (cm (cp d 2) (g)))))) (ca (ca (cm (cz (2)) (cm (cp d 2) (j))) (ca (cm (cm (cz (2)) (d)) (cm (e) (g))) (cm (cm (cz (2)) (d)) (cm (e) (j))))) (ca (cm (cm (cz (2)) (d)) (cm (f) (k))) (ca (cm (cm (cz (2)) (d)) (cm (f) (i))) (cm (cm (cz (4)) (d)) (cm (g) (k))))))) (ca (ca (ca (cm (cm (cz (2)) (d)) (cm (g) (i))) (ca (cm (cm (cz (6)) (d)) (cm (k) (j))) (cm (cz (-2)) (cm (cp e 2) (f))))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (k))) (ca (cm (cm (cz (-2)) (e)) (cm (f) (i))) (cm (cm (cz (-2)) (e)) (cm (g) (i)))))) (ca (ca (cm (cm (cz (-2)) (e)) (cm (i) (j))) (ca (cm (cz (1)) (cm (g) (cp k 2))) (cm (cm (cz (2)) (g)) (cm (k) (i))))) (ca (ca (cm (cz (-1)) (cm (g) (cp i 2))) (cm (cz (2)) (cm (cp k 2) (j)))) (ca (cm (cm (cz (4)) (k)) (cm (i) (j))) (cm (cz (-2)) (cm (cp i 2) (j)))))))),
    ca (ca (ca (ca (cm (cz (-2)) (cm (a) (b))) (cm (cz (-4)) (cm (a) (d)))) (ca (cm (cz (-4)) (cm (a) (e))) (cm (cz (-4)) (cm (b) (c))))) (ca (ca (cm (cz (-4)) (cm (b) (f))) (cm (cz (-4)) (cm (c) (d)))) (ca (cm (cz (-4)) (cm (c) (e))) (cm (cz (-4)) (cm (c) (k)))))) (ca (ca (ca (cm (cz (-4)) (cm (c) (i))) (cm (cz (-4)) (cm (d) (f)))) (ca (cm (cz (-4)) (cm (d) (g))) (cm (cz (-4)) (cm (d) (j))))) (ca (ca (cm (cz (-4)) (cm (e) (f))) (cm (cz (-2)) (cm (g) (k)))) (ca (cm (cz (-4)) (cm (g) (i))) (ca (cm (cz (-4)) (cm (k) (j))) (cm (cz (-4)) (cm (i) (j))))))),
    ca (ca (ca (cm (cz (-1)) (cm (cp b 2) (k))) (ca (cm (cz (-1)) (cm (b) (cp d 2))) (cm (cm (cz (-2)) (b)) (cm (d) (k))))) (ca (cm (cm (cz (-2)) (b)) (cm (e) (k))) (ca (cm (cz (-1)) (cm (b) (cp k 2))) (cm (cm (cz (-2)) (b)) (cm (k) (i)))))) (ca (ca (cm (cz (1)) (cm (b) (cp i 2))) (ca (cm (cz (-2)) (cp d 3)) (cm (cz (-2)) (cm (cp d 2) (e))))) (ca (ca (cm (cz (-1)) (cm (cp d 2) (k))) (cm (cz (-2)) (cm (cp d 2) (i)))) (ca (cm (cm (cz (2)) (d)) (cm (e) (i))) (cm (cz (1)) (cm (cp e 2) (k)))))),
    ca (ca (ca (cm (cz (-2)) (cp b 2)) (ca (cm (cz (-8)) (cm (b) (d))) (cm (cz (-4)) (cm (b) (e))))) (ca (cm (cz (-2)) (cm (b) (k))) (ca (cm (cz (-6)) (cp d 2)) (cm (cz (-4)) (cm (d) (e)))))) (ca (ca (cm (cz (-8)) (cm (d) (k))) (ca (cm (cz (-4)) (cm (d) (i))) (cm (cz (2)) (cp e 2)))) (ca (ca (cm (cz (4)) (cm (e) (i))) (cm (cz (-2)) (cp k 2))) (ca (cm (cz (-4)) (cm (k) (i))) (cm (cz (2)) (cp i 2)))))]

def polynomial (p : Fin 19 → ℂ) (x y z : ℂ) : ℂ :=
  ca (ca (ca (ca (cm (p 0) (cm (x) (cp y 3))) (cm (cm (p 1) (x)) (cm (cp y 2) (z)))) (ca (cm (p 2) (cm (x) (cp y 2))) (cm (cm (p 3) (x)) (cm (y) (cp z 2))))) (ca (ca (cm (cm (p 4) (x)) (cm (y) (z))) (cm (p 5) (cm (x) (y)))) (ca (cm (p 6) (cm (x) (cp z 3))) (ca (cm (p 7) (cm (x) (cp z 2))) (cm (p 8) (cm (x) (z))))))) (ca (ca (ca (cm (p 9) (cm (cp y 3) (z))) (cm (p 10) (cp y 3))) (ca (cm (p 11) (cm (cp y 2) (cp z 2))) (ca (cm (p 12) (cm (cp y 2) (z))) (cm (p 13) (cp y 2))))) (ca (ca (cm (p 14) (cm (y) (cp z 3))) (cm (p 15) (cm (y) (cp z 2)))) (ca (cm (p 16) (cm (y) (z))) (ca (cm (p 17) (cp z 3)) (cm (p 18) (cp z 2))))))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
lemma extract_coefficients (p : Fin 19 → ℂ)
    (hp : ∀ x y z, polynomial p x y z = 0) : ∀ n, p n = 0 := by
  have h0 := hp 0 0 1
  have h1 := hp 0 0 (-1)
  have h2 := hp 0 1 0
  have h3 := hp 0 1 1
  have h4 := hp 0 1 (-1)
  have h5 := hp 0 1 2
  have h6 := hp 0 (-1) 0
  have h7 := hp 0 (-1) 1
  have h8 := hp 0 (-1) (-1)
  have h9 := hp 0 2 1
  have h10 := hp 1 0 1
  have h11 := hp 1 0 (-1)
  have h12 := hp 1 0 2
  have h13 := hp 1 1 0
  have h14 := hp 1 1 1
  have h15 := hp 1 1 (-1)
  have h16 := hp 1 (-1) 0
  have h17 := hp 1 (-1) 1
  have h18 := hp 1 2 0
  simp only [polynomial, ca, cm, cp, cz] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  intro n
  fin_cases n
  · change p 0 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h6 + (-1 / 2 : ℂ) * h13 + (-1 / 6 : ℂ) * h16 + (1 / 6 : ℂ) * h18
  · change p 1 = 0
    linear_combination (1 : ℂ) * h0 + (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (1 / 2 : ℂ) * h6 + (-1 / 2 : ℂ) * h7 + (-1 : ℂ) * h10 + (-1 / 2 : ℂ) * h13 + (1 / 2 : ℂ) * h14 + (-1 / 2 : ℂ) * h16 + (1 / 2 : ℂ) * h17
  · change p 2 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h6 + (1 / 2 : ℂ) * h13 + (1 / 2 : ℂ) * h16
  · change p 3 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (-1 / 2 : ℂ) * h4 + (-1 / 2 : ℂ) * h10 + (-1 / 2 : ℂ) * h11 + (-1 : ℂ) * h13 + (1 / 2 : ℂ) * h14 + (1 / 2 : ℂ) * h15
  · change p 4 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h4 + (-1 / 2 : ℂ) * h6 + (1 / 2 : ℂ) * h7 + (1 / 2 : ℂ) * h10 + (1 / 2 : ℂ) * h11 + (1 / 2 : ℂ) * h13 + (-1 / 2 : ℂ) * h15 + (1 / 2 : ℂ) * h16 + (-1 / 2 : ℂ) * h17
  · change p 5 = 0
    linear_combination (1 : ℂ) * h13 + (-1 / 3 : ℂ) * h16 + (-1 / 6 : ℂ) * h18
  · change p 6 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h10 + (-1 / 6 : ℂ) * h11 + (1 / 6 : ℂ) * h12
  · change p 7 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h10 + (1 / 2 : ℂ) * h11
  · change p 8 = 0
    linear_combination (1 : ℂ) * h10 + (-1 / 3 : ℂ) * h11 + (-1 / 6 : ℂ) * h12
  · change p 9 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (1 / 2 : ℂ) * h6 + (-1 / 6 : ℂ) * h7 + (1 / 6 : ℂ) * h9
  · change p 10 = 0
    linear_combination (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h6
  · change p 11 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2 + (1 / 4 : ℂ) * h3 + (1 / 4 : ℂ) * h4 + (-1 / 2 : ℂ) * h6 + (1 / 4 : ℂ) * h7 + (1 / 4 : ℂ) * h8
  · change p 12 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 / 4 : ℂ) * h3 + (-1 / 4 : ℂ) * h4 + (1 / 4 : ℂ) * h7 + (-1 / 4 : ℂ) * h8
  · change p 13 = 0
    linear_combination (1 / 2 : ℂ) * h2 + (1 / 2 : ℂ) * h6
  · change p 14 = 0
    linear_combination (-1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2 + (-1 / 2 : ℂ) * h3 + (-1 / 6 : ℂ) * h4 + (1 / 6 : ℂ) * h5
  · change p 15 = 0
    linear_combination (-1 / 2 : ℂ) * h2 + (1 / 4 : ℂ) * h3 + (1 / 4 : ℂ) * h4 + (1 / 2 : ℂ) * h6 + (-1 / 4 : ℂ) * h7 + (-1 / 4 : ℂ) * h8
  · change p 16 = 0
    linear_combination (-1 / 2 : ℂ) * h1 + (5 / 4 : ℂ) * h3 + (-1 / 12 : ℂ) * h4 + (-1 / 6 : ℂ) * h5 + (-1 / 2 : ℂ) * h6 + (-1 / 12 : ℂ) * h7 + (1 / 4 : ℂ) * h8 + (-1 / 6 : ℂ) * h9
  · change p 17 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (-1 / 2 : ℂ) * h1
  · change p 18 = 0
    linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h1

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma permanent_expansion (a b c d e f g k i j rr x y z : ℂ) (hr : rr ^ 2 = 2) :
    Matrix.permanent (Matrix.of fun r s => (1 : ℂ) + model a b c d e f g k i j rr x y z r s) - 24 =
      polynomial (coefficients a b c d e f g k i j rr) x y z := by
  simp [perm4, Matrix.of_apply, model, polynomial, coefficients, ca, cm, cp, cz,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (norm := skip) (ca (ca (ca (cm (cm (cz (-1)) (a)) (cm (g) (cm (cp x 2) (cp y 2)))) (ca (cm (cm (cz (-1)) (cm (a) (k))) (cm (cp x 2) (cm (y) (z)))) (cm (cm (cz (-1)) (a)) (cm (cp x 2) (y))))) (ca (ca (cm (cm (cz (-1)) (cm (b) (g))) (cm (cp x 2) (cm (y) (z)))) (cm (cm (cz (-1)) (b)) (cm (k) (cm (cp x 2) (cp z 2))))) (ca (cm (cm (cz (-1)) (b)) (cm (cp x 2) (z))) (cm (cm (cz (-1)) (cp c 2)) (cm (cp x 2) (cp y 2)))))) (ca (ca (cm (cm (cz (-2)) (cm (c) (d))) (cm (cp x 2) (cm (y) (z)))) (ca (cm (cm (cz (-2)) (c)) (cm (cp x 2) (y))) (cm (cm (cz (-1)) (cp d 2)) (cm (cp x 2) (cp z 2))))) (ca (ca (cm (cm (cz (-2)) (d)) (cm (cp x 2) (z))) (cm (cm (cz (-1)) (g)) (cm (cp x 2) (y)))) (ca (cm (cm (cz (-1)) (k)) (cm (cp x 2) (z))) (cm (cz (-2)) (cp x 2)))))) * hr
  simp only [ca, cm, cp, cz]
  ring

lemma coefficients_zero (a b c d e f g k i j rr : ℂ) (hr : rr ^ 2 = 2)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +
      model a b c d e f g k i j rr x y z r s) = 24) : ∀ n, coefficients a b c d e f g k i j rr n = 0 := by
  apply extract_coefficients
  intro x y z
  rw [← permanent_expansion a b c d e f g k i j rr x y z hr, hp x y z]
  ring

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma same_matrix_obstruction (a b c d g k i j rr : ℂ) (hr : rr ^ 2 = 2)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +
      model a b c d 1 1 g k i j rr x y z r s) = 24) : False := by
  have hz := coefficients_zero a b c d 1 1 g k i j rr hr hp
  apply PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.normalized_same_obstruction a b c d g k i j rr
  · have h := hz 0
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 1
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 2
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 3
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 4
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · have h := hz 5
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · have h := hz 6
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 7
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 8
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · have h := hz 9
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 10
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 11
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 12
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 13
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · have h := hz 14
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 15
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 16
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · have h := hz 17
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 : ℂ) * h
  · have h := hz 18
    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at h
    simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination (1 / 2 : ℂ) * h
  · simp only [PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.ca, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cm, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cp, PEqualNP.Outside.L_gct_231_aux.DoubleSingleSameQuotientCertificate.cz]
    linear_combination hr

lemma model_rescale (a b c d e f g k i j rr sy sz x y z : ℂ) :
    model (a*sy) (b*sz) (c*sy) (d*sz) (e*sz) (f*sy)
      (g*sy) (k*sz) (i*sz) (j*sy) rr x y z =
    model a b c d e f g k i j rr x (sy*y) (sz*z) := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [model, ca, cm, cp, cz] <;> ring

lemma same_nonzero_matrix_obstruction (a b c d e f g k i j rr : ℂ)
    (hr : rr ^ 2 = 2) (he : e ≠ 0) (hf : f ≠ 0)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +
      model a b c d e f g k i j rr x y z r s) = 24) : False := by
  apply same_matrix_obstruction (a*f⁻¹) (b*e⁻¹) (c*f⁻¹) (d*e⁻¹)
    (g*f⁻¹) (k*e⁻¹) (i*e⁻¹) (j*f⁻¹) rr hr
  intro x y z
  have he1 : e * e⁻¹ = 1 := mul_inv_cancel₀ he
  have hf1 : f * f⁻¹ = 1 := mul_inv_cancel₀ hf
  have hm := model_rescale a b c d e f g k i j rr f⁻¹ e⁻¹ x y z
  rw [he1, hf1] at hm
  rw [hm]
  exact hp x (f⁻¹*y) (e⁻¹*z)

lemma sparse_cross_matrix_obstruction (a b c d g k rr : ℂ) (hr : rr^2=2)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model a b c d 0 1 g k 1 0 rr x y z r s)=24) : False := by
  have hz := coefficients_zero a b c d 0 1 g k 1 0 rr hr hp
  have h2 := hz 2
  have h4 := hz 4
  have h5 := hz 5
  have h7 := hz 7
  have h8 := hz 8
  clear hz hp
  simp [coefficients,ca,cm,cp,cz] at h2 h4 h5 h7 h8
  have hg : g=2*(rr+1)-a-2*c := by
    linear_combination (-(rr+1)/2)*h5-(a+2*c+g)*hr
  have hk : k= -2*(rr-1)-b-2*d := by
    linear_combination ((rr-1)/2)*h8-(b+2*d+k)*hr
  subst g
  subst k
  have impossible : (20:ℂ)=0 := by
    linear_combination h4-h2-h7-8*hr
  norm_num at impossible


lemma sparse_cross_nonzero_matrix_obstruction (a b c d f g k i rr : ℂ)
    (hr : rr^2=2) (hi : i≠0) (hf : f≠0)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model a b c d 0 f g k i 0 rr x y z r s)=24) : False := by
  apply sparse_cross_matrix_obstruction (a*f⁻¹) (b*i⁻¹) (c*f⁻¹) (d*i⁻¹)
    (g*f⁻¹) (k*i⁻¹) rr hr
  intro x y z
  have hi1 : i*i⁻¹=1 := mul_inv_cancel₀ hi
  have hf1 : f*f⁻¹=1 := mul_inv_cancel₀ hf
  have hm := model_rescale a b c d 0 f g k i 0 rr f⁻¹ i⁻¹ x y z
  simp only [zero_mul,hi1,hf1] at hm
  rw [hm]
  exact hp x (f⁻¹*y) (i⁻¹*z)

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge


namespace PEqualNP.Outside.L_gct_231_aux.DoubleSingleGeometry

open PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge

def base (h : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,0],![0,0,0,0],![0,0,h-1,1],![0,0,1,-h-1]]

def ModelImpossible : Prop := ∀ a b c d e f g k i j rr : ℂ,
  rr^2=2 → (f≠0 ∨ j≠0) → (e≠0 ∨ i≠0) →
  (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
    model a b c d e f g k i j rr x y z r s)=24) → False

def DisjointMaximal : Prop := ∀ A B C : Matrix (Fin 4) (Fin 4) ℂ,
  (∀ r s, A r s=A s r) → (∀ r s, B r s=B s r) → (∀ r s, C r s=C s r) →
  (∀ j, A 2 j=0) → (∀ j, A 3 j=0) → (∀ j, B 0 j=0) → (∀ j, B 1 j=0) →
  A≠0 → B≠0 →
  (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+x*A r s+y*B r s+z*C r s)=24) →
  ∃ p q : ℂ, C=Matrix.of fun r s => p*A r s+q*B r s

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma total_entries_zero (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hp : ∀ w, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+w*M r s)=24) :
    ∑ r, ∑ s, M r s=0 := by
  have h1 := hp 1
  have hn1 := hp (-1)
  have h2 := hp 2
  have hn2 := hp (-2)
  simp [perm4, Matrix.of_apply] at h1 hn1 h2 hn2
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero]
  linear_combination (1/9:ℂ)*h1-(1/9:ℂ)*hn1-(1/72:ℂ)*h2+(1/72:ℂ)*hn2

lemma normalized_block (a b c : ℂ) (hS : a+c+2*b=0) (hQ : a*c+b^2=0)
    (hne : a≠0 ∨ b≠0 ∨ c≠0) :
    b≠0 ∧ ∃ h : ℂ, h^2=2 ∧ a=b*(h-1) ∧ c=b*(-h-1) := by
  have hb : b≠0 := by
    intro hb
    have ha2 : a^2=0 := by linear_combination a*hS-hQ+(b-2*a)*hb
    have ha := eq_zero_of_pow_eq_zero ha2
    have hc : c=0 := by linear_combination hS-ha-2*hb
    exact hne.elim (fun hn => hn ha) (fun hn => hn.elim (fun hn => hn hb) (fun hn => hn hc))
  have hmul : (a/b)*b=a := div_mul_cancel₀ a hb
  have haq : a^2+2*a*b-b^2=0 := by linear_combination a*hS-hQ
  refine ⟨hb,a/b+1,?_,?_,?_⟩
  · apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination (a/b*b+a+2*b)*hmul+haq
  · linear_combination -hmul
  · linear_combination hS+hmul

lemma normalized_independent_impossible (hm : ModelImpossible) (hd : DisjointMaximal)
    (h : ℂ) (hh : h^2=2) (B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsB : ∀ r s, B r s=B s r) (hsC : ∀ r s, C r s=C s r)
    (hB2 : ∀ j, B 2 j=0) (hC3 : ∀ j, C 3 j=0)
    (hind : ∀ u v w : ℂ, (∀ r s, u*base h r s+v*B r s+w*C r s=0) →
      u=0 ∧ v=0 ∧ w=0)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+x*base h r s+y*B r s+z*C r s)=24) : False := by
  have hsumB : ∑ r, ∑ s, B r s=0 := by
    apply total_entries_zero
    intro w
    simpa only [zero_mul,add_zero,zero_add] using hp 0 w 0
  have hsumC : ∑ r, ∑ s, C r s=0 := by
    apply total_entries_zero
    intro w
    simpa only [zero_mul,add_zero,zero_add] using hp 0 0 w
  have hB33 : B 3 3= -B 0 0-B 1 1-2*B 0 1-2*B 0 3-2*B 1 3 := by
    simp [Fin.sum_univ_succ,hB2,hsB 0 2,hsB 1 2,hsB 3 2,hsB 1 0,hsB 3 0,hsB 3 1] at hsumB
    linear_combination hsumB
  have hC22 : C 2 2= -C 0 0-C 1 1-2*C 0 1-2*C 0 2-2*C 1 2 := by
    simp [Fin.sum_univ_succ,hC3,hsC 0 3,hsC 1 3,hsC 2 3,hsC 1 0,hsC 2 0,hsC 2 1] at hsumC
    linear_combination hsumC
  have heq (x y z : ℂ) :
      model (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
        (B 1 1) (C 1 1) (C 1 2) (B 1 3) h x y z =
      Matrix.of (fun r s => x*base h r s+y*B r s+z*C r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [model,base,ca,cm,cp,cz,Matrix.of_apply,hB2,hC3,
        hsB 0 2,hsB 1 2,hsB 3 2,hsB 1 0,hsB 3 0,hsB 3 1,
        hsC 0 3,hsC 1 3,hsC 2 3,hsC 1 0,hsC 2 0,hsC 2 1,hB33,hC22] <;> ring
  have hpmodel (x y z : ℂ) : Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
        (B 1 1) (C 1 1) (C 1 2) (B 1 3) h x y z r s)=24 := by
    rw [heq]
    simpa only [Matrix.of_apply,add_assoc] using hp x y z
  have hz := coefficients_zero (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
    (B 1 1) (C 1 1) (C 1 2) (B 1 3) h hh hpmodel
  have hsA (r s : Fin 4) : base h r s=base h s r := by
    fin_cases r <;> fin_cases s <;> simp [base]
  have hA0 (j : Fin 4) : base h 0 j=0 := by fin_cases j <;> simp [base]
  have hA1 (j : Fin 4) : base h 1 j=0 := by fin_cases j <;> simp [base]
  have hAne : base h≠0 := by
    intro he
    have ht := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 3) he
    norm_num [base] at ht
  have hBne : B≠0 := by
    intro he
    have hc := (hind 0 1 0 (by intro r s; simp [he])).2.1
    norm_num at hc
  have hCne : C≠0 := by
    intro he
    have hc := (hind 0 0 1 (by intro r s; simp [he])).2.2
    norm_num at hc
  have hcrossB : B 0 3≠0 ∨ B 1 3≠0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hb03,hb13⟩ := hn
    have hp5 := hz 5
    simp [coefficients,ca,cm,cp,cz,hb03,hb13] at hp5
    have hdiag : B 0 0+B 1 1+2*B 0 1=0 := by
      linear_combination (-(h+1)/2)*hp5-(B 0 0+B 1 1+2*B 0 1)*hh
    have hB3 (j : Fin 4) : B 3 j=0 := by
      fin_cases j <;> simp [hsB 3 0,hsB 3 1,hB2,hsB 3 2,hb03,hb13,hB33]
      linear_combination -hdiag
    obtain ⟨p,q,hC⟩ := hd B (base h) C hsB hsA hsC hB2 hB3 hA0 hA1 hBne hAne
      (by intro x y z; simpa only [add_assoc,add_left_comm,add_comm] using hp y x z)
    have hrel (r s : Fin 4) : (-q)*base h r s+(-p)*B r s+1*C r s=0 := by
      rw [hC]
      simp only [Matrix.of_apply]
      ring
    have hc := (hind (-q) (-p) 1 hrel).2.2
    norm_num at hc
  have hcrossC : C 0 2≠0 ∨ C 1 2≠0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hc02,hc12⟩ := hn
    have hp8 := hz 8
    simp [coefficients,ca,cm,cp,cz,hc02,hc12] at hp8
    have hdiag : C 0 0+C 1 1+2*C 0 1=0 := by
      linear_combination ((h-1)/2)*hp8-(C 0 0+C 1 1+2*C 0 1)*hh
    have hC2 (j : Fin 4) : C 2 j=0 := by
      fin_cases j <;> simp [hsC 2 0,hsC 2 1,hC3,hsC 2 3,hc02,hc12,hC22]
      linear_combination -hdiag
    obtain ⟨p,q,hB⟩ := hd C (base h) B hsC hsA hsB hC2 hC3 hA0 hA1 hCne hAne
      (by intro x y z; simpa only [add_assoc,add_left_comm,add_comm] using hp y z x)
    have hrel (r s : Fin 4) : (-q)*base h r s+1*B r s+(-p)*C r s=0 := by
      rw [hB]
      simp only [Matrix.of_apply]
      ring
    have hc := (hind (-q) 1 (-p) hrel).2.1
    norm_num at hc
  exact hm (B 0 0) (C 0 0) (B 0 1) (C 0 1) (C 0 2) (B 0 3)
    (B 1 1) (C 1 1) (C 1 2) (B 1 3) h hh hcrossB hcrossC hpmodel

lemma independent_coefficients (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hi : LinearIndependent ℂ ![A,B,C]) (u v w : ℂ)
    (hrel : ∀ r s, u*A r s+v*B r s+w*C r s=0) : u=0 ∧ v=0 ∧ w=0 := by
  have hz : ∑ n : Fin 3, (![u,v,w] : Fin 3 → ℂ) n • (![A,B,C] : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) n=0 := by
    ext r s
    simpa [Fin.sum_univ_succ,Matrix.smul_apply,add_assoc] using hrel r s
  have h := Fintype.linearIndependent_iff.mp hi (![u,v,w] : Fin 3 → ℂ) hz
  exact ⟨h 0,h 1,h 2⟩

def bottom (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,0],![0,0,0,0],![0,0,a,b],![0,0,b,c]]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
lemma repeated_rows_impossible (hm : ModelImpossible) (hd : DisjointMaximal)
    (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s, A r s=A s r) (hsB : ∀ r s, B r s=B s r)
    (hsC : ∀ r s, C r s=C s r)
    (hA0 : ∀ j, A 0 j=0) (hA1 : ∀ j, A 1 j=0)
    (hB2 : ∀ j, B 2 j=0) (hC3 : ∀ j, C 3 j=0)
    (hi : LinearIndependent ℂ ![A,B,C])
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+x*A r s+y*B r s+z*C r s)=24) : False := by
  have hc := independent_coefficients A B C hi
  have hAne : A≠0 := by
    intro ha
    have he := (hc 1 0 0 (by intro r s; simp [ha])).1
    norm_num at he
  have hAeq : A=bottom (A 2 2) (A 2 3) (A 3 3) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [bottom,hA0,hA1,hsA 2 0,hsA 2 1,hsA 3 0,hsA 3 1,hsA 3 2]
  have hnonzero : A 2 2≠0 ∨ A 2 3≠0 ∨ A 3 3≠0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨h22,h23,h33⟩ := hn
    apply hAne
    rw [hAeq,h22,h23,h33]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottom]
  have hplus := hp 1 0 0
  have hminus := hp (-1) 0 0
  rw [hAeq] at hplus hminus
  simp [perm4,Matrix.of_apply,bottom] at hplus hminus
  have hS : A 2 2+A 3 3+2*A 2 3=0 := by
    linear_combination (1/12:ℂ)*(hplus-hminus)
  have hQ : A 2 2*A 3 3+(A 2 3)^2=0 := by
    linear_combination (1/4:ℂ)*(hplus+hminus)
  obtain ⟨ha,h,hh,h22,h33⟩ := normalized_block (A 2 2) (A 2 3) (A 3 3) hS hQ hnonzero
  have hAscale : A=Matrix.of (fun r s => A 2 3*base h r s) := by
    apply hAeq.trans
    ext r s
    fin_cases r <;> fin_cases s <;> simp [bottom,base,Matrix.of_apply,h22,h33] <;> ring
  have hentry (r s : Fin 4) : A r s=A 2 3*base h r s :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M r s) hAscale
  apply normalized_independent_impossible hm hd h hh B C hsB hsC hB2 hC3
  · intro u v w hzero
    have hrel (r s : Fin 4) : (u/A 2 3)*A r s+v*B r s+w*C r s=0 := by
      rw [hentry r s]
      simpa only [←mul_assoc,div_mul_cancel₀ u ha] using hzero r s
    obtain ⟨hu,hv,hw⟩ := hc (u/A 2 3) v w hrel
    refine ⟨?_,hv,hw⟩
    exact (div_eq_zero_iff).mp hu |>.resolve_right ha
  · intro x y z
    convert hp (x/A 2 3) y z using 1
    congr 1
    ext r s
    simp only [Matrix.of_apply]
    rw [hentry r s]
    simp only [←mul_assoc,div_mul_cancel₀ x ha]

lemma model_swap_level (a b c d e f g k i j rr : ℂ)
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model a b c d e f g k i j rr x y z r s)=24) :
    ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
      model g k c d i j a b e f rr x y z r s)=24 := by
  intro x y z
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r s => (1:ℂ)+
    model a b c d e f g k i j rr x y z r s
  have heq : M.submatrix σ σ=Matrix.of (fun r s => (1:ℂ)+
      model g k c d i j a b e f rr x y z r s) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [M,σ,Matrix.submatrix_apply,Matrix.of_apply,Equiv.swap_apply_def,model,ca,cm,cp,cz] <;> ring
  have hinv : Matrix.permanent (M.submatrix σ σ)=Matrix.permanent M := by
    change Matrix.permanent ((M.submatrix σ id).submatrix id σ)=Matrix.permanent M
    rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]
  rw [←heq]
  exact hinv.trans (hp x y z)

lemma model_impossible_from_same_sparse
    (hsame : ∀ a b c d e f g k i j rr : ℂ, rr^2=2 → e≠0 → f≠0 →
      (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
        model a b c d e f g k i j rr x y z r s)=24) → False)
    (hsparse : ∀ a b c d f g k i rr : ℂ, rr^2=2 → i≠0 → f≠0 →
      (∀ x y z, Matrix.permanent (Matrix.of fun r s => (1:ℂ)+
        model a b c d 0 f g k i 0 rr x y z r s)=24) → False) : ModelImpossible := by
  intro a b c d e f g k i j rr hr hB hC hp
  have hswap := model_swap_level a b c d e f g k i j rr hp
  by_cases hf : f≠0
  · by_cases he : e≠0
    · exact hsame a b c d e f g k i j rr hr he hf hp
    · have he0 : e=0 := not_ne_iff.mp he
      have hi : i≠0 := hC.resolve_left he
      by_cases hj : j≠0
      · exact hsame g k c d i j a b e f rr hr hi hj hswap
      · have hj0 : j=0 := not_ne_iff.mp hj
        subst e
        subst j
        exact hsparse a b c d f g k i rr hr hi hf hp
  · have hf0 : f=0 := not_ne_iff.mp hf
    have hj : j≠0 := hB.resolve_left hf
    by_cases hi : i≠0
    · exact hsame g k c d i j a b e f rr hr hi hj hswap
    · have hi0 : i=0 := not_ne_iff.mp hi
      have he : e≠0 := hC.resolve_right hi
      subst f
      subst i
      exact hsparse g k c d j a b e rr hr he hj hswap

lemma actual_repeated_matrix_obstruction (A B C : Matrix (Fin 4) (Fin 4) ℂ)
    (hsA : ∀ r s, A r s=A s r) (hsB : ∀ r s, B r s=B s r)
    (hsC : ∀ r s, C r s=C s r)
    (hA0 : ∀ j, A 0 j=0) (hA1 : ∀ j, A 1 j=0)
    (hB2 : ∀ j, B 2 j=0) (hC3 : ∀ j, C 3 j=0)
    (hi : LinearIndependent ℂ ![A,B,C])
    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s =>
      (1:ℂ)+x*A r s+y*B r s+z*C r s)=24) : False := by
  exact repeated_rows_impossible
    (model_impossible_from_same_sparse same_nonzero_matrix_obstruction sparse_cross_nonzero_matrix_obstruction)
    PEqualNP.Outside.L_gct_231.TwoBlock.MatrixBridge.two_double_kernel_rows_maximal
    A B C hsA hsB hsC hA0 hA1 hB2 hC3 hi hp

end PEqualNP.Outside.L_gct_231_aux.DoubleSingleGeometry
