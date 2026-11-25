import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace PEqualNP.Outside.L_gct_231_aux.C4Coordinates

lemma sum_perm_succ {n : ℕ} {R : Type*} [CommRing R] (f : Equiv.Perm (Fin (n + 1)) → R) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4 {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring

def scaledMatrix {R : Type*} [CommRing R] (e f a b H X Y : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![2*H+2*b-4*e, 2*e+2*f+2*X-a-b, 0, 2*e-2*f-2*Y-b+a;
     2*e+2*f+2*X-a-b, -2*H+2*a-4*e, 2*e-2*f+2*Y+b-a, 0;
     0, 2*e-2*f+2*Y+b-a, 2*H-2*b-4*e, 2*e+2*f-2*X+a+b;
     2*e-2*f-2*Y-b+a, 0, 2*e+2*f-2*X+a+b, -2*H-2*a-4*e]

def quadratic {R : Type*} [CommRing R] (e f a b H X Y : R) : R :=
  6*e^2+2*f^2+a^2+b^2-H^2-X^2-Y^2-X*(a+b)+Y*(b-a)

def cubic {R : Type*} [CommRing R] (e f a b H X Y : R) : R :=
  2*f*a*b-2*H*X*Y +
    e*(-4*X^2-4*Y^2+4*X*(a+b)+4*Y*(a-b)-a^2-b^2+4*f^2)-4*e^3

lemma scaledMatrix_symmetric {R : Type*} [CommRing R] (e f a b H X Y : R) :
    ∀ i j, scaledMatrix e f a b H X Y i j = scaledMatrix e f a b H X Y j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma scaledMatrix_tangent {R : Type*} [CommRing R] (e f a b H X Y : R) :
    (∑ i : Fin 4, ∑ j : Fin 4, scaledMatrix e f a b H X Y i j) = 0 := by
  simp [scaledMatrix, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma scaled_permanent_expansion {R : Type*} [CommRing R]
    (e f a b H X Y z : R) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * scaledMatrix e f a b H X Y i j) =
      24 + (16 * quadratic e f a b H X Y) * z^2 +
        (32 * cubic e f a b H X Y) * z^3 +
        Matrix.permanent (scaledMatrix e f a b H X Y) * z^4 := by
  rw [perm4 (Matrix.of fun (i j : Fin 4) => 1 + z * scaledMatrix e f a b H X Y i j),
    perm4 (scaledMatrix e f a b H X Y)]
  simp +decide [scaledMatrix, Matrix.of_apply, quadratic, cubic]
  ring



open Polynomial

lemma quartic_expansion_coeff_two_three
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) :
    p.coeff 2 = q ∧ p.coeff 3 = c := by
  rw [h]
  constructor <;> simp

lemma quartic_coeffs_zero_of_eval_constant
    (p : ℂ[X]) (q c r : ℂ)
    (h : p = C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4)
    (heval : ∀ z : ℂ, p.eval z = 24) :
    q = 0 ∧ c = 0 := by
  have hp : p = C 24 := by
    apply Polynomial.funext
    intro z
    simpa only [eval_C] using heval z
  obtain ⟨h2, h3⟩ := quartic_expansion_coeff_two_three p q c r h
  constructor
  · rw [← h2, hp]
    simp
  · rw [← h3, hp]
    simp

lemma quartic_coeffs_zero_of_pointwise
    (q c r : ℂ)
    (h : ∀ z : ℂ, 24 + q * z ^ 2 + c * z ^ 3 + r * z ^ 4 = 24) :
    q = 0 ∧ c = 0 := by
  apply quartic_coeffs_zero_of_eval_constant
    (C 24 + C q * X ^ 2 + C c * X ^ 3 + C r * X ^ 4) q c r rfl
  intro z
  simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X] using h z

noncomputable def matrix (e f a b H X Y : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 : ℂ) / 8) • scaledMatrix e f a b H X Y

lemma matrix_symmetric (e f a b H X Y : ℂ) :
    ∀ i j, matrix e f a b H X Y i j = matrix e f a b H X Y j i := by
  intro i j
  change (1 / 8 : ℂ) * scaledMatrix e f a b H X Y i j =
    (1 / 8 : ℂ) * scaledMatrix e f a b H X Y j i
  rw [scaledMatrix_symmetric e f a b H X Y i j]

lemma matrix_tangent (e f a b H X Y : ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4, matrix e f a b H X Y i j) = 0 := by
  simp only [matrix, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [scaledMatrix_tangent, mul_zero]

lemma permanent_expansion (e f a b H X Y z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) =
      24 + (quadratic e f a b H X Y / 4) * z^2 +
        (cubic e f a b H X Y / 16) * z^3 +
        Matrix.permanent (matrix e f a b H X Y) * z^4 := by
  have hm : (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) =
      (Matrix.of fun (i j : Fin 4) => 1 + (z / 8) * scaledMatrix e f a b H X Y i j) := by
    ext i j
    simp only [matrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, scaled_permanent_expansion, matrix, Matrix.permanent_smul]
  simp only [Fintype.card_fin]
  ring

noncomputable def linePolynomial (M : Matrix (Fin 4) (Fin 4) ℂ) : ℂ[X] :=
  Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + Polynomial.X * C (M i j))

lemma linePolynomial_eval (M : Matrix (Fin 4) (Fin 4) ℂ) (z : ℂ) :
    (linePolynomial M).eval z =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1 + z * M i j) := by
  simp only [linePolynomial, Matrix.permanent, Matrix.of_apply, eval_finsetSum,
    eval_prod, eval_add, eval_one, eval_mul, eval_X, eval_C]

lemma linePolynomial_expansion (e f a b H X Y : ℂ) :
    linePolynomial (matrix e f a b H X Y) =
      C 24 + C (quadratic e f a b H X Y / 4) * Polynomial.X^2 +
        C (cubic e f a b H X Y / 16) * Polynomial.X^3 +
        C (Matrix.permanent (matrix e f a b H X Y)) * Polynomial.X^4 := by
  apply Polynomial.funext
  intro z
  rw [linePolynomial_eval]
  simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X] using
    permanent_expansion e f a b H X Y z

theorem coefficient_formulas (e f a b H X Y : ℂ) :
    (linePolynomial (matrix e f a b H X Y)).coeff 2 = quadratic e f a b H X Y / 4 ∧
    (linePolynomial (matrix e f a b H X Y)).coeff 3 = cubic e f a b H X Y / 16 := by
  exact quartic_expansion_coeff_two_three _ _ _ _ (linePolynomial_expansion e f a b H X Y)

theorem quadratic_cubic_zero_of_constant_line (e f a b H X Y : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * matrix e f a b H X Y i j) = 24) :
    quadratic e f a b H X Y = 0 ∧ cubic e f a b H X Y = 0 := by
  have hzero := quartic_coeffs_zero_of_pointwise
    (quadratic e f a b H X Y / 4) (cubic e f a b H X Y / 16)
    (Matrix.permanent (matrix e f a b H X Y))
    (fun z => (permanent_expansion e f a b H X Y z).symm.trans (h z))
  constructor
  · linear_combination (4 : ℂ) * hzero.1
  · linear_combination (16 : ℂ) * hzero.2

lemma cubic_at_e_zero (f a b H X Y : ℂ) :
    cubic 0 f a b H X Y = 2 * (f*a*b-H*X*Y) := by
  unfold cubic
  ring

theorem product_identity_of_constant_line (f a b H X Y : ℂ)
    (h : ∀ z : ℂ, Matrix.permanent
      (Matrix.of fun (i j : Fin 4) => 1 + z * matrix 0 f a b H X Y i j) = 24) :
    f*a*b = H*X*Y := by
  have hc := (quadratic_cubic_zero_of_constant_line 0 f a b H X Y h).2
  rw [cubic_at_e_zero] at hc
  linear_combination (1 / 2 : ℂ) * hc


-- Append inside namespace PEqualNP.Outside.L_gct_231_aux.C4Coordinates.
-- Requires the existing scaledMatrix and the Matrix.IsSymm API.

lemma scaledMatrix_reconstruct_entries
    (d0 d1 d2 d3 p s q r : ℂ)
    (ht : d0 + d1 + d2 + d3 + 2 * (p + r + q + s) = 0) :
    ((1 : ℂ) / 8) • scaledMatrix
      (p + r + q + s) (p + r - q - s)
      (2 * (d1 - d3)) (2 * (d0 - d2))
      (2 * (d0 + d2 + (p + r + q + s)))
      (2 * (p - r) + (2 * (d1 - d3) + 2 * (d0 - d2)) / 2)
      (2 * (q - s) - (2 * (d0 - d2) - 2 * (d1 - d3)) / 2) =
      !![d0, p, 0, s; p, d1, q, 0; 0, q, d2, r; s, 0, r, d3] := by
  have hd3 : d3 = -d0 - d1 - d2 - 2 * (p + r + q + s) := by
    linear_combination ht
  rw [hd3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledMatrix, Matrix.smul_apply, smul_eq_mul] <;> ring

lemma scaledMatrix_reconstruct_supported
    (M : Matrix (Fin 4) (Fin 4) ℂ) (hsym : M.IsSymm)
    (h02 : M 0 2 = 0) (h13 : M 1 3 = 0)
    (htangent : (∑ i : Fin 4, ∑ j : Fin 4, M i j) = 0) :
    let e := M 0 1 + M 2 3 + M 1 2 + M 0 3
    let f := M 0 1 + M 2 3 - M 1 2 - M 0 3
    let a := 2 * (M 1 1 - M 3 3)
    let b := 2 * (M 0 0 - M 2 2)
    let H := 2 * (M 0 0 + M 2 2 + e)
    let X := 2 * (M 0 1 - M 2 3) + (a + b) / 2
    let Y := 2 * (M 1 2 - M 0 3) - (b - a) / 2
    ((1 : ℂ) / 8) • scaledMatrix e f a b H X Y = M := by
  have h10 : M 1 0 = M 0 1 := hsym.apply 0 1
  have h20 : M 2 0 = 0 := (hsym.apply 0 2).trans h02
  have h30 : M 3 0 = M 0 3 := hsym.apply 0 3
  have h21 : M 2 1 = M 1 2 := hsym.apply 1 2
  have h31 : M 3 1 = 0 := (hsym.apply 1 3).trans h13
  have h32 : M 3 2 = M 2 3 := hsym.apply 2 3
  have ht : M 0 0 + M 1 1 + M 2 2 + M 3 3 +
      2 * (M 0 1 + M 2 3 + M 1 2 + M 0 3) = 0 := by
    have h := htangent
    simp [Fin.sum_univ_succ, h10, h20, h30, h21, h31, h32, h02, h13] at h
    linear_combination h
  dsimp only
  rw [scaledMatrix_reconstruct_entries
    (M 0 0) (M 1 1) (M 2 2) (M 3 3) (M 0 1) (M 0 3) (M 1 2) (M 2 3) ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h10, h20, h30, h21, h31, h32, h02, h13]

end PEqualNP.Outside.L_gct_231_aux.C4Coordinates
