import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

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

end PEqualNP.Outside.L_gct_231_aux.C4Coordinates

