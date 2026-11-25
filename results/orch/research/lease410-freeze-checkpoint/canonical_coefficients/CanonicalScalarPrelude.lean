import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.L_gct_231

lemma permanent_four {R : Type*} [CommSemiring R] (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.permanent M =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 +
      M 0 0 * M 1 1 * M 3 2 * M 2 3 +
      M 0 0 * M 2 1 * M 1 2 * M 3 3 +
      M 0 0 * M 2 1 * M 3 2 * M 1 3 +
      M 0 0 * M 3 1 * M 1 2 * M 2 3 +
      M 0 0 * M 3 1 * M 2 2 * M 1 3 +
      M 1 0 * M 0 1 * M 2 2 * M 3 3 +
      M 1 0 * M 0 1 * M 3 2 * M 2 3 +
      M 1 0 * M 2 1 * M 0 2 * M 3 3 +
      M 1 0 * M 2 1 * M 3 2 * M 0 3 +
      M 1 0 * M 3 1 * M 0 2 * M 2 3 +
      M 1 0 * M 3 1 * M 2 2 * M 0 3 +
      M 2 0 * M 0 1 * M 1 2 * M 3 3 +
      M 2 0 * M 0 1 * M 3 2 * M 1 3 +
      M 2 0 * M 1 1 * M 0 2 * M 3 3 +
      M 2 0 * M 1 1 * M 3 2 * M 0 3 +
      M 2 0 * M 3 1 * M 0 2 * M 1 3 +
      M 2 0 * M 3 1 * M 1 2 * M 0 3 +
      M 3 0 * M 0 1 * M 1 2 * M 2 3 +
      M 3 0 * M 0 1 * M 2 2 * M 1 3 +
      M 3 0 * M 1 1 * M 0 2 * M 2 3 +
      M 3 0 * M 1 1 * M 2 2 * M 0 3 +
      M 3 0 * M 2 1 * M 0 2 * M 1 3 +
      M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  classical
  unfold Matrix.permanent
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 4))) =
      permsOfFinset (Finset.univ : Finset (Fin 4)) := by
    ext p
    simp [mem_perms_of_finset_iff]
  rw [hu]
  change ((permsOfList ([0, 1, 2, 3] : List (Fin 4))).map
    (fun p => ∏ i : Fin 4, M (p i) i)).sum = _
  simp [permsOfList, Fin.prod_univ_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  ring

lemma quartic_first_coefficients (a b c d : ℂ)
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

lemma quartic_all_coefficients (a b c d : ℂ)
    (h : ∀ z : ℂ, a*z+b*z^2+c*z^3+d*z^4 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨ha,hb⟩ := quartic_first_coefficients a b c d h
  have h1 := h 1
  have hn := h (-1)
  refine ⟨ha,hb,?_,?_⟩
  · linear_combination (1/2:ℂ)*h1-(1/2:ℂ)*hn-ha
  · linear_combination (1/2:ℂ)*h1+(1/2:ℂ)*hn-hb

def hadamardSigns : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

noncomputable def hadamardTransform :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun V p := (∑ i : Fin 4, ∑ j : Fin 4,
    hadamardSigns p.1 i * V (i,j) * hadamardSigns p.2 j) / 4
  map_add' V W := by
    funext p
    simp [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib,add_div]
  map_smul' z V := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp [hadamardSigns,Fin.sum_univ_succ]
    ring

noncomputable def hadamardCoordinateMatrix (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => (!![0,(P 0-D 0)/2,(P 1-D 1)/2,(P 2-D 2)/2;
    (P 0-D 0)/2,B 0,(3*D 2-P 2)/2,(3*D 1-P 1)/2;
    (P 1-D 1)/2,(3*D 2-P 2)/2,B 1,(3*D 0-P 0)/2;
    (P 2-D 2)/2,(3*D 1-P 1)/2,(3*D 0-P 0)/2,B 2] : Matrix (Fin 4) (Fin 4) ℂ) p.1 p.2

noncomputable def hadamardReconstruct (B P D : Fin 3 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  hadamardTransform (hadamardCoordinateMatrix B P D)

def canonicalHadamardQuadratic (B P D : Fin 3 → ℂ) : ℂ :=
  (B 0)^2 + (B 1)^2 + (B 2)^2 - (P 0)^2 - (P 1)^2 - (P 2)^2 + 3*(D 0)^2 + 3*(D 1)^2 + 3*(D 2)^2

def canonicalHadamardCubic (B P D : Fin 3 → ℂ) : ℂ :=
  2*(B 0)*(B 1)*(B 2) + (B 0)*(P 0)^2 - 4*(B 0)*(P 0)*(D 0) + (B 0)*(P 1)^2 - 4*(B 0)*(P 1)*(D 1)
    + (B 0)*(P 2)^2 - 4*(B 0)*(P 2)*(D 2) + 5*(B 0)*(D 0)^2 + 3*(B 0)*(D 1)^2 + 3*(B 0)*(D 2)^2
    + (B 1)*(P 0)^2 - 4*(B 1)*(P 0)*(D 0) + (B 1)*(P 1)^2 - 4*(B 1)*(P 1)*(D 1) + (B 1)*(P 2)^2
    - 4*(B 1)*(P 2)*(D 2) + 3*(B 1)*(D 0)^2 + 5*(B 1)*(D 1)^2 + 3*(B 1)*(D 2)^2 + (B 2)*(P 0)^2
    - 4*(B 2)*(P 0)*(D 0) + (B 2)*(P 1)^2 - 4*(B 2)*(P 1)*(D 1) + (B 2)*(P 2)^2 - 4*(B 2)*(P 2)*(D 2)
    + 3*(B 2)*(D 0)^2 + 3*(B 2)*(D 1)^2 + 5*(B 2)*(D 2)^2 - 2*(P 0)*(P 1)*(P 2) + 6*(P 0)*(P 1)*(D 2)
    + 6*(P 0)*(P 2)*(D 1) - 14*(P 0)*(D 1)*(D 2) + 6*(P 1)*(P 2)*(D 0) - 14*(P 1)*(D 0)*(D 2)
    - 14*(P 2)*(D 0)*(D 1) + 30*(D 0)*(D 1)*(D 2)

def canonicalHadamardQuartic (B P D : Fin 3 → ℂ) : ℂ :=
  3*(B 0)^4 + 2*(B 0)^2*(B 1)^2 + 2*(B 0)^2*(B 2)^2 - 2*(B 0)^2*(P 0)^2 - 2*(B 0)^2*(P 1)^2
    + 16*(B 0)^2*(P 1)*(D 1) - 2*(B 0)^2*(P 2)^2 + 16*(B 0)^2*(P 2)*(D 2) + 6*(B 0)^2*(D 0)^2
    - 26*(B 0)^2*(D 1)^2 - 26*(B 0)^2*(D 2)^2 + 4*(B 0)*(B 1)*(P 0)^2 - 16*(B 0)*(B 1)*(P 0)*(D 0)
    + 4*(B 0)*(B 1)*(P 1)^2 - 16*(B 0)*(B 1)*(P 1)*(D 1) + 4*(B 0)*(B 1)*(P 2)^2
    - 16*(B 0)*(B 1)*(P 2)*(D 2) + 12*(B 0)*(B 1)*(D 0)^2 + 12*(B 0)*(B 1)*(D 1)^2
    + 20*(B 0)*(B 1)*(D 2)^2 + 4*(B 0)*(B 2)*(P 0)^2 - 16*(B 0)*(B 2)*(P 0)*(D 0) + 4*(B 0)*(B 2)*(P 1)^2
    - 16*(B 0)*(B 2)*(P 1)*(D 1) + 4*(B 0)*(B 2)*(P 2)^2 - 16*(B 0)*(B 2)*(P 2)*(D 2)
    + 12*(B 0)*(B 2)*(D 0)^2 + 20*(B 0)*(B 2)*(D 1)^2 + 12*(B 0)*(B 2)*(D 2)^2
    - 8*(B 0)*(P 0)*(P 1)*(P 2) + 8*(B 0)*(P 0)*(P 1)*(D 2) + 8*(B 0)*(P 0)*(P 2)*(D 1)
    + 8*(B 0)*(P 0)*(D 1)*(D 2) + 24*(B 0)*(P 1)*(P 2)*(D 0) - 40*(B 0)*(P 1)*(D 0)*(D 2)
    - 40*(B 0)*(P 2)*(D 0)*(D 1) + 56*(B 0)*(D 0)*(D 1)*(D 2) + 3*(B 1)^4 + 2*(B 1)^2*(B 2)^2
    - 2*(B 1)^2*(P 0)^2 + 16*(B 1)^2*(P 0)*(D 0) - 2*(B 1)^2*(P 1)^2 - 2*(B 1)^2*(P 2)^2
    + 16*(B 1)^2*(P 2)*(D 2) - 26*(B 1)^2*(D 0)^2 + 6*(B 1)^2*(D 1)^2 - 26*(B 1)^2*(D 2)^2
    + 4*(B 1)*(B 2)*(P 0)^2 - 16*(B 1)*(B 2)*(P 0)*(D 0) + 4*(B 1)*(B 2)*(P 1)^2
    - 16*(B 1)*(B 2)*(P 1)*(D 1) + 4*(B 1)*(B 2)*(P 2)^2 - 16*(B 1)*(B 2)*(P 2)*(D 2)
    + 20*(B 1)*(B 2)*(D 0)^2 + 12*(B 1)*(B 2)*(D 1)^2 + 12*(B 1)*(B 2)*(D 2)^2
    - 8*(B 1)*(P 0)*(P 1)*(P 2) + 8*(B 1)*(P 0)*(P 1)*(D 2) + 24*(B 1)*(P 0)*(P 2)*(D 1)
    - 40*(B 1)*(P 0)*(D 1)*(D 2) + 8*(B 1)*(P 1)*(P 2)*(D 0) + 8*(B 1)*(P 1)*(D 0)*(D 2)
    - 40*(B 1)*(P 2)*(D 0)*(D 1) + 56*(B 1)*(D 0)*(D 1)*(D 2) + 3*(B 2)^4 - 2*(B 2)^2*(P 0)^2
    + 16*(B 2)^2*(P 0)*(D 0) - 2*(B 2)^2*(P 1)^2 + 16*(B 2)^2*(P 1)*(D 1) - 2*(B 2)^2*(P 2)^2
    - 26*(B 2)^2*(D 0)^2 - 26*(B 2)^2*(D 1)^2 + 6*(B 2)^2*(D 2)^2 - 8*(B 2)*(P 0)*(P 1)*(P 2)
    + 24*(B 2)*(P 0)*(P 1)*(D 2) + 8*(B 2)*(P 0)*(P 2)*(D 1) - 40*(B 2)*(P 0)*(D 1)*(D 2)
    + 8*(B 2)*(P 1)*(P 2)*(D 0) - 40*(B 2)*(P 1)*(D 0)*(D 2) + 8*(B 2)*(P 2)*(D 0)*(D 1)
    + 56*(B 2)*(D 0)*(D 1)*(D 2) + 2*(P 0)^4 - 16*(P 0)^3*(D 0) + 4*(P 0)^2*(P 1)^2
    - 16*(P 0)^2*(P 1)*(D 1) + 4*(P 0)^2*(P 2)^2 - 16*(P 0)^2*(P 2)*(D 2) + 52*(P 0)^2*(D 0)^2
    + 12*(P 0)^2*(D 1)^2 + 12*(P 0)^2*(D 2)^2 - 16*(P 0)*(P 1)^2*(D 0) + 64*(P 0)*(P 1)*(D 0)*(D 1)
    - 16*(P 0)*(P 2)^2*(D 0) + 64*(P 0)*(P 2)*(D 0)*(D 2) - 80*(P 0)*(D 0)^3 - 48*(P 0)*(D 0)*(D 1)^2
    - 48*(P 0)*(D 0)*(D 2)^2 + 2*(P 1)^4 - 16*(P 1)^3*(D 1) + 4*(P 1)^2*(P 2)^2 - 16*(P 1)^2*(P 2)*(D 2)
    + 12*(P 1)^2*(D 0)^2 + 52*(P 1)^2*(D 1)^2 + 12*(P 1)^2*(D 2)^2 - 16*(P 1)*(P 2)^2*(D 1)
    + 64*(P 1)*(P 2)*(D 1)*(D 2) - 48*(P 1)*(D 0)^2*(D 1) - 80*(P 1)*(D 1)^3 - 48*(P 1)*(D 1)*(D 2)^2
    + 2*(P 2)^4 - 16*(P 2)^3*(D 2) + 12*(P 2)^2*(D 0)^2 + 12*(P 2)^2*(D 1)^2 + 52*(P 2)^2*(D 2)^2
    - 48*(P 2)*(D 0)^2*(D 2) - 48*(P 2)*(D 1)^2*(D 2) - 80*(P 2)*(D 2)^3 + 50*(D 0)^4
    + 28*(D 0)^2*(D 1)^2 + 28*(D 0)^2*(D 2)^2 + 50*(D 1)^4 + 28*(D 1)^2*(D 2)^2 + 50*(D 2)^4

noncomputable def canonicalHadamardMatrix (B P D : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(B 0+B 1+B 2+2*D 0+2*D 1+2*D 2)/4,(B 0-B 1-B 2+2*P 0-4*D 0)/4,(-B 0+B 1-B 2+2*P 1-4*D 1)/4,(-B 0-B 1+B 2+2*P 2-4*D 2)/4;
    (B 0-B 1-B 2+2*P 0-4*D 0)/4,(B 0+B 1+B 2+2*D 0-2*D 1-2*D 2)/4,(-B 0-B 1+B 2-2*P 2+4*D 2)/4,(-B 0+B 1-B 2-2*P 1+4*D 1)/4;
    (-B 0+B 1-B 2+2*P 1-4*D 1)/4,(-B 0-B 1+B 2-2*P 2+4*D 2)/4,(B 0+B 1+B 2-2*D 0+2*D 1-2*D 2)/4,(B 0-B 1-B 2-2*P 0+4*D 0)/4;
    (-B 0-B 1+B 2+2*P 2-4*D 2)/4,(-B 0+B 1-B 2-2*P 1+4*D 1)/4,(B 0-B 1-B 2-2*P 0+4*D 0)/4,(B 0+B 1+B 2-2*D 0-2*D 1+2*D 2)/4]

lemma canonical_reconstruct_entry (B P D : Fin 3 → ℂ) (i j : Fin 4) :
    hadamardReconstruct B P D (i,j)=canonicalHadamardMatrix B P D i j := by
  fin_cases i <;> fin_cases j <;>
    simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
      hadamardSigns,Fin.sum_univ_succ,canonicalHadamardMatrix] <;> ring

set_option maxHeartbeats 2400000 in
lemma canonical_hadamard_radial_permanent (B P D : Fin 3 → ℂ) (z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j)) =
      24+canonicalHadamardQuadratic B P D*z^2+
        canonicalHadamardCubic B P D/2*z^3+canonicalHadamardQuartic B P D/32*z^4 := by
  simp_rw [canonical_reconstruct_entry]
  rw [permanent_four]
  simp [canonicalHadamardMatrix,canonicalHadamardQuadratic,
    canonicalHadamardCubic,canonicalHadamardQuartic]
  ring

lemma canonical_hadamard_homogeneous_zero (B P D : Fin 3 → ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j))=24) :
    canonicalHadamardQuadratic B P D=0 ∧ canonicalHadamardCubic B P D=0 ∧
      canonicalHadamardQuartic B P D=0 := by
  have hh : ∀ z : ℂ, (0:ℂ)*z+canonicalHadamardQuadratic B P D*z^2+
      (canonicalHadamardCubic B P D/2)*z^3+
      (canonicalHadamardQuartic B P D/32)*z^4=0 := by
    intro z
    have h := hp z
    rw [canonical_hadamard_radial_permanent] at h
    linear_combination h
  obtain ⟨_,h2,h3,h4⟩ := quartic_all_coefficients _ _ _ _ hh
  refine ⟨h2,?_,?_⟩
  · linear_combination 2*h3
  · linear_combination 32*h4

def canonicalCoefficientCoordinates (v : Fin 9 → ℂ) (s t u : ℂ) : Fin 3 → ℂ :=
  ![v 0*s+v 1*t+v 2*u,v 3*s+v 4*t+v 5*u,v 6*s+v 7*t+v 8*u]

lemma canonicalCoefficientCoordinates_scale (v : Fin 9 → ℂ) (s t u z : ℂ) :
    canonicalCoefficientCoordinates v (z*s) (z*t) (z*u)=
      z • canonicalCoefficientCoordinates v s t u := by
  funext i
  fin_cases i <;> simp [canonicalCoefficientCoordinates] <;> ring

lemma canonical_family_homogeneous_zero (p b : Fin 9 → ℂ)
    (hp : ∀ s t u : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24) :
    ∀ s t u : ℂ,
      canonicalHadamardQuadratic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardCubic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardQuartic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 := by
  intro s t u
  apply canonical_hadamard_homogeneous_zero
  intro z
  have h := hp (z*s) (z*t) (z*u)
  rw [canonicalCoefficientCoordinates_scale,canonicalCoefficientCoordinates_scale] at h
  have hd : (![z*s,z*t,z*u] : Fin 3 → ℂ)=z • ![s,t,u] := by
    funext i
    fin_cases i <;> simp
  rw [hd] at h
  exact h

end PEqualNP.Outside.L_gct_231
