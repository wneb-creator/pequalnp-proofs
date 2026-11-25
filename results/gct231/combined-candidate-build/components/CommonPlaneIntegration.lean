import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.LinearAlgebra.Matrix.Polynomial

namespace PEqualNP.Outside.L_gct_231_aux

open Matrix

theorem block_zero_det_square {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) :
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).det = B.det ^ 2 := by
  have hs : Equiv.Perm.sign (Equiv.sumComm (Fin 2) (Fin 2)) = 1 := by decide
  have hm :
      (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D).submatrix
          (Equiv.sumComm (Fin 2) (Fin 2)) id =
        Matrix.fromBlocks Bᵀ D (0 : Matrix (Fin 2) (Fin 2) R) B := by
    ext i j
    cases i <;> cases j <;> rfl
  have hd := Matrix.det_permute (Equiv.sumComm (Fin 2) (Fin 2))
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D)
  simpa [hm, hs, Matrix.det_fromBlocks_zero₂₁, pow_two] using hd.symm

theorem block_zero_det_congruence {R : Type*} [CommRing R]
    (M P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (B D : Matrix (Fin 2) (Fin 2) R)
    (h : Pᵀ * M * P = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R) B Bᵀ D) :
    P.det ^ 2 * M.det = B.det ^ 2 := by
  simpa [Matrix.det_mul, block_zero_det_square, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using congrArg Matrix.det h

open Polynomial

theorem polynomial_det_square_of_constant_congruence
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X])
    (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (B D : Matrix (Fin 2) (Fin 2) ℂ[X]) (hp : P.det ≠ 0)
    (h : (P.map C)ᵀ * M * P.map C =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ[X]) B Bᵀ D) :
    ∃ p : ℂ[X], M.det = p ^ 2 := by
  have hd : (P.map C).det = C P.det := (C.map_det P).symm
  have hs := block_zero_det_congruence M (P.map C) B D h
  rw [hd] at hs
  have hi : C (P.det)⁻¹ * C P.det = (1 : ℂ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hp, map_one]
  refine ⟨C (P.det)⁻¹ * B.det, ?_⟩
  calc
    M.det = (C (P.det)⁻¹ * C P.det) ^ 2 * M.det := by rw [hi]; simp
    _ = C (P.det)⁻¹ ^ 2 * (C P.det ^ 2 * M.det) := by ring
    _ = (C (P.det)⁻¹ * B.det) ^ 2 := by rw [hs]; ring

theorem symmetric_zero_block {R : Type*} [CommRing R]
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (hm : M.IsSymm)
    (hz : ∀ i j : Fin 2, M (Sum.inl i) (Sum.inl j) = 0) :
    M = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) R)
      (fun i j => M (Sum.inl i) (Sum.inr j))
      (fun i j => M (Sum.inl i) (Sum.inr j))ᵀ
      (fun i j => M (Sum.inr i) (Sum.inr j)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact hz i j
  · rfl
  · exact (hm.apply (Sum.inr i) (Sum.inl j)).symm
  · rfl

theorem symmetric_congruence {R : Type*} [CommRing R]
    {n : Type*} [Fintype n]
    (M P : Matrix n n R) (hm : M.IsSymm) : (Pᵀ * M * P).IsSymm := by
  simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hm.eq,
    Matrix.mul_assoc]

theorem determinant_pencil_square_of_adapted
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (hm0 : ∀ i j : Fin 2, (Pᵀ * M * P) (Sum.inl i) (Sum.inl j) = 0)
    (hn0 : ∀ i j : Fin 2, (Pᵀ * N * P) (Sum.inl i) (Sum.inl j) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  let L : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ[X] :=
    N.map C - (X : ℂ[X]) • M.map C
  have hi : (P.map C)ᵀ * L * P.map C =
      (Pᵀ * N * P).map C - (X : ℂ[X]) • (Pᵀ * M * P).map C := by
    simp only [L, Matrix.map_mul, Matrix.transpose_map, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j : Fin 2, ((P.map C)ᵀ * L * P.map C) (Sum.inl i) (Sum.inl j) = 0 := by
    intro i j
    rw [hi]
    change C ((Pᵀ * N * P) (Sum.inl i) (Sum.inl j)) -
      X * C ((Pᵀ * M * P) (Sum.inl i) (Sum.inl j)) = 0
    rw [hn0, hm0, map_zero, mul_zero, sub_zero]
  have hl : L.IsSymm := (hn.map C).sub ((hm.map C).smul X)
  exact polynomial_det_square_of_constant_congruence L P _ _ hp
    (symmetric_zero_block _ (symmetric_congruence L (P.map C) hl) hz)

theorem symmetric_quadratic_vanishing_polarizes
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) (hm : M.IsSymm)
    (W : Submodule ℂ (n → ℂ))
    (h : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0) :
    ∀ u ∈ W, ∀ v ∈ W, dotProduct u (M.mulVec v) = 0 := by
  intro u hu v hv
  have hz := h (u + v) (W.add_mem hu hv)
  have hu0 := h u hu
  have hv0 := h v hv
  have hc := hm.dotProduct_mulVec_comm (x := u) (y := v)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hu0, hv0,
    zero_add, add_zero] at hz
  rw [← hc] at hz
  linear_combination (1 / 2 : ℂ) * hz

theorem congruence_entry_is_pairing {R : Type*} [CommSemiring R]
    {n : Type*} [Fintype n] (M P : Matrix n n R) (i j : n) :
    (Pᵀ * M * P) i j = dotProduct (fun k => P k i) (M.mulVec (fun k => P k j)) := by
  rw [Matrix.mul_assoc]
  rfl

theorem determinant_pencil_square_of_isotropic_columns
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ))
    (hmem : ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W)
    (hM : ∀ u ∈ W, ∀ v ∈ W, dotProduct u (M.mulVec v) = 0)
    (hN : ∀ u ∈ W, ∀ v ∈ W, dotProduct u (N.mulVec v) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  apply determinant_pencil_square_of_adapted M N P hm hn hp
  · intro i j
    rw [congruence_entry_is_pairing]
    exact hM _ (hmem i) _ (hmem j)
  · intro i j
    rw [congruence_entry_is_pairing]
    exact hN _ (hmem i) _ (hmem j)

theorem determinant_pencil_square_of_quadratic_columns
    (M N P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm) (hp : P.det ≠ 0)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ))
    (hmem : ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  exact determinant_pencil_square_of_isotropic_columns M N P hm hn hp W hmem
    (symmetric_quadratic_vanishing_polarizes M hm W hM)
    (symmetric_quadratic_vanishing_polarizes N hn W hN)


abbrev Index4 := Fin 2 ⊕ Fin 2

theorem exists_adapted_basis
    (W : Submodule ℂ (Index4 → ℂ)) (hdim : Module.finrank ℂ W = 2) :
    ∃ b : Module.Basis Index4 ℂ (Index4 → ℂ),
      ∀ j : Fin 2, b (Sum.inl j) ∈ W := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl W
  have htotal : Module.finrank ℂ (Index4 → ℂ) = 4 := by
    simp [Index4, Module.finrank_fintype_fun_eq_card]
  have hdimU : Module.finrank ℂ U = 2 := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hU
    rw [hdim, htotal] at hadd
    exact Nat.add_left_cancel (show 2 + Module.finrank ℂ U = 2 + 2 from hadd)
  let bW : Module.Basis (Fin 2) ℂ W := Module.finBasisOfFinrankEq ℂ W hdim
  let bU : Module.Basis (Fin 2) ℂ U := Module.finBasisOfFinrankEq ℂ U hdimU
  refine ⟨(bW.prod bU).map (W.prodEquivOfIsCompl U hU), ?_⟩
  intro j
  simp only [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl',
    Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
    ZeroMemClass.coe_zero, add_zero]
  exact (bW j).property

theorem exists_adapted_matrix
    (W : Submodule ℂ (Index4 → ℂ)) (hdim : Module.finrank ℂ W = 2) :
    ∃ P : Matrix Index4 Index4 ℂ,
      P.det ≠ 0 ∧ ∀ j : Fin 2, (fun i => P i (Sum.inl j)) ∈ W := by
  classical
  obtain ⟨b, hb⟩ := exists_adapted_basis W hdim
  let P : Matrix Index4 Index4 ℂ := fun i j => b j i
  refine ⟨P, ?_, ?_⟩
  · apply Matrix.nonsingular_iff_det_ne_zero.mp
    apply Matrix.Nonsingular.of_linearIndependent_col
    change LinearIndependent ℂ (fun j => b j)
    exact b.linearIndependent
  · exact hb


theorem determinant_pencil_square_of_common_isotropic_plane
    (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ)) (hdim : Module.finrank ℂ W = 2)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    ∃ p : ℂ[X], Matrix.det (fun i j => C (N i j) - X * C (M i j)) = p ^ 2 := by
  obtain ⟨P, hp, hmem⟩ := exists_adapted_matrix W hdim
  exact determinant_pencil_square_of_quadratic_columns M N P hm hn hp W hmem hM hN


open Polynomial

theorem quartic_square_coefficient_identities {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q p : R[X]) (hdeg : q.natDegree ≤ 4) (hsq : q = p ^ 2) :
    8 * q.coeff 4 ^ 2 * q.coeff 1 -
        4 * q.coeff 4 * q.coeff 3 * q.coeff 2 + q.coeff 3 ^ 3 = 0 ∧
      (4 * q.coeff 4 * q.coeff 2 - q.coeff 3 ^ 2) ^ 2 -
        64 * q.coeff 4 ^ 3 * q.coeff 0 = 0 := by
  have hroot : p.natDegree ≤ 2 := by
    rw [hsq, Polynomial.natDegree_pow] at hdeg
    omega
  have hp3 : p.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hp4 : p.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h4 : q.coeff 4 = p.coeff 2 ^ 2 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3, hp4]
  have h3 : q.coeff 3 = 2 * p.coeff 2 * p.coeff 1 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hp3]
    ring
  have h2 : q.coeff 2 = p.coeff 1 ^ 2 + 2 * p.coeff 2 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h1 : q.coeff 1 = 2 * p.coeff 1 * p.coeff 0 := by
    simp [hsq, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    ring
  have h0 : q.coeff 0 = p.coeff 0 ^ 2 := by simp [hsq, pow_two]
  constructor
  · rw [h4, h3, h2, h1]
    ring
  · rw [h4, h3, h2, h0]
    ring

theorem common_isotropic_plane_coefficient_identities
    (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (hm : M.IsSymm) (hn : N.IsSymm)
    (W : Submodule ℂ ((Fin 2 ⊕ Fin 2) → ℂ)) (hdim : Module.finrank ℂ W = 2)
    (hM : ∀ u ∈ W, dotProduct u (M.mulVec u) = 0)
    (hN : ∀ u ∈ W, dotProduct u (N.mulVec u) = 0) :
    let q : ℂ[X] := Matrix.det (fun i j => C (N i j) - X * C (M i j))
    8 * q.coeff 4 ^ 2 * q.coeff 1 -
        4 * q.coeff 4 * q.coeff 3 * q.coeff 2 + q.coeff 3 ^ 3 = 0 ∧
      (4 * q.coeff 4 * q.coeff 2 - q.coeff 3 ^ 2) ^ 2 -
        64 * q.coeff 4 ^ 3 * q.coeff 0 = 0 := by
  let q : ℂ[X] := Matrix.det (fun i j => C (N i j) - X * C (M i j))
  obtain ⟨p, hp⟩ := determinant_pencil_square_of_common_isotropic_plane M N hm hn W hdim hM hN
  have hdeg : q.natDegree ≤ 4 := by
    have h := Polynomial.natDegree_det_X_add_C_le (-M) N
    have heq : (X : ℂ[X]) • (-M).map C + N.map C =
        (fun i j => C (N i j) - X * C (M i j)) := by
      apply Matrix.ext
      intro i j
      change X * C (-(M i j)) + C (N i j) = C (N i j) - X * C (M i j)
      rw [map_neg]
      ring
    rw [heq] at h
    simpa [q] using h
  exact quartic_square_coefficient_identities q p hdeg hp

end PEqualNP.Outside.L_gct_231_aux
