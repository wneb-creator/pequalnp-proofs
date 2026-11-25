import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

noncomputable def starAffine (a b c : ℂ) : MvPolynomial (Fin 3) ℂ :=
  1 + MvPolynomial.C a * MvPolynomial.X 0 +
    MvPolynomial.C b * MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 2

lemma sum_perm_succ_poly {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → (MvPolynomial (Fin 3) ℂ)) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

lemma perm4_poly (M : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ)) : Matrix.permanent M =
    M 0 0 * M 1 1 * M 2 2 * M 3 3 + M 0 0 * M 1 1 * M 3 2 * M 2 3 + M 0 0 * M 2 1 * M 1 2 * M 3 3
  + M 0 0 * M 2 1 * M 3 2 * M 1 3 + M 0 0 * M 3 1 * M 1 2 * M 2 3 + M 0 0 * M 3 1 * M 2 2 * M 1 3
  + M 1 0 * M 0 1 * M 2 2 * M 3 3 + M 1 0 * M 0 1 * M 3 2 * M 2 3 + M 1 0 * M 2 1 * M 0 2 * M 3 3
  + M 1 0 * M 2 1 * M 3 2 * M 0 3 + M 1 0 * M 3 1 * M 0 2 * M 2 3 + M 1 0 * M 3 1 * M 2 2 * M 0 3
  + M 2 0 * M 0 1 * M 1 2 * M 3 3 + M 2 0 * M 0 1 * M 3 2 * M 1 3 + M 2 0 * M 1 1 * M 0 2 * M 3 3
  + M 2 0 * M 1 1 * M 3 2 * M 0 3 + M 2 0 * M 3 1 * M 0 2 * M 1 3 + M 2 0 * M 3 1 * M 1 2 * M 0 3
  + M 3 0 * M 0 1 * M 1 2 * M 2 3 + M 3 0 * M 0 1 * M 2 2 * M 1 3 + M 3 0 * M 1 1 * M 0 2 * M 2 3
  + M 3 0 * M 1 1 * M 2 2 * M 0 3 + M 3 0 * M 2 1 * M 0 2 * M 1 3 + M 3 0 * M 2 1 * M 1 2 * M 0 3 := by
  simp only [Matrix.permanent]
  rw [sum_perm_succ_poly]
  simp only [sum_perm_succ_poly (n := 2), sum_perm_succ_poly (n := 1), sum_perm_succ_poly (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring


noncomputable def fullStarMatrix (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  !![starAffine d0 d1 d2, starAffine 1 0 0, starAffine 0 1 0, starAffine 0 0 1;
    starAffine 1 0 0, starAffine d3 d4 d5, starAffine o0 o1 o2, starAffine o3 o4 o5;
    starAffine 0 1 0, starAffine o0 o1 o2, starAffine d6 d7 d8, starAffine o6 o7 o8;
    starAffine 0 0 1, starAffine o3 o4 o5, starAffine o6 o7 o8, starAffine (-(d0+d3+d6+2*(1+o0+o3+o6)))
      (-(d1+d4+d7+2*(1+o1+o4+o7)))
      (-(d2+d5+d8+2*(1+o2+o5+o8)))]

noncomputable def certD400 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p))))

theorem certD400_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD400 (p+q) = certD400 p + certD400 q := by simp [certD400]

theorem certD400_nat (n : ℕ) : certD400 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD400]

set_option maxHeartbeats 1000000 in
theorem certD400_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD400 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a0*b0*c0*d0) := by
  simp [certD400, starAffine] <;> ring

noncomputable def certD310 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))))

theorem certD310_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD310 (p+q) = certD310 p + certD310 q := by simp [certD310]

theorem certD310_nat (n : ℕ) : certD310 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD310]

set_option maxHeartbeats 1000000 in
theorem certD310_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD310 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b0*c0*d1 + a0*b0*c1*d0 + a0*b1*c0*d0 + a1*b0*c0*d0) := by
  simp [certD310, starAffine] <;> ring

noncomputable def certD301 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p))))

theorem certD301_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD301 (p+q) = certD301 p + certD301 q := by simp [certD301]

theorem certD301_nat (n : ℕ) : certD301 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD301]

set_option maxHeartbeats 1000000 in
theorem certD301_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD301 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b0*c0*d2 + a0*b0*c2*d0 + a0*b2*c0*d0 + a2*b0*c0*d0) := by
  simp [certD301, starAffine] <;> ring

noncomputable def certD300 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p)))

theorem certD300_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD300 (p+q) = certD300 p + certD300 q := by simp [certD300]

theorem certD300_nat (n : ℕ) : certD300 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD300]

set_option maxHeartbeats 1000000 in
theorem certD300_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD300 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b0*c0*d0 + a0*c0*d0 + a0*b0*d0 + a0*b0*c0) := by
  simp [certD300, starAffine] <;> ring

noncomputable def certD220 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD220_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD220 (p+q) = certD220 p + certD220 q := by simp [certD220]

theorem certD220_nat (n : ℕ) : certD220 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD220]

set_option maxHeartbeats 1000000 in
theorem certD220_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD220 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a0*b0*c1*d1 + a0*b1*c0*d1 + a0*b1*c1*d0 + a1*b0*c0*d1 + a1*b0*c1*d0 + a1*b1*c0*d0) := by
  simp [certD220, starAffine] <;> ring

noncomputable def certD211 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD211_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD211 (p+q) = certD211 p + certD211 q := by simp [certD211]

theorem certD211_nat (n : ℕ) : certD211 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD211]

set_option maxHeartbeats 1000000 in
theorem certD211_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD211 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b0*c1*d2 + a0*b0*c2*d1 + a0*b1*c0*d2 + a0*b1*c2*d0 + a0*b2*c0*d1 + a0*b2*c1*d0 + a1*b0*c0*d2 + a1*b0*c2*d0 + a1*b2*c0*d0 + a2*b0*c0*d1 + a2*b0*c1*d0 + a2*b1*c0*d0) := by
  simp [certD211, starAffine] <;> ring

noncomputable def certD210 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p)))

theorem certD210_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD210 (p+q) = certD210 p + certD210 q := by simp [certD210]

theorem certD210_nat (n : ℕ) : certD210 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD210]

set_option maxHeartbeats 1000000 in
theorem certD210_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD210 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c0*d1 + b0*c1*d0 + b1*c0*d0 + a0*c0*d1 + a0*c1*d0 + a0*b0*d1 + a0*b0*c1 + a0*b1*d0 + a0*b1*c0 + a1*c0*d0 + a1*b0*d0 + a1*b0*c0) := by
  simp [certD210, starAffine] <;> ring

noncomputable def certD202 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD202_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD202 (p+q) = certD202 p + certD202 q := by simp [certD202]

theorem certD202_nat (n : ℕ) : certD202 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD202]

set_option maxHeartbeats 1000000 in
theorem certD202_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD202 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a0*b0*c2*d2 + a0*b2*c0*d2 + a0*b2*c2*d0 + a2*b0*c0*d2 + a2*b0*c2*d0 + a2*b2*c0*d0) := by
  simp [certD202, starAffine] <;> ring

noncomputable def certD201 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p)))

theorem certD201_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD201 (p+q) = certD201 p + certD201 q := by simp [certD201]

theorem certD201_nat (n : ℕ) : certD201 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD201]

set_option maxHeartbeats 1000000 in
theorem certD201_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD201 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c0*d2 + b0*c2*d0 + b2*c0*d0 + a0*c0*d2 + a0*c2*d0 + a0*b0*d2 + a0*b0*c2 + a0*b2*d0 + a0*b2*c0 + a2*c0*d0 + a2*b0*d0 + a2*b0*c0) := by
  simp [certD201, starAffine] <;> ring

noncomputable def certD200 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p))

theorem certD200_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD200 (p+q) = certD200 p + certD200 q := by simp [certD200]

theorem certD200_nat (n : ℕ) : certD200 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD200]

set_option maxHeartbeats 1000000 in
theorem certD200_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD200 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c0*d0 + b0*d0 + b0*c0 + a0*d0 + a0*c0 + a0*b0) := by
  simp [certD200, starAffine] <;> ring

noncomputable def certD130 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD130_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD130 (p+q) = certD130 p + certD130 q := by simp [certD130]

theorem certD130_nat (n : ℕ) : certD130 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD130]

set_option maxHeartbeats 1000000 in
theorem certD130_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD130 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b1*c1*d1 + a1*b0*c1*d1 + a1*b1*c0*d1 + a1*b1*c1*d0) := by
  simp [certD130, starAffine] <;> ring

noncomputable def certD121 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD121_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD121 (p+q) = certD121 p + certD121 q := by simp [certD121]

theorem certD121_nat (n : ℕ) : certD121 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD121]

set_option maxHeartbeats 1000000 in
theorem certD121_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD121 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b1*c1*d2 + a0*b1*c2*d1 + a0*b2*c1*d1 + a1*b0*c1*d2 + a1*b0*c2*d1 + a1*b1*c0*d2 + a1*b1*c2*d0 + a1*b2*c0*d1 + a1*b2*c1*d0 + a2*b0*c1*d1 + a2*b1*c0*d1 + a2*b1*c1*d0) := by
  simp [certD121, starAffine] <;> ring

noncomputable def certD120 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)))

theorem certD120_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD120 (p+q) = certD120 p + certD120 q := by simp [certD120]

theorem certD120_nat (n : ℕ) : certD120 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD120]

set_option maxHeartbeats 1000000 in
theorem certD120_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD120 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c1*d1 + b1*c0*d1 + b1*c1*d0 + a0*c1*d1 + a0*b1*d1 + a0*b1*c1 + a1*c0*d1 + a1*c1*d0 + a1*b0*d1 + a1*b0*c1 + a1*b1*d0 + a1*b1*c0) := by
  simp [certD120, starAffine] <;> ring

noncomputable def certD112 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD112_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD112 (p+q) = certD112 p + certD112 q := by simp [certD112]

theorem certD112_nat (n : ℕ) : certD112 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD112]

set_option maxHeartbeats 1000000 in
theorem certD112_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD112 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (a0*b1*c2*d2 + a0*b2*c1*d2 + a0*b2*c2*d1 + a1*b0*c2*d2 + a1*b2*c0*d2 + a1*b2*c2*d0 + a2*b0*c1*d2 + a2*b0*c2*d1 + a2*b1*c0*d2 + a2*b1*c2*d0 + a2*b2*c0*d1 + a2*b2*c1*d0) := by
  simp [certD112, starAffine] <;> ring

noncomputable def certD111 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))

theorem certD111_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD111 (p+q) = certD111 p + certD111 q := by simp [certD111]

theorem certD111_nat (n : ℕ) : certD111 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD111]

set_option maxHeartbeats 1000000 in
theorem certD111_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD111 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (b0*c1*d2 + b0*c2*d1 + b1*c0*d2 + b1*c2*d0 + b2*c0*d1 + b2*c1*d0 + a0*c1*d2 + a0*c2*d1 + a0*b1*d2 + a0*b1*c2 + a0*b2*d1 + a0*b2*c1 + a1*c0*d2 + a1*c2*d0 + a1*b0*d2 + a1*b0*c2 + a1*b2*d0 + a1*b2*c0 + a2*c0*d1 + a2*c1*d0 + a2*b0*d1 + a2*b0*c1 + a2*b1*d0 + a2*b1*c0) := by
  simp [certD111, starAffine] <;> ring

noncomputable def certD110 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))

theorem certD110_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD110 (p+q) = certD110 p + certD110 q := by simp [certD110]

theorem certD110_nat (n : ℕ) : certD110 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD110]

set_option maxHeartbeats 1000000 in
theorem certD110_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD110 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c0*d1 + c1*d0 + b0*d1 + b0*c1 + b1*d0 + b1*c0 + a0*d1 + a0*c1 + a0*b1 + a1*d0 + a1*c0 + a1*b0) := by
  simp [certD110, starAffine] <;> ring

noncomputable def certD103 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD103_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD103 (p+q) = certD103 p + certD103 q := by simp [certD103]

theorem certD103_nat (n : ℕ) : certD103 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD103]

set_option maxHeartbeats 1000000 in
theorem certD103_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD103 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a0*b2*c2*d2 + a2*b0*c2*d2 + a2*b2*c0*d2 + a2*b2*c2*d0) := by
  simp [certD103, starAffine] <;> ring

noncomputable def certD102 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD102_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD102 (p+q) = certD102 p + certD102 q := by simp [certD102]

theorem certD102_nat (n : ℕ) : certD102 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD102]

set_option maxHeartbeats 1000000 in
theorem certD102_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD102 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b0*c2*d2 + b2*c0*d2 + b2*c2*d0 + a0*c2*d2 + a0*b2*d2 + a0*b2*c2 + a2*c0*d2 + a2*c2*d0 + a2*b0*d2 + a2*b0*c2 + a2*b2*d0 + a2*b2*c0) := by
  simp [certD102, starAffine] <;> ring

noncomputable def certD101 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p))

theorem certD101_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD101 (p+q) = certD101 p + certD101 q := by simp [certD101]

theorem certD101_nat (n : ℕ) : certD101 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD101]

set_option maxHeartbeats 1000000 in
theorem certD101_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD101 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c0*d2 + c2*d0 + b0*d2 + b0*c2 + b2*d0 + b2*c0 + a0*d2 + a0*c2 + a0*b2 + a2*d0 + a2*c0 + a2*b0) := by
  simp [certD101, starAffine] <;> ring

noncomputable def certD040 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))))

theorem certD040_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD040 (p+q) = certD040 p + certD040 q := by simp [certD040]

theorem certD040_nat (n : ℕ) : certD040 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD040]

set_option maxHeartbeats 1000000 in
theorem certD040_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD040 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a1*b1*c1*d1) := by
  simp [certD040, starAffine] <;> ring

noncomputable def certD031 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))))

theorem certD031_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD031 (p+q) = certD031 p + certD031 q := by simp [certD031]

theorem certD031_nat (n : ℕ) : certD031 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD031]

set_option maxHeartbeats 1000000 in
theorem certD031_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD031 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a1*b1*c1*d2 + a1*b1*c2*d1 + a1*b2*c1*d1 + a2*b1*c1*d1) := by
  simp [certD031, starAffine] <;> ring

noncomputable def certD030 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)))

theorem certD030_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD030 (p+q) = certD030 p + certD030 q := by simp [certD030]

theorem certD030_nat (n : ℕ) : certD030 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD030]

set_option maxHeartbeats 1000000 in
theorem certD030_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD030 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b1*c1*d1 + a1*c1*d1 + a1*b1*d1 + a1*b1*c1) := by
  simp [certD030, starAffine] <;> ring

noncomputable def certD022 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD022_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD022 (p+q) = certD022 p + certD022 q := by simp [certD022]

theorem certD022_nat (n : ℕ) : certD022 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD022]

set_option maxHeartbeats 1000000 in
theorem certD022_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD022 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      4 * (a1*b1*c2*d2 + a1*b2*c1*d2 + a1*b2*c2*d1 + a2*b1*c1*d2 + a2*b1*c2*d1 + a2*b2*c1*d1) := by
  simp [certD022, starAffine] <;> ring

noncomputable def certD021 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))

theorem certD021_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD021 (p+q) = certD021 p + certD021 q := by simp [certD021]

theorem certD021_nat (n : ℕ) : certD021 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD021]

set_option maxHeartbeats 1000000 in
theorem certD021_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD021 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b1*c1*d2 + b1*c2*d1 + b2*c1*d1 + a1*c1*d2 + a1*c2*d1 + a1*b1*d2 + a1*b1*c2 + a1*b2*d1 + a1*b2*c1 + a2*c1*d1 + a2*b1*d1 + a2*b1*c1) := by
  simp [certD021, starAffine] <;> ring

noncomputable def certD020 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))

theorem certD020_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD020 (p+q) = certD020 p + certD020 q := by simp [certD020]

theorem certD020_nat (n : ℕ) : certD020 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD020]

set_option maxHeartbeats 1000000 in
theorem certD020_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD020 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c1*d1 + b1*d1 + b1*c1 + a1*d1 + a1*c1 + a1*b1) := by
  simp [certD020, starAffine] <;> ring

noncomputable def certD013 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD013_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD013 (p+q) = certD013 p + certD013 q := by simp [certD013]

theorem certD013_nat (n : ℕ) : certD013 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD013]

set_option maxHeartbeats 1000000 in
theorem certD013_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD013 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (a1*b2*c2*d2 + a2*b1*c2*d2 + a2*b2*c1*d2 + a2*b2*c2*d1) := by
  simp [certD013, starAffine] <;> ring

noncomputable def certD012 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD012_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD012 (p+q) = certD012 p + certD012 q := by simp [certD012]

theorem certD012_nat (n : ℕ) : certD012 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD012]

set_option maxHeartbeats 1000000 in
theorem certD012_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD012 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (b1*c2*d2 + b2*c1*d2 + b2*c2*d1 + a1*c2*d2 + a1*b2*d2 + a1*b2*c2 + a2*c1*d2 + a2*c2*d1 + a2*b1*d2 + a2*b1*c2 + a2*b2*d1 + a2*b2*c1) := by
  simp [certD012, starAffine] <;> ring

noncomputable def certD011 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))

theorem certD011_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD011 (p+q) = certD011 p + certD011 q := by simp [certD011]

theorem certD011_nat (n : ℕ) : certD011 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD011]

set_option maxHeartbeats 1000000 in
theorem certD011_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD011 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      1 * (c1*d2 + c2*d1 + b1*d2 + b1*c2 + b2*d1 + b2*c1 + a1*d2 + a1*c2 + a1*b2 + a2*d1 + a2*c1 + a2*b1) := by
  simp [certD011, starAffine] <;> ring

noncomputable def certD004 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))))

theorem certD004_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD004 (p+q) = certD004 p + certD004 q := by simp [certD004]

theorem certD004_nat (n : ℕ) : certD004 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD004]

set_option maxHeartbeats 1000000 in
theorem certD004_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD004 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      24 * (a2*b2*c2*d2) := by
  simp [certD004, starAffine] <;> ring

noncomputable def certD003 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)))

theorem certD003_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD003 (p+q) = certD003 p + certD003 q := by simp [certD003]

theorem certD003_nat (n : ℕ) : certD003 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD003]

set_option maxHeartbeats 1000000 in
theorem certD003_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD003 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      6 * (b2*c2*d2 + a2*c2*d2 + a2*b2*d2 + a2*b2*c2) := by
  simp [certD003, starAffine] <;> ring

noncomputable def certD002 (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.constantCoeff (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))

theorem certD002_add (p q : MvPolynomial (Fin 3) ℂ) :
    certD002 (p+q) = certD002 p + certD002 q := by simp [certD002]

theorem certD002_nat (n : ℕ) : certD002 (n : MvPolynomial (Fin 3) ℂ) = 0 := by
  simp [certD002]

set_option maxHeartbeats 1000000 in
theorem certD002_four (a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 : ℂ) :
    certD002 (starAffine a0 a1 a2 * starAffine b0 b1 b2 *
      starAffine c0 c1 c2 * starAffine d0 d1 d2) =
      2 * (c2*d2 + b2*d2 + b2*c2 + a2*d2 + a2*c2 + a2*b2) := by
  simp [certD002, starAffine] <;> ring

set_option maxHeartbeats 20000000 in
theorem full_star_primitive_equations (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ)
    (h : Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8) =
      (24 : MvPolynomial (Fin 3) ℂ)) :
    (-d0^2*d3*d6 - d0^2*o0^2 - d0*d3^2*d6 - d0*d3*d6^2 - 2*d0*d3*d6*o0 - 2*d0*d3*d6*o3 - 2*d0*d3*d6*o6 - 2*d0*d3*d6 - d0*d3*o0^2 + d0*d3*o6^2 - d0*d6*o0^2 + d0*d6*o3^2 - d0*d6 - 2*d0*o0^3 - 2*d0*o0^2*o3 - 2*d0*o0^2*o6 - 2*d0*o0^2 + 2*d0*o0*o3*o6 - d3*d6 - d6^2 - 2*d6*o0 - 2*d6*o3 - 2*d6*o6 - 2*d6 + o6^2) = 0 ∧
    (-d0^2*d3*d7 - d0^2*d4*d6 - 2*d0^2*o0*o1 - 2*d0*d1*d3*d6 - 2*d0*d1*o0^2 - d0*d3^2*d7 - 2*d0*d3*d4*d6 - 2*d0*d3*d6*d7 - 2*d0*d3*d6*o1 - 2*d0*d3*d6*o4 - 2*d0*d3*d6*o7 - 2*d0*d3*d6 - 2*d0*d3*d7*o0 - 2*d0*d3*d7*o3 - 2*d0*d3*d7*o6 - 2*d0*d3*d7 - 2*d0*d3*o0*o1 + 2*d0*d3*o6*o7 - d0*d4*d6^2 - 2*d0*d4*d6*o0 - 2*d0*d4*d6*o3 - 2*d0*d4*d6*o6 - 2*d0*d4*d6 - d0*d4*o0^2 + d0*d4*o6^2 - 2*d0*d6*o0*o1 + 2*d0*d6*o3*o4 - d0*d7*o0^2 + d0*d7*o3^2 - d0*d7 - 6*d0*o0^2*o1 - 2*d0*o0^2*o4 - 2*d0*o0^2*o7 - 2*d0*o0^2 - 4*d0*o0*o1*o3 - 4*d0*o0*o1*o6 - 4*d0*o0*o1 + 2*d0*o0*o3*o7 + 2*d0*o0*o4*o6 - 2*d0*o0 + 2*d0*o1*o3*o6 - d1*d3^2*d6 - d1*d3*d6^2 - 2*d1*d3*d6*o0 - 2*d1*d3*d6*o3 - 2*d1*d3*d6*o6 - 2*d1*d3*d6 - d1*d3*o0^2 + d1*d3*o6^2 - d1*d6*o0^2 + d1*d6*o3^2 - d1*d6 - 2*d1*o0^3 - 2*d1*o0^2*o3 - 2*d1*o0^2*o6 - 2*d1*o0^2 + 2*d1*o0*o3*o6 - d3*d7 - 2*d3*o0 - d4*d6 - 2*d6*d7 - 2*d6*o0 - 2*d6*o1 - 2*d6*o4 - 2*d6*o7 - 2*d6 - 2*d7*o0 - 2*d7*o3 - 2*d7*o6 - 2*d7 - 4*o0^2 - 4*o0*o3 - 4*o0*o6 - 4*o0 + 2*o3*o6 + 2*o6*o7) = 0 ∧
    (-d0^2*d3*d8 - d0^2*d5*d6 - 2*d0^2*o0*o2 - 2*d0*d2*d3*d6 - 2*d0*d2*o0^2 - d0*d3^2*d8 - 2*d0*d3*d5*d6 - 2*d0*d3*d6*d8 - 2*d0*d3*d6*o2 - 2*d0*d3*d6*o5 - 2*d0*d3*d6*o8 - 2*d0*d3*d6 - 2*d0*d3*d8*o0 - 2*d0*d3*d8*o3 - 2*d0*d3*d8*o6 - 2*d0*d3*d8 - 2*d0*d3*o0*o2 + 2*d0*d3*o6*o8 - d0*d5*d6^2 - 2*d0*d5*d6*o0 - 2*d0*d5*d6*o3 - 2*d0*d5*d6*o6 - 2*d0*d5*d6 - d0*d5*o0^2 + d0*d5*o6^2 - 2*d0*d6*o0*o2 + 2*d0*d6*o3*o5 - d0*d8*o0^2 + d0*d8*o3^2 - d0*d8 - 6*d0*o0^2*o2 - 2*d0*o0^2*o5 - 2*d0*o0^2*o8 - 2*d0*o0^2 - 4*d0*o0*o2*o3 - 4*d0*o0*o2*o6 - 4*d0*o0*o2 + 2*d0*o0*o3*o8 + 2*d0*o0*o5*o6 + 2*d0*o2*o3*o6 - d2*d3^2*d6 - d2*d3*d6^2 - 2*d2*d3*d6*o0 - 2*d2*d3*d6*o3 - 2*d2*d3*d6*o6 - 2*d2*d3*d6 - d2*d3*o0^2 + d2*d3*o6^2 - d2*d6*o0^2 + d2*d6*o3^2 - d2*d6 - 2*d2*o0^3 - 2*d2*o0^2*o3 - 2*d2*o0^2*o6 - 2*d2*o0^2 + 2*d2*o0*o3*o6 - d3*d8 - d5*d6 - 2*d6*d8 - 2*d6*o2 + 2*d6*o3 - 2*d6*o5 - 2*d6*o8 - 2*d6 - 2*d8*o0 - 2*d8*o3 - 2*d8*o6 - 2*d8 + 2*o0*o6 + 2*o6*o8) = 0 ∧
    (-d0^2*d3 - d0^2*d6 - 2*d0^2*o0 - d0*d3^2 - 2*d0*d3*d6 - 4*d0*d3*o0 - 2*d0*d3*o3 - 2*d0*d3 - d0*d6^2 - 4*d0*d6*o0 - 2*d0*d6*o6 - 4*d0*d6 - 4*d0*o0^2 - 2*d0*o0*o3 - 2*d0*o0*o6 - 6*d0*o0 + d0*o3^2 + 2*d0*o3*o6 + d0*o6^2 - d0 - d3^2*d6 - d3*d6^2 - 2*d3*d6*o0 - 2*d3*d6*o3 - 2*d3*d6*o6 - 4*d3*d6 - d3*o0^2 - 2*d3*o0 + d3*o6^2 - d3 - 2*d6^2 - d6*o0^2 - 6*d6*o0 + d6*o3^2 - 2*d6*o3 - 4*d6*o6 - 4*d6 - 2*o0^3 - 2*o0^2*o3 - 2*o0^2*o6 - 6*o0^2 + 2*o0*o3*o6 - 4*o0*o3 - 2*o0*o6 - 6*o0 + 2*o3*o6 - 2*o3 + 2*o6^2 - 2) = 0 ∧
    (-d0^2*d4*d7 - d0^2*o1^2 - 2*d0*d1*d3*d7 - 2*d0*d1*d4*d6 - 4*d0*d1*o0*o1 - 2*d0*d3*d4*d7 - d0*d3*d7^2 - 2*d0*d3*d7*o1 - 2*d0*d3*d7*o4 - 2*d0*d3*d7*o7 - 2*d0*d3*d7 - d0*d3*o1^2 + d0*d3*o7^2 - d0*d3 - d0*d4^2*d6 - 2*d0*d4*d6*d7 - 2*d0*d4*d6*o1 - 2*d0*d4*d6*o4 - 2*d0*d4*d6*o7 - 2*d0*d4*d6 - 2*d0*d4*d7*o0 - 2*d0*d4*d7*o3 - 2*d0*d4*d7*o6 - 2*d0*d4*d7 - 2*d0*d4*o0*o1 + 2*d0*d4*o6*o7 - d0*d6*o1^2 + d0*d6*o4^2 - 2*d0*d7*o0*o1 + 2*d0*d7*o3*o4 - 6*d0*o0*o1^2 - 4*d0*o0*o1*o4 - 4*d0*o0*o1*o7 - 4*d0*o0*o1 + 2*d0*o0*o4*o7 - 2*d0*o1^2*o3 - 2*d0*o1^2*o6 - 2*d0*o1^2 + 2*d0*o1*o3*o7 + 2*d0*o1*o4*o6 - 2*d0*o1 - d1^2*d3*d6 - d1^2*o0^2 - d1*d3^2*d7 - 2*d1*d3*d4*d6 - 2*d1*d3*d6*d7 - 2*d1*d3*d6*o1 - 2*d1*d3*d6*o4 - 2*d1*d3*d6*o7 - 2*d1*d3*d6 - 2*d1*d3*d7*o0 - 2*d1*d3*d7*o3 - 2*d1*d3*d7*o6 - 2*d1*d3*d7 - 2*d1*d3*o0*o1 + 2*d1*d3*o6*o7 - d1*d4*d6^2 - 2*d1*d4*d6*o0 - 2*d1*d4*d6*o3 - 2*d1*d4*d6*o6 - 2*d1*d4*d6 - d1*d4*o0^2 + d1*d4*o6^2 - 2*d1*d6*o0*o1 + 2*d1*d6*o3*o4 - d1*d7*o0^2 + d1*d7*o3^2 - d1*d7 - 6*d1*o0^2*o1 - 2*d1*o0^2*o4 - 2*d1*o0^2*o7 - 2*d1*o0^2 - 4*d1*o0*o1*o3 - 4*d1*o0*o1*o6 - 4*d1*o0*o1 + 2*d1*o0*o3*o7 + 2*d1*o0*o4*o6 - 2*d1*o0 + 2*d1*o1*o3*o6 - d3^2 - d3*d6 - 2*d3*o0 - 2*d3*o1 - 2*d3*o3 - 2*d3*o6 - 2*d3 - d4*d7 - 2*d4*o0 - 2*d6*o1 - d7^2 - 2*d7*o0 - 2*d7*o1 - 2*d7*o4 - 2*d7*o7 - 2*d7 - 8*o0*o1 - 4*o0*o4 - 4*o0*o7 - 4*o0 - 4*o1*o3 - 4*o1*o6 - 4*o1 + o3^2 + 2*o3*o7 + 2*o4*o6 + o7^2) = 0 ∧
    (-d0^2*d4*d8 - d0^2*d5*d7 - 2*d0^2*o1*o2 - 2*d0*d1*d3*d8 - 2*d0*d1*d5*d6 - 4*d0*d1*o0*o2 - 2*d0*d2*d3*d7 - 2*d0*d2*d4*d6 - 4*d0*d2*o0*o1 - 2*d0*d3*d4*d8 - 2*d0*d3*d5*d7 - 2*d0*d3*d7*d8 - 2*d0*d3*d7*o2 - 2*d0*d3*d7*o5 - 2*d0*d3*d7*o8 - 2*d0*d3*d7 - 2*d0*d3*d8*o1 - 2*d0*d3*d8*o4 - 2*d0*d3*d8*o7 - 2*d0*d3*d8 - 2*d0*d3*o1*o2 + 2*d0*d3*o7*o8 - 2*d0*d4*d5*d6 - 2*d0*d4*d6*d8 - 2*d0*d4*d6*o2 - 2*d0*d4*d6*o5 - 2*d0*d4*d6*o8 - 2*d0*d4*d6 - 2*d0*d4*d8*o0 - 2*d0*d4*d8*o3 - 2*d0*d4*d8*o6 - 2*d0*d4*d8 - 2*d0*d4*o0*o2 + 2*d0*d4*o6*o8 - 2*d0*d5*d6*d7 - 2*d0*d5*d6*o1 - 2*d0*d5*d6*o4 - 2*d0*d5*d6*o7 - 2*d0*d5*d6 - 2*d0*d5*d7*o0 - 2*d0*d5*d7*o3 - 2*d0*d5*d7*o6 - 2*d0*d5*d7 - 2*d0*d5*o0*o1 + 2*d0*d5*o6*o7 - 2*d0*d6*o1*o2 + 2*d0*d6*o4*o5 - 2*d0*d7*o0*o2 + 2*d0*d7*o3*o5 - 2*d0*d8*o0*o1 + 2*d0*d8*o3*o4 - 12*d0*o0*o1*o2 - 4*d0*o0*o1*o5 - 4*d0*o0*o1*o8 - 4*d0*o0*o1 - 4*d0*o0*o2*o4 - 4*d0*o0*o2*o7 - 4*d0*o0*o2 + 2*d0*o0*o4*o8 + 2*d0*o0*o5*o7 - 4*d0*o1*o2*o3 - 4*d0*o1*o2*o6 - 4*d0*o1*o2 + 2*d0*o1*o3*o8 + 2*d0*o1*o5*o6 + 2*d0*o2*o3*o7 + 2*d0*o2*o4*o6 - 2*d0*o2 - 2*d1*d2*d3*d6 - 2*d1*d2*o0^2 - d1*d3^2*d8 - 2*d1*d3*d5*d6 - 2*d1*d3*d6*d8 - 2*d1*d3*d6*o2 - 2*d1*d3*d6*o5 - 2*d1*d3*d6*o8 - 2*d1*d3*d6 - 2*d1*d3*d8*o0 - 2*d1*d3*d8*o3 - 2*d1*d3*d8*o6 - 2*d1*d3*d8 - 2*d1*d3*o0*o2 + 2*d1*d3*o6*o8 - d1*d5*d6^2 - 2*d1*d5*d6*o0 - 2*d1*d5*d6*o3 - 2*d1*d5*d6*o6 - 2*d1*d5*d6 - d1*d5*o0^2 + d1*d5*o6^2 - 2*d1*d6*o0*o2 + 2*d1*d6*o3*o5 - d1*d8*o0^2 + d1*d8*o3^2 - d1*d8 - 6*d1*o0^2*o2 - 2*d1*o0^2*o5 - 2*d1*o0^2*o8 - 2*d1*o0^2 - 4*d1*o0*o2*o3 - 4*d1*o0*o2*o6 - 4*d1*o0*o2 + 2*d1*o0*o3*o8 + 2*d1*o0*o5*o6 + 2*d1*o2*o3*o6 - d2*d3^2*d7 - 2*d2*d3*d4*d6 - 2*d2*d3*d6*d7 - 2*d2*d3*d6*o1 - 2*d2*d3*d6*o4 - 2*d2*d3*d6*o7 - 2*d2*d3*d6 - 2*d2*d3*d7*o0 - 2*d2*d3*d7*o3 - 2*d2*d3*d7*o6 - 2*d2*d3*d7 - 2*d2*d3*o0*o1 + 2*d2*d3*o6*o7 - d2*d4*d6^2 - 2*d2*d4*d6*o0 - 2*d2*d4*d6*o3 - 2*d2*d4*d6*o6 - 2*d2*d4*d6 - d2*d4*o0^2 + d2*d4*o6^2 - 2*d2*d6*o0*o1 + 2*d2*d6*o3*o4 - d2*d7*o0^2 + d2*d7*o3^2 - d2*d7 - 6*d2*o0^2*o1 - 2*d2*o0^2*o4 - 2*d2*o0^2*o7 - 2*d2*o0^2 - 4*d2*o0*o1*o3 - 4*d2*o0*o1*o6 - 4*d2*o0*o1 + 2*d2*o0*o3*o7 + 2*d2*o0*o4*o6 - 2*d2*o0 + 2*d2*o1*o3*o6 - 2*d3*o2 + 2*d3*o6 - d4*d8 - d5*d7 - 2*d5*o0 - 2*d6*o2 + 2*d6*o4 - 2*d7*d8 - 2*d7*o2 + 2*d7*o3 - 2*d7*o5 - 2*d7*o8 - 2*d7 - 2*d8*o0 - 2*d8*o1 - 2*d8*o4 - 2*d8*o7 - 2*d8 - 8*o0*o2 + 2*o0*o3 - 4*o0*o5 + 2*o0*o7 - 4*o0*o8 - 4*o0 + 2*o1*o6 - 4*o2*o3 - 4*o2*o6 - 4*o2 + 2*o3*o8 + 2*o5*o6 + 2*o7*o8) = 0 ∧
    (-d0^2*d4 - d0^2*d7 - 2*d0^2*o1 - 2*d0*d1*d3 - 2*d0*d1*d6 - 4*d0*d1*o0 - 2*d0*d3*d4 - 2*d0*d3*d7 - 4*d0*d3*o1 - 2*d0*d3*o4 - 4*d0*d3 - 2*d0*d4*d6 - 4*d0*d4*o0 - 2*d0*d4*o3 - 2*d0*d4 - 2*d0*d6*d7 - 4*d0*d6*o1 - 2*d0*d6*o7 - 2*d0*d6 - 4*d0*d7*o0 - 2*d0*d7*o6 - 4*d0*d7 - 8*d0*o0*o1 - 2*d0*o0*o4 - 2*d0*o0*o7 - 6*d0*o0 - 2*d0*o1*o3 - 2*d0*o1*o6 - 6*d0*o1 + 2*d0*o3*o4 + 2*d0*o3*o7 + 2*d0*o4*o6 + 2*d0*o6*o7 - 2*d0 - d1*d3^2 - 2*d1*d3*d6 - 4*d1*d3*o0 - 2*d1*d3*o3 - 2*d1*d3 - d1*d6^2 - 4*d1*d6*o0 - 2*d1*d6*o6 - 4*d1*d6 - 4*d1*o0^2 - 2*d1*o0*o3 - 2*d1*o0*o6 - 6*d1*o0 + d1*o3^2 + 2*d1*o3*o6 + d1*o6^2 - d1 - d3^2*d7 - 2*d3^2 - 2*d3*d4*d6 - 2*d3*d6*d7 - 2*d3*d6*o1 - 2*d3*d6*o4 - 2*d3*d6*o7 - 4*d3*d6 - 2*d3*d7*o0 - 2*d3*d7*o3 - 2*d3*d7*o6 - 4*d3*d7 - 2*d3*o0*o1 - 6*d3*o0 - 2*d3*o1 - 4*d3*o3 + 2*d3*o6*o7 - 2*d3*o6 - 6*d3 - d4*d6^2 - 2*d4*d6*o0 - 2*d4*d6*o3 - 2*d4*d6*o6 - 4*d4*d6 - d4*o0^2 - 2*d4*o0 + d4*o6^2 - d4 - 4*d6*d7 - 2*d6*o0*o1 - 2*d6*o0 - 6*d6*o1 + 2*d6*o3*o4 - 2*d6*o4 - 4*d6*o7 - 6*d6 - d7*o0^2 - 6*d7*o0 + d7*o3^2 - 2*d7*o3 - 4*d7*o6 - 4*d7 - 6*o0^2*o1 - 2*o0^2*o4 - 2*o0^2*o7 - 6*o0^2 - 4*o0*o1*o3 - 4*o0*o1*o6 - 12*o0*o1 + 2*o0*o3*o7 - 2*o0*o3 + 2*o0*o4*o6 - 4*o0*o4 - 4*o0*o6 - 2*o0*o7 - 10*o0 + 2*o1*o3*o6 - 4*o1*o3 - 2*o1*o6 - 6*o1 + 2*o3^2 + 2*o3*o6 + 2*o3*o7 - 2*o3 + 2*o4*o6 - 2*o4 + 4*o6*o7 - 2*o6 - 6) = 0 ∧
    (-d0^2*d5*d8 - d0^2*o2^2 - 2*d0*d2*d3*d8 - 2*d0*d2*d5*d6 - 4*d0*d2*o0*o2 - 2*d0*d3*d5*d8 - d0*d3*d8^2 - 2*d0*d3*d8*o2 - 2*d0*d3*d8*o5 - 2*d0*d3*d8*o8 - 2*d0*d3*d8 - d0*d3*o2^2 + d0*d3*o8^2 - d0*d5^2*d6 - 2*d0*d5*d6*d8 - 2*d0*d5*d6*o2 - 2*d0*d5*d6*o5 - 2*d0*d5*d6*o8 - 2*d0*d5*d6 - 2*d0*d5*d8*o0 - 2*d0*d5*d8*o3 - 2*d0*d5*d8*o6 - 2*d0*d5*d8 - 2*d0*d5*o0*o2 + 2*d0*d5*o6*o8 - d0*d6*o2^2 + d0*d6*o5^2 - 2*d0*d8*o0*o2 + 2*d0*d8*o3*o5 - 6*d0*o0*o2^2 - 4*d0*o0*o2*o5 - 4*d0*o0*o2*o8 - 4*d0*o0*o2 + 2*d0*o0*o5*o8 - 2*d0*o2^2*o3 - 2*d0*o2^2*o6 - 2*d0*o2^2 + 2*d0*o2*o3*o8 + 2*d0*o2*o5*o6 - d2^2*d3*d6 - d2^2*o0^2 - d2*d3^2*d8 - 2*d2*d3*d5*d6 - 2*d2*d3*d6*d8 - 2*d2*d3*d6*o2 - 2*d2*d3*d6*o5 - 2*d2*d3*d6*o8 - 2*d2*d3*d6 - 2*d2*d3*d8*o0 - 2*d2*d3*d8*o3 - 2*d2*d3*d8*o6 - 2*d2*d3*d8 - 2*d2*d3*o0*o2 + 2*d2*d3*o6*o8 - d2*d5*d6^2 - 2*d2*d5*d6*o0 - 2*d2*d5*d6*o3 - 2*d2*d5*d6*o6 - 2*d2*d5*d6 - d2*d5*o0^2 + d2*d5*o6^2 - 2*d2*d6*o0*o2 + 2*d2*d6*o3*o5 - d2*d8*o0^2 + d2*d8*o3^2 - d2*d8 - 6*d2*o0^2*o2 - 2*d2*o0^2*o5 - 2*d2*o0^2*o8 - 2*d2*o0^2 - 4*d2*o0*o2*o3 - 4*d2*o0*o2*o6 - 4*d2*o0*o2 + 2*d2*o0*o3*o8 + 2*d2*o0*o5*o6 + 2*d2*o2*o3*o6 + d3*d6 - d5*d8 + 2*d6*o5 - d8^2 - 2*d8*o2 + 2*d8*o3 - 2*d8*o5 - 2*d8*o8 - 2*d8 + o0^2 + 2*o0*o8 + 2*o2*o6 + o8^2) = 0 ∧
    (-d0^2*d5 - d0^2*d8 - 2*d0^2*o2 - 2*d0*d2*d3 - 2*d0*d2*d6 - 4*d0*d2*o0 - 2*d0*d3*d5 - 2*d0*d3*d8 - 4*d0*d3*o2 - 2*d0*d3*o5 - 2*d0*d3 - 2*d0*d5*d6 - 4*d0*d5*o0 - 2*d0*d5*o3 - 2*d0*d5 - 2*d0*d6*d8 - 4*d0*d6*o2 - 2*d0*d6*o8 - 2*d0*d6 - 4*d0*d8*o0 - 2*d0*d8*o6 - 4*d0*d8 - 8*d0*o0*o2 - 2*d0*o0*o5 - 2*d0*o0*o8 - 4*d0*o0 - 2*d0*o2*o3 - 2*d0*o2*o6 - 6*d0*o2 + 2*d0*o3*o5 + 2*d0*o3*o8 + 2*d0*o5*o6 + 2*d0*o6*o8 - d2*d3^2 - 2*d2*d3*d6 - 4*d2*d3*o0 - 2*d2*d3*o3 - 2*d2*d3 - d2*d6^2 - 4*d2*d6*o0 - 2*d2*d6*o6 - 4*d2*d6 - 4*d2*o0^2 - 2*d2*o0*o3 - 2*d2*o0*o6 - 6*d2*o0 + d2*o3^2 + 2*d2*o3*o6 + d2*o6^2 - d2 - d3^2*d8 - 2*d3*d5*d6 - 2*d3*d6*d8 - 2*d3*d6*o2 - 2*d3*d6*o5 - 2*d3*d6*o8 - 2*d3*d8*o0 - 2*d3*d8*o3 - 2*d3*d8*o6 - 4*d3*d8 - 2*d3*o0*o2 - 2*d3*o2 + 2*d3*o6*o8 + 2*d3*o6 - d5*d6^2 - 2*d5*d6*o0 - 2*d5*d6*o3 - 2*d5*d6*o6 - 4*d5*d6 - d5*o0^2 - 2*d5*o0 + d5*o6^2 - d5 - 4*d6*d8 - 2*d6*o0*o2 - 6*d6*o2 + 2*d6*o3*o5 + 2*d6*o3 - 2*d6*o5 - 4*d6*o8 - 2*d6 - d8*o0^2 - 6*d8*o0 + d8*o3^2 - 2*d8*o3 - 4*d8*o6 - 4*d8 - 6*o0^2*o2 - 2*o0^2*o5 - 2*o0^2*o8 - 4*o0*o2*o3 - 4*o0*o2*o6 - 12*o0*o2 + 2*o0*o3*o8 + 2*o0*o3 + 2*o0*o5*o6 - 4*o0*o5 + 2*o0*o6 - 2*o0*o8 - 2*o0 + 2*o2*o3*o6 - 4*o2*o3 - 2*o2*o6 - 6*o2 + 2*o3*o8 + 2*o3 + 2*o5*o6 - 2*o5 + 4*o6*o8 + 2*o6 - 2) = 0 ∧
    (-d0^2 - d0*d3 - d0*d6 - 2*d0*o0 - 4*d0 - d3^2 - d3*d6 - 4*d3*o0 - 2*d3*o3 - 4*d3 - d6^2 - 4*d6*o0 - 2*d6*o6 - 2*d6 - 3*o0^2 - 2*o0*o3 - 2*o0*o6 - 6*o0 + o3^2 + 2*o3*o6 - 2*o3 + o6^2 - 3) = 0 ∧
    (-2*d0*d1*d4*d7 - 2*d0*d1*o1^2 - d0*d4^2*d7 - d0*d4*d7^2 - 2*d0*d4*d7*o1 - 2*d0*d4*d7*o4 - 2*d0*d4*d7*o7 - 2*d0*d4*d7 - d0*d4*o1^2 + d0*d4*o7^2 - d0*d4 - d0*d7*o1^2 + d0*d7*o4^2 - 2*d0*o1^3 - 2*d0*o1^2*o4 - 2*d0*o1^2*o7 - 2*d0*o1^2 + 2*d0*o1*o4*o7 - d1^2*d3*d7 - d1^2*d4*d6 - 2*d1^2*o0*o1 - 2*d1*d3*d4*d7 - d1*d3*d7^2 - 2*d1*d3*d7*o1 - 2*d1*d3*d7*o4 - 2*d1*d3*d7*o7 - 2*d1*d3*d7 - d1*d3*o1^2 + d1*d3*o7^2 - d1*d3 - d1*d4^2*d6 - 2*d1*d4*d6*d7 - 2*d1*d4*d6*o1 - 2*d1*d4*d6*o4 - 2*d1*d4*d6*o7 - 2*d1*d4*d6 - 2*d1*d4*d7*o0 - 2*d1*d4*d7*o3 - 2*d1*d4*d7*o6 - 2*d1*d4*d7 - 2*d1*d4*o0*o1 + 2*d1*d4*o6*o7 - d1*d6*o1^2 + d1*d6*o4^2 - 2*d1*d7*o0*o1 + 2*d1*d7*o3*o4 - 6*d1*o0*o1^2 - 4*d1*o0*o1*o4 - 4*d1*o0*o1*o7 - 4*d1*o0*o1 + 2*d1*o0*o4*o7 - 2*d1*o1^2*o3 - 2*d1*o1^2*o6 - 2*d1*o1^2 + 2*d1*o1*o3*o7 + 2*d1*o1*o4*o6 - 2*d1*o1 - 2*d3*d4 - d3*d7 - 2*d3*o1 - 2*d3*o4 - 2*d3*o7 - 2*d3 - d4*d6 - 2*d4*o0 - 2*d4*o1 - 2*d4*o3 - 2*d4*o6 - 2*d4 - 2*d7*o1 - 4*o1^2 - 4*o1*o4 - 4*o1*o7 - 4*o1 + 2*o3*o4 + 2*o4*o7) = 0 ∧
    (-2*d0*d1*d4*d8 - 2*d0*d1*d5*d7 - 4*d0*d1*o1*o2 - 2*d0*d2*d4*d7 - 2*d0*d2*o1^2 - d0*d4^2*d8 - 2*d0*d4*d5*d7 - 2*d0*d4*d7*d8 - 2*d0*d4*d7*o2 - 2*d0*d4*d7*o5 - 2*d0*d4*d7*o8 - 2*d0*d4*d7 - 2*d0*d4*d8*o1 - 2*d0*d4*d8*o4 - 2*d0*d4*d8*o7 - 2*d0*d4*d8 - 2*d0*d4*o1*o2 + 2*d0*d4*o7*o8 - d0*d5*d7^2 - 2*d0*d5*d7*o1 - 2*d0*d5*d7*o4 - 2*d0*d5*d7*o7 - 2*d0*d5*d7 - d0*d5*o1^2 + d0*d5*o7^2 - d0*d5 - 2*d0*d7*o1*o2 + 2*d0*d7*o4*o5 - d0*d8*o1^2 + d0*d8*o4^2 - 6*d0*o1^2*o2 - 2*d0*o1^2*o5 - 2*d0*o1^2*o8 - 2*d0*o1^2 - 4*d0*o1*o2*o4 - 4*d0*o1*o2*o7 - 4*d0*o1*o2 + 2*d0*o1*o4*o8 + 2*d0*o1*o5*o7 + 2*d0*o2*o4*o7 - d1^2*d3*d8 - d1^2*d5*d6 - 2*d1^2*o0*o2 - 2*d1*d2*d3*d7 - 2*d1*d2*d4*d6 - 4*d1*d2*o0*o1 - 2*d1*d3*d4*d8 - 2*d1*d3*d5*d7 - 2*d1*d3*d7*d8 - 2*d1*d3*d7*o2 - 2*d1*d3*d7*o5 - 2*d1*d3*d7*o8 - 2*d1*d3*d7 - 2*d1*d3*d8*o1 - 2*d1*d3*d8*o4 - 2*d1*d3*d8*o7 - 2*d1*d3*d8 - 2*d1*d3*o1*o2 + 2*d1*d3*o7*o8 - 2*d1*d4*d5*d6 - 2*d1*d4*d6*d8 - 2*d1*d4*d6*o2 - 2*d1*d4*d6*o5 - 2*d1*d4*d6*o8 - 2*d1*d4*d6 - 2*d1*d4*d8*o0 - 2*d1*d4*d8*o3 - 2*d1*d4*d8*o6 - 2*d1*d4*d8 - 2*d1*d4*o0*o2 + 2*d1*d4*o6*o8 - 2*d1*d5*d6*d7 - 2*d1*d5*d6*o1 - 2*d1*d5*d6*o4 - 2*d1*d5*d6*o7 - 2*d1*d5*d6 - 2*d1*d5*d7*o0 - 2*d1*d5*d7*o3 - 2*d1*d5*d7*o6 - 2*d1*d5*d7 - 2*d1*d5*o0*o1 + 2*d1*d5*o6*o7 - 2*d1*d6*o1*o2 + 2*d1*d6*o4*o5 - 2*d1*d7*o0*o2 + 2*d1*d7*o3*o5 - 2*d1*d8*o0*o1 + 2*d1*d8*o3*o4 - 12*d1*o0*o1*o2 - 4*d1*o0*o1*o5 - 4*d1*o0*o1*o8 - 4*d1*o0*o1 - 4*d1*o0*o2*o4 - 4*d1*o0*o2*o7 - 4*d1*o0*o2 + 2*d1*o0*o4*o8 + 2*d1*o0*o5*o7 - 4*d1*o1*o2*o3 - 4*d1*o1*o2*o6 - 4*d1*o1*o2 + 2*d1*o1*o3*o8 + 2*d1*o1*o5*o6 + 2*d1*o2*o3*o7 + 2*d1*o2*o4*o6 - 2*d1*o2 - 2*d2*d3*d4*d7 - d2*d3*d7^2 - 2*d2*d3*d7*o1 - 2*d2*d3*d7*o4 - 2*d2*d3*d7*o7 - 2*d2*d3*d7 - d2*d3*o1^2 + d2*d3*o7^2 - d2*d3 - d2*d4^2*d6 - 2*d2*d4*d6*d7 - 2*d2*d4*d6*o1 - 2*d2*d4*d6*o4 - 2*d2*d4*d6*o7 - 2*d2*d4*d6 - 2*d2*d4*d7*o0 - 2*d2*d4*d7*o3 - 2*d2*d4*d7*o6 - 2*d2*d4*d7 - 2*d2*d4*o0*o1 + 2*d2*d4*o6*o7 - d2*d6*o1^2 + d2*d6*o4^2 - 2*d2*d7*o0*o1 + 2*d2*d7*o3*o4 - 6*d2*o0*o1^2 - 4*d2*o0*o1*o4 - 4*d2*o0*o1*o7 - 4*d2*o0*o1 + 2*d2*o0*o4*o7 - 2*d2*o1^2*o3 - 2*d2*o1^2*o6 - 2*d2*o1^2 + 2*d2*o1*o3*o7 + 2*d2*o1*o4*o6 - 2*d2*o1 - 2*d3*d5 - d3*d8 - 2*d3*o2 - 2*d3*o5 + 2*d3*o7 - 2*d3*o8 - 2*d3 - 2*d4*o2 + 2*d4*o6 - d5*d6 - 2*d5*o0 - 2*d5*o1 - 2*d5*o3 - 2*d5*o6 - 2*d5 - 2*d7*o2 + 2*d7*o4 - 2*d8*o1 + 2*o0*o4 - 8*o1*o2 + 2*o1*o3 - 4*o1*o5 + 2*o1*o7 - 4*o1*o8 - 4*o1 - 4*o2*o4 - 4*o2*o7 - 4*o2 + 2*o3*o5 + 2*o4*o8 + 2*o5*o7) = 0 ∧
    (-2*d0*d1*d4 - 2*d0*d1*d7 - 4*d0*d1*o1 - d0*d4^2 - 2*d0*d4*d7 - 4*d0*d4*o1 - 2*d0*d4*o4 - 4*d0*d4 - d0*d7^2 - 4*d0*d7*o1 - 2*d0*d7*o7 - 2*d0*d7 - 4*d0*o1^2 - 2*d0*o1*o4 - 2*d0*o1*o7 - 6*d0*o1 + d0*o4^2 + 2*d0*o4*o7 + d0*o7^2 - d0 - d1^2*d3 - d1^2*d6 - 2*d1^2*o0 - 2*d1*d3*d4 - 2*d1*d3*d7 - 4*d1*d3*o1 - 2*d1*d3*o4 - 4*d1*d3 - 2*d1*d4*d6 - 4*d1*d4*o0 - 2*d1*d4*o3 - 2*d1*d4 - 2*d1*d6*d7 - 4*d1*d6*o1 - 2*d1*d6*o7 - 2*d1*d6 - 4*d1*d7*o0 - 2*d1*d7*o6 - 4*d1*d7 - 8*d1*o0*o1 - 2*d1*o0*o4 - 2*d1*o0*o7 - 6*d1*o0 - 2*d1*o1*o3 - 2*d1*o1*o6 - 6*d1*o1 + 2*d1*o3*o4 + 2*d1*o3*o7 + 2*d1*o4*o6 + 2*d1*o6*o7 - 2*d1 - 2*d3*d4*d7 - 4*d3*d4 - d3*d7^2 - 2*d3*d7*o1 - 2*d3*d7*o4 - 2*d3*d7*o7 - 4*d3*d7 - d3*o1^2 - 6*d3*o1 - 4*d3*o4 + d3*o7^2 - 2*d3*o7 - 4*d3 - d4^2*d6 - 2*d4*d6*d7 - 2*d4*d6*o1 - 2*d4*d6*o4 - 2*d4*d6*o7 - 4*d4*d6 - 2*d4*d7*o0 - 2*d4*d7*o3 - 2*d4*d7*o6 - 4*d4*d7 - 2*d4*o0*o1 - 6*d4*o0 - 2*d4*o1 - 4*d4*o3 + 2*d4*o6*o7 - 2*d4*o6 - 6*d4 - d6*o1^2 - 2*d6*o1 + d6*o4^2 - d6 - 2*d7^2 - 2*d7*o0*o1 - 2*d7*o0 - 6*d7*o1 + 2*d7*o3*o4 - 2*d7*o4 - 4*d7*o7 - 6*d7 - 6*o0*o1^2 - 4*o0*o1*o4 - 4*o0*o1*o7 - 12*o0*o1 + 2*o0*o4*o7 - 2*o0*o4 - 4*o0*o7 - 6*o0 - 2*o1^2*o3 - 2*o1^2*o6 - 6*o1^2 + 2*o1*o3*o7 - 2*o1*o3 + 2*o1*o4*o6 - 4*o1*o4 - 4*o1*o6 - 2*o1*o7 - 10*o1 + 4*o3*o4 + 2*o3*o7 + 2*o4*o6 + 2*o4*o7 - 2*o4 - 2*o6 + 2*o7^2 - 2*o7 - 6) = 0 ∧
    (-2*d0*d1*d5*d8 - 2*d0*d1*o2^2 - 2*d0*d2*d4*d8 - 2*d0*d2*d5*d7 - 4*d0*d2*o1*o2 - 2*d0*d4*d5*d8 - d0*d4*d8^2 - 2*d0*d4*d8*o2 - 2*d0*d4*d8*o5 - 2*d0*d4*d8*o8 - 2*d0*d4*d8 - d0*d4*o2^2 + d0*d4*o8^2 - d0*d5^2*d7 - 2*d0*d5*d7*d8 - 2*d0*d5*d7*o2 - 2*d0*d5*d7*o5 - 2*d0*d5*d7*o8 - 2*d0*d5*d7 - 2*d0*d5*d8*o1 - 2*d0*d5*d8*o4 - 2*d0*d5*d8*o7 - 2*d0*d5*d8 - 2*d0*d5*o1*o2 + 2*d0*d5*o7*o8 - d0*d7*o2^2 + d0*d7*o5^2 - 2*d0*d8*o1*o2 + 2*d0*d8*o4*o5 - 6*d0*o1*o2^2 - 4*d0*o1*o2*o5 - 4*d0*o1*o2*o8 - 4*d0*o1*o2 + 2*d0*o1*o5*o8 - 2*d0*o2^2*o4 - 2*d0*o2^2*o7 - 2*d0*o2^2 + 2*d0*o2*o4*o8 + 2*d0*o2*o5*o7 - 2*d1*d2*d3*d8 - 2*d1*d2*d5*d6 - 4*d1*d2*o0*o2 - 2*d1*d3*d5*d8 - d1*d3*d8^2 - 2*d1*d3*d8*o2 - 2*d1*d3*d8*o5 - 2*d1*d3*d8*o8 - 2*d1*d3*d8 - d1*d3*o2^2 + d1*d3*o8^2 - d1*d5^2*d6 - 2*d1*d5*d6*d8 - 2*d1*d5*d6*o2 - 2*d1*d5*d6*o5 - 2*d1*d5*d6*o8 - 2*d1*d5*d6 - 2*d1*d5*d8*o0 - 2*d1*d5*d8*o3 - 2*d1*d5*d8*o6 - 2*d1*d5*d8 - 2*d1*d5*o0*o2 + 2*d1*d5*o6*o8 - d1*d6*o2^2 + d1*d6*o5^2 - 2*d1*d8*o0*o2 + 2*d1*d8*o3*o5 - 6*d1*o0*o2^2 - 4*d1*o0*o2*o5 - 4*d1*o0*o2*o8 - 4*d1*o0*o2 + 2*d1*o0*o5*o8 - 2*d1*o2^2*o3 - 2*d1*o2^2*o6 - 2*d1*o2^2 + 2*d1*o2*o3*o8 + 2*d1*o2*o5*o6 - d2^2*d3*d7 - d2^2*d4*d6 - 2*d2^2*o0*o1 - 2*d2*d3*d4*d8 - 2*d2*d3*d5*d7 - 2*d2*d3*d7*d8 - 2*d2*d3*d7*o2 - 2*d2*d3*d7*o5 - 2*d2*d3*d7*o8 - 2*d2*d3*d7 - 2*d2*d3*d8*o1 - 2*d2*d3*d8*o4 - 2*d2*d3*d8*o7 - 2*d2*d3*d8 - 2*d2*d3*o1*o2 + 2*d2*d3*o7*o8 - 2*d2*d4*d5*d6 - 2*d2*d4*d6*d8 - 2*d2*d4*d6*o2 - 2*d2*d4*d6*o5 - 2*d2*d4*d6*o8 - 2*d2*d4*d6 - 2*d2*d4*d8*o0 - 2*d2*d4*d8*o3 - 2*d2*d4*d8*o6 - 2*d2*d4*d8 - 2*d2*d4*o0*o2 + 2*d2*d4*o6*o8 - 2*d2*d5*d6*d7 - 2*d2*d5*d6*o1 - 2*d2*d5*d6*o4 - 2*d2*d5*d6*o7 - 2*d2*d5*d6 - 2*d2*d5*d7*o0 - 2*d2*d5*d7*o3 - 2*d2*d5*d7*o6 - 2*d2*d5*d7 - 2*d2*d5*o0*o1 + 2*d2*d5*o6*o7 - 2*d2*d6*o1*o2 + 2*d2*d6*o4*o5 - 2*d2*d7*o0*o2 + 2*d2*d7*o3*o5 - 2*d2*d8*o0*o1 + 2*d2*d8*o3*o4 - 12*d2*o0*o1*o2 - 4*d2*o0*o1*o5 - 4*d2*o0*o1*o8 - 4*d2*o0*o1 - 4*d2*o0*o2*o4 - 4*d2*o0*o2*o7 - 4*d2*o0*o2 + 2*d2*o0*o4*o8 + 2*d2*o0*o5*o7 - 4*d2*o1*o2*o3 - 4*d2*o1*o2*o6 - 4*d2*o1*o2 + 2*d2*o1*o3*o8 + 2*d2*o1*o5*o6 + 2*d2*o2*o3*o7 + 2*d2*o2*o4*o6 - 2*d2*o2 + d3*d7 + 2*d3*o8 + d4*d6 - 2*d5*o2 + 2*d5*o6 + 2*d7*o5 - 2*d8*o2 + 2*d8*o4 + 2*o0*o1 + 2*o0*o5 + 2*o1*o8 - 4*o2^2 + 2*o2*o3 - 4*o2*o5 + 2*o2*o7 - 4*o2*o8 - 4*o2 + 2*o5*o8) = 0 ∧
    (-d0*d1*d5 - d0*d1*d8 - 2*d0*d1*o2 - d0*d2*d4 - d0*d2*d7 - 2*d0*d2*o1 - d0*d4*d5 - d0*d4*d8 - 2*d0*d4*o2 - d0*d4*o5 - d0*d4 - d0*d5*d7 - 2*d0*d5*o1 - d0*d5*o4 - 2*d0*d5 - d0*d7*d8 - 2*d0*d7*o2 - d0*d7*o8 - d0*d7 - 2*d0*d8*o1 - d0*d8*o7 - d0*d8 - 4*d0*o1*o2 - d0*o1*o5 - d0*o1*o8 - 2*d0*o1 - d0*o2*o4 - d0*o2*o7 - 3*d0*o2 + d0*o4*o5 + d0*o4*o8 + d0*o5*o7 + d0*o7*o8 - d1*d2*d3 - d1*d2*d6 - 2*d1*d2*o0 - d1*d3*d5 - d1*d3*d8 - 2*d1*d3*o2 - d1*d3*o5 - d1*d3 - d1*d5*d6 - 2*d1*d5*o0 - d1*d5*o3 - d1*d5 - d1*d6*d8 - 2*d1*d6*o2 - d1*d6*o8 - d1*d6 - 2*d1*d8*o0 - d1*d8*o6 - 2*d1*d8 - 4*d1*o0*o2 - d1*o0*o5 - d1*o0*o8 - 2*d1*o0 - d1*o2*o3 - d1*o2*o6 - 3*d1*o2 + d1*o3*o5 + d1*o3*o8 + d1*o5*o6 + d1*o6*o8 - d2*d3*d4 - d2*d3*d7 - 2*d2*d3*o1 - d2*d3*o4 - 2*d2*d3 - d2*d4*d6 - 2*d2*d4*o0 - d2*d4*o3 - d2*d4 - d2*d6*d7 - 2*d2*d6*o1 - d2*d6*o7 - d2*d6 - 2*d2*d7*o0 - d2*d7*o6 - 2*d2*d7 - 4*d2*o0*o1 - d2*o0*o4 - d2*o0*o7 - 3*d2*o0 - d2*o1*o3 - d2*o1*o6 - 3*d2*o1 + d2*o3*o4 + d2*o3*o7 + d2*o4*o6 + d2*o6*o7 - d2 - d3*d4*d8 - d3*d5*d7 - 2*d3*d5 - d3*d7*d8 - d3*d7*o2 - d3*d7*o5 - d3*d7*o8 - d3*d8*o1 - d3*d8*o4 - d3*d8*o7 - 2*d3*d8 - d3*o1*o2 - 3*d3*o2 - 2*d3*o5 + d3*o7*o8 + d3*o7 - d3*o8 - d3 - d4*d5*d6 - d4*d6*d8 - d4*d6*o2 - d4*d6*o5 - d4*d6*o8 - d4*d8*o0 - d4*d8*o3 - d4*d8*o6 - 2*d4*d8 - d4*o0*o2 - d4*o2 + d4*o6*o8 + d4*o6 - d5*d6*d7 - d5*d6*o1 - d5*d6*o4 - d5*d6*o7 - 2*d5*d6 - d5*d7*o0 - d5*d7*o3 - d5*d7*o6 - 2*d5*d7 - d5*o0*o1 - 3*d5*o0 - d5*o1 - 2*d5*o3 + d5*o6*o7 - d5*o6 - 3*d5 - d6*o1*o2 - d6*o2 + d6*o4*o5 + d6*o4 - 2*d7*d8 - d7*o0*o2 - 3*d7*o2 + d7*o3*o5 + d7*o3 - d7*o5 - 2*d7*o8 - d7 - d8*o0*o1 - d8*o0 - 3*d8*o1 + d8*o3*o4 - d8*o4 - 2*d8*o7 - 3*d8 - 6*o0*o1*o2 - 2*o0*o1*o5 - 2*o0*o1*o8 - 2*o0*o2*o4 - 2*o0*o2*o7 - 6*o0*o2 + o0*o4*o8 + o0*o4 + o0*o5*o7 - o0*o5 + o0*o7 - 2*o0*o8 - o0 - 2*o1*o2*o3 - 2*o1*o2*o6 - 6*o1*o2 + o1*o3*o8 + o1*o3 + o1*o5*o6 - 2*o1*o5 + o1*o6 - o1*o8 - o1 + o2*o3*o7 - o2*o3 + o2*o4*o6 - 2*o2*o4 - 2*o2*o6 - o2*o7 - 5*o2 + 2*o3*o5 + o3*o8 + o3 + o4*o8 + o4 + o5*o6 + o5*o7 - o5 + o6 + 2*o7*o8 + o7 - o8 - 2) = 0 ∧
    (-2*d0*d1 - d0*d4 - d0*d7 - 2*d0*o1 - 4*d0 - d1*d3 - d1*d6 - 2*d1*o0 - 4*d1 - 2*d3*d4 - d3*d7 - 4*d3*o1 - 2*d3*o4 - 2*d3 - d4*d6 - 4*d4*o0 - 2*d4*o3 - 4*d4 - 2*d6*d7 - 4*d6*o1 - 2*d6*o7 - 4*d6 - 4*d7*o0 - 2*d7*o6 - 2*d7 - 6*o0*o1 - 2*o0*o4 - 2*o0*o7 - 6*o0 - 2*o1*o3 - 2*o1*o6 - 6*o1 + 2*o3*o4 + 2*o3*o7 + 2*o4*o6 - 2*o4 + 2*o6*o7 - 2*o6 - 6) = 0 ∧
    (-2*d0*d2*d5*d8 - 2*d0*d2*o2^2 - d0*d5^2*d8 - d0*d5*d8^2 - 2*d0*d5*d8*o2 - 2*d0*d5*d8*o5 - 2*d0*d5*d8*o8 - 2*d0*d5*d8 - d0*d5*o2^2 + d0*d5*o8^2 - d0*d8*o2^2 + d0*d8*o5^2 - 2*d0*o2^3 - 2*d0*o2^2*o5 - 2*d0*o2^2*o8 - 2*d0*o2^2 + 2*d0*o2*o5*o8 - d2^2*d3*d8 - d2^2*d5*d6 - 2*d2^2*o0*o2 - 2*d2*d3*d5*d8 - d2*d3*d8^2 - 2*d2*d3*d8*o2 - 2*d2*d3*d8*o5 - 2*d2*d3*d8*o8 - 2*d2*d3*d8 - d2*d3*o2^2 + d2*d3*o8^2 - d2*d5^2*d6 - 2*d2*d5*d6*d8 - 2*d2*d5*d6*o2 - 2*d2*d5*d6*o5 - 2*d2*d5*d6*o8 - 2*d2*d5*d6 - 2*d2*d5*d8*o0 - 2*d2*d5*d8*o3 - 2*d2*d5*d8*o6 - 2*d2*d5*d8 - 2*d2*d5*o0*o2 + 2*d2*d5*o6*o8 - d2*d6*o2^2 + d2*d6*o5^2 - 2*d2*d8*o0*o2 + 2*d2*d8*o3*o5 - 6*d2*o0*o2^2 - 4*d2*o0*o2*o5 - 4*d2*o0*o2*o8 - 4*d2*o0*o2 + 2*d2*o0*o5*o8 - 2*d2*o2^2*o3 - 2*d2*o2^2*o6 - 2*d2*o2^2 + 2*d2*o2*o3*o8 + 2*d2*o2*o5*o6 + d3*d8 + d5*d6 + 2*d8*o5 + 2*o0*o2 + 2*o2*o8) = 0 ∧
    (-2*d0*d2*d5 - 2*d0*d2*d8 - 4*d0*d2*o2 - d0*d5^2 - 2*d0*d5*d8 - 4*d0*d5*o2 - 2*d0*d5*o5 - 2*d0*d5 - d0*d8^2 - 4*d0*d8*o2 - 2*d0*d8*o8 - 2*d0*d8 - 4*d0*o2^2 - 2*d0*o2*o5 - 2*d0*o2*o8 - 4*d0*o2 + d0*o5^2 + 2*d0*o5*o8 + d0*o8^2 - d2^2*d3 - d2^2*d6 - 2*d2^2*o0 - 2*d2*d3*d5 - 2*d2*d3*d8 - 4*d2*d3*o2 - 2*d2*d3*o5 - 2*d2*d3 - 2*d2*d5*d6 - 4*d2*d5*o0 - 2*d2*d5*o3 - 2*d2*d5 - 2*d2*d6*d8 - 4*d2*d6*o2 - 2*d2*d6*o8 - 2*d2*d6 - 4*d2*d8*o0 - 2*d2*d8*o6 - 4*d2*d8 - 8*d2*o0*o2 - 2*d2*o0*o5 - 2*d2*o0*o8 - 4*d2*o0 - 2*d2*o2*o3 - 2*d2*o2*o6 - 6*d2*o2 + 2*d2*o3*o5 + 2*d2*o3*o8 + 2*d2*o5*o6 + 2*d2*o6*o8 - 2*d3*d5*d8 - d3*d8^2 - 2*d3*d8*o2 - 2*d3*d8*o5 - 2*d3*d8*o8 - d3*o2^2 + d3*o8^2 + 2*d3*o8 + d3 - d5^2*d6 - 2*d5*d6*d8 - 2*d5*d6*o2 - 2*d5*d6*o5 - 2*d5*d6*o8 - 2*d5*d8*o0 - 2*d5*d8*o3 - 2*d5*d8*o6 - 4*d5*d8 - 2*d5*o0*o2 - 2*d5*o2 + 2*d5*o6*o8 + 2*d5*o6 - d6*o2^2 + d6*o5^2 + 2*d6*o5 + d6 - 2*d8^2 - 2*d8*o0*o2 - 6*d8*o2 + 2*d8*o3*o5 + 2*d8*o3 - 2*d8*o5 - 4*d8*o8 - 2*d8 - 6*o0*o2^2 - 4*o0*o2*o5 - 4*o0*o2*o8 + 2*o0*o5*o8 + 2*o0*o5 + 2*o0*o8 + 2*o0 - 2*o2^2*o3 - 2*o2^2*o6 - 6*o2^2 + 2*o2*o3*o8 + 2*o2*o3 + 2*o2*o5*o6 - 4*o2*o5 + 2*o2*o6 - 2*o2*o8 - 2*o2 + 2*o5*o8 + 2*o5 + 2*o8^2 + 2*o8) = 0 ∧
    (-2*d0*d2 - d0*d5 - d0*d8 - 2*d0*o2 - 2*d0 - d2*d3 - d2*d6 - 2*d2*o0 - 4*d2 - 2*d3*d5 - d3*d8 - 4*d3*o2 - 2*d3*o5 - d5*d6 - 4*d5*o0 - 2*d5*o3 - 4*d5 - 2*d6*d8 - 4*d6*o2 - 2*d6*o8 - 4*d8*o0 - 2*d8*o6 - 2*d8 - 6*o0*o2 - 2*o0*o5 - 2*o0*o8 - 2*o2*o3 - 2*o2*o6 - 6*o2 + 2*o3*o5 + 2*o3*o8 + 2*o3 + 2*o5*o6 - 2*o5 + 2*o6*o8 + 2*o6 - 2) = 0 ∧
    (-d1^2*d4*d7 - d1^2*o1^2 - d1*d4^2*d7 - d1*d4*d7^2 - 2*d1*d4*d7*o1 - 2*d1*d4*d7*o4 - 2*d1*d4*d7*o7 - 2*d1*d4*d7 - d1*d4*o1^2 + d1*d4*o7^2 - d1*d4 - d1*d7*o1^2 + d1*d7*o4^2 - 2*d1*o1^3 - 2*d1*o1^2*o4 - 2*d1*o1^2*o7 - 2*d1*o1^2 + 2*d1*o1*o4*o7 - d4^2 - d4*d7 - 2*d4*o1 - 2*d4*o4 - 2*d4*o7 - 2*d4 + o4^2) = 0 ∧
    (-d1^2*d4*d8 - d1^2*d5*d7 - 2*d1^2*o1*o2 - 2*d1*d2*d4*d7 - 2*d1*d2*o1^2 - d1*d4^2*d8 - 2*d1*d4*d5*d7 - 2*d1*d4*d7*d8 - 2*d1*d4*d7*o2 - 2*d1*d4*d7*o5 - 2*d1*d4*d7*o8 - 2*d1*d4*d7 - 2*d1*d4*d8*o1 - 2*d1*d4*d8*o4 - 2*d1*d4*d8*o7 - 2*d1*d4*d8 - 2*d1*d4*o1*o2 + 2*d1*d4*o7*o8 - d1*d5*d7^2 - 2*d1*d5*d7*o1 - 2*d1*d5*d7*o4 - 2*d1*d5*d7*o7 - 2*d1*d5*d7 - d1*d5*o1^2 + d1*d5*o7^2 - d1*d5 - 2*d1*d7*o1*o2 + 2*d1*d7*o4*o5 - d1*d8*o1^2 + d1*d8*o4^2 - 6*d1*o1^2*o2 - 2*d1*o1^2*o5 - 2*d1*o1^2*o8 - 2*d1*o1^2 - 4*d1*o1*o2*o4 - 4*d1*o1*o2*o7 - 4*d1*o1*o2 + 2*d1*o1*o4*o8 + 2*d1*o1*o5*o7 + 2*d1*o2*o4*o7 - d2*d4^2*d7 - d2*d4*d7^2 - 2*d2*d4*d7*o1 - 2*d2*d4*d7*o4 - 2*d2*d4*d7*o7 - 2*d2*d4*d7 - d2*d4*o1^2 + d2*d4*o7^2 - d2*d4 - d2*d7*o1^2 + d2*d7*o4^2 - 2*d2*o1^3 - 2*d2*o1^2*o4 - 2*d2*o1^2*o7 - 2*d2*o1^2 + 2*d2*o1*o4*o7 - 2*d4*d5 - d4*d8 - 2*d4*o2 - 2*d4*o5 + 2*d4*o7 - 2*d4*o8 - 2*d4 - d5*d7 - 2*d5*o1 - 2*d5*o4 - 2*d5*o7 - 2*d5 + 2*o1*o4 + 2*o4*o5) = 0 ∧
    (-d1^2*d4 - d1^2*d7 - 2*d1^2*o1 - d1*d4^2 - 2*d1*d4*d7 - 4*d1*d4*o1 - 2*d1*d4*o4 - 4*d1*d4 - d1*d7^2 - 4*d1*d7*o1 - 2*d1*d7*o7 - 2*d1*d7 - 4*d1*o1^2 - 2*d1*o1*o4 - 2*d1*o1*o7 - 6*d1*o1 + d1*o4^2 + 2*d1*o4*o7 + d1*o7^2 - d1 - d4^2*d7 - 2*d4^2 - d4*d7^2 - 2*d4*d7*o1 - 2*d4*d7*o4 - 2*d4*d7*o7 - 4*d4*d7 - d4*o1^2 - 6*d4*o1 - 4*d4*o4 + d4*o7^2 - 2*d4*o7 - 4*d4 - d7*o1^2 - 2*d7*o1 + d7*o4^2 - d7 - 2*o1^3 - 2*o1^2*o4 - 2*o1^2*o7 - 6*o1^2 + 2*o1*o4*o7 - 2*o1*o4 - 4*o1*o7 - 6*o1 + 2*o4^2 + 2*o4*o7 - 2*o7 - 2) = 0 ∧
    (-d1^2*d5*d8 - d1^2*o2^2 - 2*d1*d2*d4*d8 - 2*d1*d2*d5*d7 - 4*d1*d2*o1*o2 - 2*d1*d4*d5*d8 - d1*d4*d8^2 - 2*d1*d4*d8*o2 - 2*d1*d4*d8*o5 - 2*d1*d4*d8*o8 - 2*d1*d4*d8 - d1*d4*o2^2 + d1*d4*o8^2 - d1*d5^2*d7 - 2*d1*d5*d7*d8 - 2*d1*d5*d7*o2 - 2*d1*d5*d7*o5 - 2*d1*d5*d7*o8 - 2*d1*d5*d7 - 2*d1*d5*d8*o1 - 2*d1*d5*d8*o4 - 2*d1*d5*d8*o7 - 2*d1*d5*d8 - 2*d1*d5*o1*o2 + 2*d1*d5*o7*o8 - d1*d7*o2^2 + d1*d7*o5^2 - 2*d1*d8*o1*o2 + 2*d1*d8*o4*o5 - 6*d1*o1*o2^2 - 4*d1*o1*o2*o5 - 4*d1*o1*o2*o8 - 4*d1*o1*o2 + 2*d1*o1*o5*o8 - 2*d1*o2^2*o4 - 2*d1*o2^2*o7 - 2*d1*o2^2 + 2*d1*o2*o4*o8 + 2*d1*o2*o5*o7 - d2^2*d4*d7 - d2^2*o1^2 - d2*d4^2*d8 - 2*d2*d4*d5*d7 - 2*d2*d4*d7*d8 - 2*d2*d4*d7*o2 - 2*d2*d4*d7*o5 - 2*d2*d4*d7*o8 - 2*d2*d4*d7 - 2*d2*d4*d8*o1 - 2*d2*d4*d8*o4 - 2*d2*d4*d8*o7 - 2*d2*d4*d8 - 2*d2*d4*o1*o2 + 2*d2*d4*o7*o8 - d2*d5*d7^2 - 2*d2*d5*d7*o1 - 2*d2*d5*d7*o4 - 2*d2*d5*d7*o7 - 2*d2*d5*d7 - d2*d5*o1^2 + d2*d5*o7^2 - d2*d5 - 2*d2*d7*o1*o2 + 2*d2*d7*o4*o5 - d2*d8*o1^2 + d2*d8*o4^2 - 6*d2*o1^2*o2 - 2*d2*o1^2*o5 - 2*d2*o1^2*o8 - 2*d2*o1^2 - 4*d2*o1*o2*o4 - 4*d2*o1*o2*o7 - 4*d2*o1*o2 + 2*d2*o1*o4*o8 + 2*d2*o1*o5*o7 + 2*d2*o2*o4*o7 + d4*d7 + 2*d4*o8 - d5^2 - d5*d8 - 2*d5*o2 - 2*d5*o5 + 2*d5*o7 - 2*d5*o8 - 2*d5 + o1^2 + 2*o1*o5 + 2*o2*o4 + o5^2) = 0 ∧
    (-d1^2*d5 - d1^2*d8 - 2*d1^2*o2 - 2*d1*d2*d4 - 2*d1*d2*d7 - 4*d1*d2*o1 - 2*d1*d4*d5 - 2*d1*d4*d8 - 4*d1*d4*o2 - 2*d1*d4*o5 - 2*d1*d4 - 2*d1*d5*d7 - 4*d1*d5*o1 - 2*d1*d5*o4 - 4*d1*d5 - 2*d1*d7*d8 - 4*d1*d7*o2 - 2*d1*d7*o8 - 2*d1*d7 - 4*d1*d8*o1 - 2*d1*d8*o7 - 2*d1*d8 - 8*d1*o1*o2 - 2*d1*o1*o5 - 2*d1*o1*o8 - 4*d1*o1 - 2*d1*o2*o4 - 2*d1*o2*o7 - 6*d1*o2 + 2*d1*o4*o5 + 2*d1*o4*o8 + 2*d1*o5*o7 + 2*d1*o7*o8 - d2*d4^2 - 2*d2*d4*d7 - 4*d2*d4*o1 - 2*d2*d4*o4 - 4*d2*d4 - d2*d7^2 - 4*d2*d7*o1 - 2*d2*d7*o7 - 2*d2*d7 - 4*d2*o1^2 - 2*d2*o1*o4 - 2*d2*o1*o7 - 6*d2*o1 + d2*o4^2 + 2*d2*o4*o7 + d2*o7^2 - d2 - d4^2*d8 - 2*d4*d5*d7 - 4*d4*d5 - 2*d4*d7*d8 - 2*d4*d7*o2 - 2*d4*d7*o5 - 2*d4*d7*o8 - 2*d4*d8*o1 - 2*d4*d8*o4 - 2*d4*d8*o7 - 4*d4*d8 - 2*d4*o1*o2 - 6*d4*o2 - 4*d4*o5 + 2*d4*o7*o8 + 2*d4*o7 - 2*d4*o8 - 2*d4 - d5*d7^2 - 2*d5*d7*o1 - 2*d5*d7*o4 - 2*d5*d7*o7 - 4*d5*d7 - d5*o1^2 - 6*d5*o1 - 4*d5*o4 + d5*o7^2 - 2*d5*o7 - 4*d5 - 2*d7*o1*o2 - 2*d7*o2 + 2*d7*o4*o5 + 2*d7*o4 - d8*o1^2 - 2*d8*o1 + d8*o4^2 - d8 - 6*o1^2*o2 - 2*o1^2*o5 - 2*o1^2*o8 - 4*o1*o2*o4 - 4*o1*o2*o7 - 12*o1*o2 + 2*o1*o4*o8 + 2*o1*o4 + 2*o1*o5*o7 - 2*o1*o5 + 2*o1*o7 - 4*o1*o8 - 2*o1 + 2*o2*o4*o7 - 2*o2*o4 - 4*o2*o7 - 6*o2 + 4*o4*o5 + 2*o4*o8 + 2*o4 + 2*o5*o7 + 2*o7 - 2*o8 - 2) = 0 ∧
    (-d1^2 - d1*d4 - d1*d7 - 2*d1*o1 - 4*d1 - d4^2 - d4*d7 - 4*d4*o1 - 2*d4*o4 - 2*d4 - d7^2 - 4*d7*o1 - 2*d7*o7 - 4*d7 - 3*o1^2 - 2*o1*o4 - 2*o1*o7 - 6*o1 + o4^2 + 2*o4*o7 + o7^2 - 2*o7 - 3) = 0 ∧
    (-2*d1*d2*d5*d8 - 2*d1*d2*o2^2 - d1*d5^2*d8 - d1*d5*d8^2 - 2*d1*d5*d8*o2 - 2*d1*d5*d8*o5 - 2*d1*d5*d8*o8 - 2*d1*d5*d8 - d1*d5*o2^2 + d1*d5*o8^2 - d1*d8*o2^2 + d1*d8*o5^2 - 2*d1*o2^3 - 2*d1*o2^2*o5 - 2*d1*o2^2*o8 - 2*d1*o2^2 + 2*d1*o2*o5*o8 - d2^2*d4*d8 - d2^2*d5*d7 - 2*d2^2*o1*o2 - 2*d2*d4*d5*d8 - d2*d4*d8^2 - 2*d2*d4*d8*o2 - 2*d2*d4*d8*o5 - 2*d2*d4*d8*o8 - 2*d2*d4*d8 - d2*d4*o2^2 + d2*d4*o8^2 - d2*d5^2*d7 - 2*d2*d5*d7*d8 - 2*d2*d5*d7*o2 - 2*d2*d5*d7*o5 - 2*d2*d5*d7*o8 - 2*d2*d5*d7 - 2*d2*d5*d8*o1 - 2*d2*d5*d8*o4 - 2*d2*d5*d8*o7 - 2*d2*d5*d8 - 2*d2*d5*o1*o2 + 2*d2*d5*o7*o8 - d2*d7*o2^2 + d2*d7*o5^2 - 2*d2*d8*o1*o2 + 2*d2*d8*o4*o5 - 6*d2*o1*o2^2 - 4*d2*o1*o2*o5 - 4*d2*o1*o2*o8 - 4*d2*o1*o2 + 2*d2*o1*o5*o8 - 2*d2*o2^2*o4 - 2*d2*o2^2*o7 - 2*d2*o2^2 + 2*d2*o2*o4*o8 + 2*d2*o2*o5*o7 + d4*d8 + d5*d7 + 2*d5*o8 + 2*o1*o2 + 2*o2*o5) = 0 ∧
    (-2*d1*d2*d5 - 2*d1*d2*d8 - 4*d1*d2*o2 - d1*d5^2 - 2*d1*d5*d8 - 4*d1*d5*o2 - 2*d1*d5*o5 - 2*d1*d5 - d1*d8^2 - 4*d1*d8*o2 - 2*d1*d8*o8 - 2*d1*d8 - 4*d1*o2^2 - 2*d1*o2*o5 - 2*d1*o2*o8 - 4*d1*o2 + d1*o5^2 + 2*d1*o5*o8 + d1*o8^2 - d2^2*d4 - d2^2*d7 - 2*d2^2*o1 - 2*d2*d4*d5 - 2*d2*d4*d8 - 4*d2*d4*o2 - 2*d2*d4*o5 - 2*d2*d4 - 2*d2*d5*d7 - 4*d2*d5*o1 - 2*d2*d5*o4 - 4*d2*d5 - 2*d2*d7*d8 - 4*d2*d7*o2 - 2*d2*d7*o8 - 2*d2*d7 - 4*d2*d8*o1 - 2*d2*d8*o7 - 2*d2*d8 - 8*d2*o1*o2 - 2*d2*o1*o5 - 2*d2*o1*o8 - 4*d2*o1 - 2*d2*o2*o4 - 2*d2*o2*o7 - 6*d2*o2 + 2*d2*o4*o5 + 2*d2*o4*o8 + 2*d2*o5*o7 + 2*d2*o7*o8 - 2*d4*d5*d8 - d4*d8^2 - 2*d4*d8*o2 - 2*d4*d8*o5 - 2*d4*d8*o8 - d4*o2^2 + d4*o8^2 + 2*d4*o8 + d4 - d5^2*d7 - 2*d5^2 - 2*d5*d7*d8 - 2*d5*d7*o2 - 2*d5*d7*o5 - 2*d5*d7*o8 - 2*d5*d8*o1 - 2*d5*d8*o4 - 2*d5*d8*o7 - 4*d5*d8 - 2*d5*o1*o2 - 6*d5*o2 - 4*d5*o5 + 2*d5*o7*o8 + 2*d5*o7 - 2*d5*o8 - 2*d5 - d7*o2^2 + d7*o5^2 + 2*d7*o5 + d7 - 2*d8*o1*o2 - 2*d8*o2 + 2*d8*o4*o5 + 2*d8*o4 - 6*o1*o2^2 - 4*o1*o2*o5 - 4*o1*o2*o8 + 2*o1*o5*o8 + 2*o1*o5 + 2*o1*o8 + 2*o1 - 2*o2^2*o4 - 2*o2^2*o7 - 6*o2^2 + 2*o2*o4*o8 + 2*o2*o4 + 2*o2*o5*o7 - 2*o2*o5 + 2*o2*o7 - 4*o2*o8 - 2*o2 + 2*o5^2 + 2*o5*o8 + 2*o5 + 2*o8) = 0 ∧
    (-2*d1*d2 - d1*d5 - d1*d8 - 2*d1*o2 - 2*d1 - d2*d4 - d2*d7 - 2*d2*o1 - 4*d2 - 2*d4*d5 - d4*d8 - 4*d4*o2 - 2*d4*o5 - d5*d7 - 4*d5*o1 - 2*d5*o4 - 2*d5 - 2*d7*d8 - 4*d7*o2 - 2*d7*o8 - 4*d8*o1 - 2*d8*o7 - 4*d8 - 6*o1*o2 - 2*o1*o5 - 2*o1*o8 - 2*o2*o4 - 2*o2*o7 - 6*o2 + 2*o4*o5 + 2*o4*o8 + 2*o4 + 2*o5*o7 + 2*o7*o8 + 2*o7 - 2*o8 - 2) = 0 ∧
    (-d2^2*d5*d8 - d2^2*o2^2 - d2*d5^2*d8 - d2*d5*d8^2 - 2*d2*d5*d8*o2 - 2*d2*d5*d8*o5 - 2*d2*d5*d8*o8 - 2*d2*d5*d8 - d2*d5*o2^2 + d2*d5*o8^2 - d2*d8*o2^2 + d2*d8*o5^2 - 2*d2*o2^3 - 2*d2*o2^2*o5 - 2*d2*o2^2*o8 - 2*d2*o2^2 + 2*d2*o2*o5*o8 + d5*d8 + o2^2) = 0 ∧
    (-d2^2*d5 - d2^2*d8 - 2*d2^2*o2 - d2*d5^2 - 2*d2*d5*d8 - 4*d2*d5*o2 - 2*d2*d5*o5 - 2*d2*d5 - d2*d8^2 - 4*d2*d8*o2 - 2*d2*d8*o8 - 2*d2*d8 - 4*d2*o2^2 - 2*d2*o2*o5 - 2*d2*o2*o8 - 4*d2*o2 + d2*o5^2 + 2*d2*o5*o8 + d2*o8^2 - d5^2*d8 - d5*d8^2 - 2*d5*d8*o2 - 2*d5*d8*o5 - 2*d5*d8*o8 - d5*o2^2 + d5*o8^2 + 2*d5*o8 + d5 - d8*o2^2 + d8*o5^2 + 2*d8*o5 + d8 - 2*o2^3 - 2*o2^2*o5 - 2*o2^2*o8 + 2*o2*o5*o8 + 2*o2*o5 + 2*o2*o8 + 2*o2) = 0 ∧
    (-d2^2 - d2*d5 - d2*d8 - 2*d2*o2 - 2*d2 - d5^2 - d5*d8 - 4*d5*o2 - 2*d5*o5 - d8^2 - 4*d8*o2 - 2*d8*o8 - 3*o2^2 - 2*o2*o5 - 2*o2*o8 + o5^2 + 2*o5*o8 + 2*o5 + o8^2 + 2*o8 + 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hq : certD400 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD400_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD400_add, certD400_four] at hq
    linear_combination (1/24 : ℂ) * hq
  · have hq : certD310 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD310_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD310_add, certD310_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD301 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD301_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD301_add, certD301_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD300 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD300_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD300_add, certD300_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD220 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD220_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD220_add, certD220_four] at hq
    linear_combination (1/4 : ℂ) * hq
  · have hq : certD211 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD211_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD211_add, certD211_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD210 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD210_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD210_add, certD210_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD202 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD202_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD202_add, certD202_four] at hq
    linear_combination (1/4 : ℂ) * hq
  · have hq : certD201 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD201_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD201_add, certD201_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD200 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD200_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD200_add, certD200_four] at hq
    linear_combination (1/4 : ℂ) * hq
  · have hq : certD130 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD130_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD130_add, certD130_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD121 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD121_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD121_add, certD121_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD120 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD120_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD120_add, certD120_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD112 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD112_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD112_add, certD112_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD111 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD111_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD111_add, certD111_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD110 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD110_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD110_add, certD110_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD103 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD103_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD103_add, certD103_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD102 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD102_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD102_add, certD102_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD101 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD101_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD101_add, certD101_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD040 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD040_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD040_add, certD040_four] at hq
    linear_combination (1/24 : ℂ) * hq
  · have hq : certD031 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD031_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD031_add, certD031_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD030 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD030_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD030_add, certD030_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD022 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD022_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD022_add, certD022_four] at hq
    linear_combination (1/4 : ℂ) * hq
  · have hq : certD021 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD021_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD021_add, certD021_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD020 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD020_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD020_add, certD020_four] at hq
    linear_combination (1/4 : ℂ) * hq
  · have hq : certD013 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD013_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD013_add, certD013_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD012 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD012_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD012_add, certD012_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD011 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD011_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD011_add, certD011_four] at hq
    linear_combination (1/2 : ℂ) * hq
  · have hq : certD004 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD004_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD004_add, certD004_four] at hq
    linear_combination (1/24 : ℂ) * hq
  · have hq : certD003 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD003_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD003_add, certD003_four] at hq
    linear_combination (1/6 : ℂ) * hq
  · have hq : certD002 (Matrix.permanent (fullStarMatrix d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8)) = 0 := by
      rw [h]
      exact certD002_nat 24
    rw [perm4_poly] at hq
    simp [fullStarMatrix, certD002_add, certD002_four] at hq
    linear_combination (1/4 : ℂ) * hq

end PEqualNP.Outside.L_gct_231_aux
