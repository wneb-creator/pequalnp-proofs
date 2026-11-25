import PEqualNP.Outside.L_gct_231

namespace PEqualNP.Outside.L_gct_231_aux.Coeff

noncomputable def affine3 (a b c : ℂ) : MvPolynomial (Fin 3) ℂ :=
  1 + MvPolynomial.C a * MvPolynomial.X 0 +
    MvPolynomial.C b * MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 2

noncomputable def fullStarMatrix (d0 d1 d2 d3 d4 d5 d6 d7 d8 o0 o1 o2 o3 o4 o5 o6 o7 o8 : ℂ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  !![affine3 d0 d1 d2, affine3 1 0 0, affine3 0 1 0, affine3 0 0 1;
    affine3 1 0 0, affine3 d3 d4 d5, affine3 o0 o1 o2, affine3 o3 o4 o5;
    affine3 0 1 0, affine3 o0 o1 o2, affine3 d6 d7 d8, affine3 o6 o7 o8;
    affine3 0 0 1, affine3 o3 o4 o5, affine3 o6 o7 o8, affine3 (-(d0+d3+d6+2*(1+o0+o3+o6)))
      (-(d1+d4+d7+2*(1+o1+o4+o7)))
      (-(d2+d5+d8+2*(1+o2+o5+o8)))]

end PEqualNP.Outside.L_gct_231_aux.Coeff

namespace PEqualNP.Outside.L_gct_231_aux

theorem linear_entry_expansion
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) (v : Fin 3 → ℂ) (i j : Fin 4) :
    F v (i,j) = F (Pi.single 0 1) (i,j) * v 0 +
      F (Pi.single 1 1) (i,j) * v 1 + F (Pi.single 2 1) (i,j) * v 2 := by
  rw [linear_map_coordinate_expansion F v]
  simp [Fin.sum_univ_succ, smul_eq_mul]
  ring

noncomputable def starFromFamily
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ)) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3) ℂ) :=
  Coeff.fullStarMatrix
    (F (Pi.single 0 1) (0,0)) (F (Pi.single 1 1) (0,0)) (F (Pi.single 2 1) (0,0))
    (F (Pi.single 0 1) (1,1)) (F (Pi.single 1 1) (1,1)) (F (Pi.single 2 1) (1,1))
    (F (Pi.single 0 1) (2,2)) (F (Pi.single 1 1) (2,2)) (F (Pi.single 2 1) (2,2))
    (F (Pi.single 0 1) (1,2)) (F (Pi.single 1 1) (1,2)) (F (Pi.single 2 1) (1,2))
    (F (Pi.single 0 1) (1,3)) (F (Pi.single 1 1) (1,3)) (F (Pi.single 2 1) (1,3))
    (F (Pi.single 0 1) (2,3)) (F (Pi.single 1 1) (2,3)) (F (Pi.single 2 1) (2,3))

set_option maxHeartbeats 4000000 in
theorem normalized_star_formal_identity
    (F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ))
    (hs : ∀ v, ∀ i j : Fin 4, F v (i,j) = F v (j,i))
    (hp : ∀ v, Matrix.permanent
      (Matrix.of fun i j : Fin 4 => (1 : ℂ) + F v (i,j)) = 24)
    (h01 : ∀ v, F v (0,1) = v 0)
    (h02 : ∀ v, F v (0,2) = v 1)
    (h03 : ∀ v, F v (0,3) = v 2) :
    Matrix.permanent (starFromFamily F) = (24 : MvPolynomial (Fin 3) ℂ) := by
  apply MvPolynomial.funext
  intro v
  have hsum : ∑ i : Fin 4, ∑ j : Fin 4, F v (i,j) = 0 := by
    apply total_entry_sum_zero
    intro z
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using hp (z • v)
  have hd := diagonal33_of_total_entry_sum_zero (F v) (hs v) hsum
  have he : (fun i j : Fin 4 => MvPolynomial.eval v (starFromFamily F i j)) =
      Matrix.of (fun i j : Fin 4 => (1 : ℂ) + F v (i,j)) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [starFromFamily, Coeff.fullStarMatrix, Coeff.affine3, h01, h02, h03,
      hs v 1 0, hs v 2 0, hs v 3 0, hs v 2 1, hs v 3 1, hs v 3 2, hd]
    all_goals simp only [linear_entry_expansion F v]
    all_goals ring
  have hh := congrArg Matrix.permanent he
  have hx := hh.trans (hp v)
  simpa [Matrix.permanent] using hx

end PEqualNP.Outside.L_gct_231_aux

