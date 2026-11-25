import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

noncomputable def relabel (p : Equiv.Perm (Fin 4)) :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun t ij := t (p.symm ij.1, p.symm ij.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem relabel_symmetric (p : Equiv.Perm (Fin 4))
    (t : Fin 4 × Fin 4 → ℂ)
    (hs : ∀ i j : Fin 4, t (i,j) = t (j,i)) :
    ∀ i j : Fin 4, relabel p t (i,j) = relabel p t (j,i) := by
  intro i j
  exact hs (p.symm i) (p.symm j)

theorem relabel_permanent (p : Equiv.Perm (Fin 4))
    (t : Fin 4 × Fin 4 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + relabel p t (i,j)) =
      Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i,j)) := by
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j => (1 : ℂ) + t (i,j)
  change (M.submatrix p.symm p.symm).permanent = M.permanent
  calc
    _ = ((M.submatrix p.symm id).submatrix id p.symm).permanent := rfl
    _ = (M.submatrix p.symm id).permanent := Matrix.permanent_permute_rows p.symm _
    _ = M.permanent := Matrix.permanent_permute_cols p.symm M

theorem relabel_injective (p : Equiv.Perm (Fin 4)) : Function.Injective (relabel p) := by
  intro t u h
  funext ij
  have he := congrFun h (p ij.1, p ij.2)
  simpa [relabel] using he

end PEqualNP.Outside.L_gct_231_aux
