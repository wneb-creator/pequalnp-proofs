import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

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


lemma permanent_star {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.permanent (!![1 + d, 1 + a, 1 + b, 1 + c;
                         1 + a, 1, 1, 1;
                         1 + b, 1, 1, 1;
                         1 + c, 1, 1, 1] : Matrix (Fin 4) (Fin 4) R) =
      24 + 6 * d + 12 * (a + b + c) + 2 * (a + b + c) ^ 2 := by
  rw [permanent_four]
  simp
  ring

end PEqualNP.Outside.L_gct_231
