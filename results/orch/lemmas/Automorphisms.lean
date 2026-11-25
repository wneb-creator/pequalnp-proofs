import Mathlib

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 ||
    x 1 && x 2 ||
    x 2 && x 3 ||
    x 3 && x 4 ||
    x 4 && x 0 ||
    x 0 && x 5 ||
    x 1 && x 6 ||
    x 2 && x 7 ||
    x 3 && x 8 ||
    x 4 && x 9 ||
    x 5 && x 7 ||
    x 7 && x 9 ||
    x 9 && x 6 ||
    x 6 && x 8 ||
    x 8 && x 5


def relabel (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
    ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
    ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
    ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] v

lemma relabel_bijective : ∀ v : Fin 10, Function.Bijective (relabel v) := by
  intro v
  fin_cases v <;> decide

lemma relabel_last : ∀ v : Fin 10, relabel v 9 = v := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma relabel_edge : ∀ (v : Fin 10) (x : Fin 10 → Bool), edge (x ∘ relabel v) = edge x := by
  intro v x
  fin_cases v <;> dsimp [edge, relabel, Function.comp_def] <;> ac_rfl

end PEqualNP.Outside.L_meta_2373
