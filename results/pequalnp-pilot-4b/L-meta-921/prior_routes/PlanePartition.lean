import Mathlib

namespace PriorRoutes.Meta921

def planeLine (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

theorem point_degree : ∀ p : Fin 13,
    (Finset.univ.filter (fun w => p ∈ planeLine w)).card = 4 := by
  decide

theorem no_two_two_partition (A : Finset (Fin 13)) :
    ¬ ∀ w, (A ∩ planeLine w).card = 2 := by
  intro balanced
  have count := Finset.card_mul_eq_card_mul
    (s := (Finset.univ : Finset (Fin 13))) (t := A)
    (m := 2) (n := 4) (fun w p => p ∈ planeLine w)
    (fun w _ => show (A.bipartiteAbove (fun w p => p ∈ planeLine w) w).card = 2 from by
      convert balanced w using 1
      congr 1)
    (fun p _ => show
      (Finset.univ.bipartiteBelow (fun w p => p ∈ planeLine w) p).card = 4 from
      point_degree p)
  norm_num at count
  omega

end PriorRoutes.Meta921
