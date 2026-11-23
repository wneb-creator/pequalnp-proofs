import Mathlib

namespace PEqualNP.Outside.Meta971Strategy

def pathTarget (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

def firstOr (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 3 && x 4)

def secondOr (x : Fin 5 → Bool) : Bool := firstOr x || x 2

def leftMeet (x : Fin 5 → Bool) : Bool := x 1 && secondOr x

def rightMeet (x : Fin 5 → Bool) : Bool := x 3 && secondOr x

def edgeInput (e : Fin 4) (v : Fin 5) : Bool :=
  decide (v.val = e.val ∨ v.val = e.val + 1)

theorem all_three_safe :
    (∀ x, firstOr x = true → pathTarget x = true) ∧
    (∀ x, leftMeet x = true → pathTarget x = true) ∧
    (∀ x, rightMeet x = true → pathTarget x = true) := by
  decide +kernel

theorem exact_edge_families :
    (∀ e : Fin 4, firstOr (edgeInput e) = decide (e = 0 ∨ e = 3)) ∧
    (∀ e : Fin 4, leftMeet (edgeInput e) = decide (e = 0 ∨ e = 1)) ∧
    (∀ e : Fin 4, rightMeet (edgeInput e) = decide (e = 2 ∨ e = 3)) := by
  decide +kernel

theorem final_union_correct :
    ∀ x, (leftMeet x || rightMeet x) = pathTarget x := by
  decide +kernel

def pathAdj (u v : Fin 5) : Bool :=
  decide (u.val + 1 = v.val ∨ v.val + 1 = u.val)

theorem path_has_no_four_cycle :
    ∀ a b c d : Fin 5, a ≠ c → b ≠ d →
      ¬ (pathAdj a b = true ∧ pathAdj b c = true ∧
        pathAdj c d = true ∧ pathAdj d a = true) := by
  decide +kernel

end PEqualNP.Outside.Meta971Strategy
