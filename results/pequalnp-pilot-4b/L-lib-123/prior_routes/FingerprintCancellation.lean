import Mathlib

namespace PriorRoutes

/-- The endpoint hash can accept an invalid pop/push sequence without any
polynomial collision: the errors cancel identically. -/
theorem wrong_pop_push_cancels {F : Type} [Field F] (r : F) (hr : r ≠ 0) :
    ((((0 : F) - 1) / r) * r + 1 - 0) / r = 0 := by
  field_simp
  ring

def checkedPop (expected : Bool) : List Bool → Option (List Bool)
  | [] => none
  | actual :: tail => if actual = expected then some tail else none

def dishonestTrace (stack : List Bool) : Option (List Bool) := do
  let stack ← checkedPop true (false :: stack)
  checkedPop false (true :: stack)

theorem dishonestTrace_rejects (stack : List Bool) : dishonestTrace stack = none := by
  simp [dishonestTrace, checkedPop]

/-- With the genuine read values, the same push/pop control skeleton is legal. -/
def honestTrace (stack : List Bool) : Option (List Bool) := do
  let stack ← checkedPop false (false :: stack)
  checkedPop false (false :: stack)

theorem honestTrace_accepts (stack : List Bool) : honestTrace stack = some stack := by
  simp [honestTrace, checkedPop]

end PriorRoutes
