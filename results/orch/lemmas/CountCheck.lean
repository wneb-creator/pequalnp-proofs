import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.CountCheck
open PEqualNP.CircuitLowerBounds
namespace Extended

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

end Extended

lemma seventeen_plus_not (C : Circuit) (floor : 17 ≤ C.gates.countP (fun g => !Extended.isNot g)) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        Extended.isNot := by
    funext g
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl
  have count : PEqualNP.NotBracket.notCount C = C.gates.countP Extended.isNot := by
    rw [PEqualNP.NotBracket.notCount, sameNot, List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have total := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at total
  rw [count]
  change 17 + C.gates.countP Extended.isNot ≤ C.gates.length
  omega

lemma at_most_two_not (C : Circuit) (floor : 17 ≤ C.gates.countP (fun g => !Extended.isNot g))
    (small : C.size ≤ 19) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  have lower := seventeen_plus_not C floor
  omega

end PEqualNP.Outside.L_meta_2592.CountCheck
