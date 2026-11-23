import Mathlib

namespace PEqualNP.Outside.L_meta_984.MaskStage

def stage (lo keep d w : Nat) : Nat :=
  ((w &&& lo) <<< d) ||| ((w >>> d) &&& lo) ||| (w &&& keep)

theorem stage_bit (lo keep d i w : Nat)
    (hshift : (lo &&& (lo <<< d)) = 0)
    (hkeep : (lo &&& keep) = 0)
    (hshiftkeep : ((lo <<< d) &&& keep) = 0) :
    (stage lo keep d w).testBit i =
      (if lo.testBit i then w.testBit (d+i)
       else if (lo <<< d).testBit i then w.testBit (i-d)
       else if keep.testBit i then w.testBit i else false) := by
  have h₁ := congrArg (fun v : Nat => v.testBit i) hshift
  have h₂ := congrArg (fun v : Nat => v.testBit i) hkeep
  have h₃ := congrArg (fun v : Nat => v.testBit i) hshiftkeep
  simp only [Nat.testBit_and, Nat.zero_testBit] at h₁ h₂ h₃
  simp only [stage,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem stage_hom (lo keep d : Nat)
    (hshift : (lo &&& (lo <<< d)) = 0)
    (hkeep : (lo &&& keep) = 0)
    (hshiftkeep : ((lo <<< d) &&& keep) = 0) (a b : Nat) :
    stage lo keep d (a &&& b) = (stage lo keep d a &&& stage lo keep d b) ∧
    stage lo keep d (a ||| b) = (stage lo keep d a ||| stage lo keep d b) ∧
    stage lo keep d (a ^^^ b) = (stage lo keep d a ^^^ stage lo keep d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
      stage_bit lo keep d i _ hshift hkeep hshiftkeep] <;>
    split_ifs <;> simp

end PEqualNP.Outside.L_meta_984.MaskStage
