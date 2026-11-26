import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17531 : ∀ (x1 : List Bool) (x2 : ℕ), (List.foldr Nat.bit (0 : ℕ) x1).testBit x2 = x1.getD x2 Bool.false := by
  intro x1
  induction x1 with
  | nil => intro x2; simp [Nat.zero_testBit]
  | cons b t ih =>
    intro x2
    cases x2 with
    | zero => simp [Nat.testBit_bit_zero]
    | succ n => simp [Nat.testBit_bit_succ, ih]
