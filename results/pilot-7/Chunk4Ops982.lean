import Chunk4And982
import Chunk4Arithmetic982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4

def safeOr (fuel a b : Nat) : Nat := a + b - safeAnd fuel a b

def safeXor (fuel a b : Nat) : Nat := a + b - 2 * safeAnd fuel a b

theorem safeOr_eq (fuel a b : Nat) : safeOr fuel a b = a ||| b := by
  unfold safeOr
  rw [safeAnd_eq, (add_bitwise a b).1]
  exact Nat.add_sub_cancel _ _

theorem safeXor_eq (fuel a b : Nat) : safeXor fuel a b = a ^^^ b := by
  unfold safeXor
  rw [safeAnd_eq, (add_bitwise a b).2]
  exact Nat.add_sub_cancel _ _

end PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4
