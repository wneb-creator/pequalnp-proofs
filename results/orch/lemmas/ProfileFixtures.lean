import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.ProfileFixtures

def singletonRow (r : Fin 7) (i : Fin 6) : Bool := r.val == i.val + 1

def signature (f : (Fin 6 → Bool) → Bool) : Nat :=
  ((List.finRange 7).map fun r => if f (singletonRow r) then 2 ^ r.val else 0).sum

def key (m : Nat) : Nat := min m (Nat.xor m 127)

def triangle (t : Fin 4) (z : Fin 6 → Bool) : Bool :=
  ![z 3 || z 4 || z 5, z 1 || z 2 || z 5,
    z 0 || z 2 || z 4, z 0 || z 1 || z 3] t

def matching (z : Fin 6 → Bool) : Bool :=
  (z 0 && z 5) || (z 1 && z 4) || (z 2 && z 3)

def combined (z : Fin 6 → Bool) (t : Fin 4 → Bool) : Bool :=
  matching z || (t 0 && triangle 0 z) || (t 1 && triangle 1 z) ||
    (t 2 && triangle 2 z) || (t 3 && triangle 3 z)

def arrange (z : Fin 6 → Bool) (t : Fin 4 → Bool) : Fin 10 → Bool :=
  ![t 0, z 5, t 1, z 2, z 3, z 4, z 0, z 1, t 2, t 3]

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

lemma matching_signature : signature matching = 0 := by decide +kernel

lemma triangle_signatures :
    (List.finRange 4).map (fun t => key (signature (triangle t))) = [15,51,42,22] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma petersen_decomposition : ∀ (z : Fin 6 → Bool) (t : Fin 4 → Bool),
    petersen (arrange z t) = combined z t := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.ProfileFixtures
