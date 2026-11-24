import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451.UncrossingObstruction

def earlier (z : Fin 4 → Bool) (i : Fin 8) : Bool :=
  ![z 0, z 1, z 2, z 3, z 0 || z 1, z 2 || z 3, false, true] i

def candidate (isAnd : Bool) (a b : Fin 8) (z : Fin 4 → Bool) : Bool :=
  if isAnd then earlier z a && earlier z b else earlier z a || earlier z b

def later (z : Fin 4 → Bool) : Bool := (z 0 || z 3) && (z 1 || z 2)

def matching (z : Fin 4 → Bool) : Bool := (z 0 && z 2) || (z 1 && z 3)

def nonedge (i : Fin 4) : Bool := decide (i = 0 ∨ i = 3)

lemma original_correct : ∀ z : Fin 4 → Bool,
    (candidate true 4 5 z && later z) = matching z := by
  decide

lemma every_one_gate_replacement_stays_dirty :
    ∀ (isAnd : Bool) (a b : Fin 8),
      (∀ z : Fin 4 → Bool, (candidate isAnd a b z && later z) = matching z) →
      isAnd = true ∧ candidate isAnd a b nonedge = true := by
  decide

lemma original_accepts_two_edges :
    candidate true 4 5 (fun i => decide (i = 0 ∨ i = 2)) = true ∧
    candidate true 4 5 (fun i => decide (i = 1 ∨ i = 3)) = true := by
  decide

end PEqualNP.Outside.L_meta_3451.UncrossingObstruction
