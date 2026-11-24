import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451.StarEssentialObstruction

def earlier (z : Fin 6 → Bool) (i : Fin 10) : Bool :=
  ![z 0, z 1, z 2, z 3, z 4, z 5, z 3 || z 5, (z 3 || z 5) || z 4, false, true] i

def candidate (isAnd : Bool) (a b : Fin 10) (z : Fin 6 → Bool) : Bool :=
  if isAnd then earlier z a && earlier z b else earlier z a || earlier z b

def later (z : Fin 6 → Bool) : Bool := (z 3 || z 1) || z 4

def output (gate : (Fin 6 → Bool) → Bool) (z : Fin 6 → Bool) : Bool :=
  (gate z && later z) || (z 1 && z 5)

def target (z : Fin 6 → Bool) : Bool := (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 5)

def pair (p l : Fin 3) (i : Fin 6) : Bool := decide (i.val = p.val ∨ i.val = 3 + l.val)

def incidence (p l : Fin 3) : Prop := (p = 0 ∧ (l = 0 ∨ l = 1)) ∨ (p = 1 ∧ l = 2)

def singleton (i : Fin 6) : Bool := decide (i = 0)

lemma original_correct : ∀ z : Fin 6 → Bool,
    output (candidate true 0 7) z = target z := by
  decide

lemma target_is_incidence : ∀ z : Fin 6 → Bool, target z = true ↔
    ∃ p l : Fin 3, incidence p l ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true := by
  unfold incidence target
  decide

lemma no_four_cycle : ∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
    ¬ (incidence p l ∧ incidence p l' ∧ incidence p' l ∧ incidence p' l') := by
  unfold incidence
  decide

lemma critical_edges_are_star : ∀ p l : Fin 3,
    (incidence p l ∧ output (candidate true 0 7) (pair p l) = true ∧
      output (fun _ => false) (pair p l) = false) ↔ p = 0 ∧ (l = 0 ∨ l = 1) := by
  unfold incidence
  decide

lemma center_replacement_stalls :
    candidate true 0 7 singleton = false ∧ earlier singleton 0 = true ∧ earlier singleton 7 = false ∧
      (∀ z : Fin 6 → Bool, (z 0 && earlier z 7) = candidate true 0 7 z) := by
  decide

lemma no_earlier_neighborhood : ∀ i : Fin 10,
    ¬ ∀ z : Fin 6 → Bool, earlier z i = (z 3 || z 4) := by
  decide

lemma every_one_gate_replacement_stays_dirty :
    ∀ (isAnd : Bool) (a b : Fin 10),
      (∀ z : Fin 6 → Bool, output (candidate isAnd a b) z = target z) →
      isAnd = true ∧ candidate isAnd a b (pair 0 2) = true := by
  decide

end PEqualNP.Outside.L_meta_3451.StarEssentialObstruction
