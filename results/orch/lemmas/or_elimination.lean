import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.OrElimination

/- This refutes a proposed induction lemma about arbitrary compact programs.
   It is not a refutation of L-meta-1031: this program is not minimum. -/

def applyOr (cut : Option (Fin 5 × Bool)) (j : Fin 5) (a b : Bool) : Bool :=
  match cut with
  | none => a || b
  | some (i, side) => if i = j then (if side then b else a) else a || b

def run (cut : Option (Fin 5 × Bool)) (x : Fin 5 → Bool) : Bool :=
  let g0 := applyOr cut 0 (x 2) (x 4)
  let g1 := applyOr cut 1 (x 1) (x 4)
  let g2 := applyOr cut 2 (x 3 && g0) (x 0 && g1)
  let g3 := applyOr cut 3 (x 2 && g0) (g1 && g2)
  let g4 := applyOr cut 4 (g0 && g2) (x 1 && g1 && g3)
  g3 && g4

def edgeInput (i : Fin 5) : Fin 5 → Bool := fun v => decide (v = i ∨ v = i + 1)

abbrev adjacent (u v : Fin 5) : Prop := u + 1 = v ∨ v + 1 = u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem computes_cycle : ∀ x : Fin 5 → Bool,
    run none x = decide (∃ u v : Fin 5, adjacent u v ∧ x u = true ∧ x v = true) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem each_replacement_loses_two : ∀ (j : Fin 5) (side : Bool),
    ∃ i k : Fin 5, i ≠ k ∧
      run none (edgeInput i) = true ∧ run none (edgeInput k) = true ∧
      run (some (j, side)) (edgeInput i) = false ∧
      run (some (j, side)) (edgeInput k) = false := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem no_triangle : ∀ a b c : Fin 5,
    ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ adjacent a b ∧ adjacent b c ∧ adjacent c a) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem no_four_cycle : ∀ a b c d : Fin 5,
    ¬ (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      adjacent a b ∧ adjacent b c ∧ adjacent c d ∧ adjacent d a) := by
  decide

end PEqualNP.Outside.L_meta_1031_aux.OrElimination
