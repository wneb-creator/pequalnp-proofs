import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4]

lemma neighbor_ne (i : Fin 10) : neighbor i ≠ i := by
  revert i
  decide +kernel

lemma edge_zero : edge (fun _ => false) = false := rfl

lemma edge_one : edge (fun _ => true) = true := rfl

lemma edge_single (i : Fin 10) : edge (fun j => decide (j = i)) = false := by
  revert i
  decide +kernel

lemma edge_neighbor_pair (i : Fin 10) :
    edge (fun j => decide (j = i ∨ j = neighbor i)) = true := by
  revert i
  decide +kernel

lemma edge_essential (i : Fin 10) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ x i = false ∧ y i = true ∧
      edge x = false ∧ edge y = true := by
  refine ⟨(fun j => decide (j = neighbor i)),
    (fun j => decide (j = i ∨ j = neighbor i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp [hj]
  · simp [Ne.symm (neighbor_ne i)]
  · simp
  · exact edge_single (neighbor i)
  · exact edge_neighbor_pair i

def pairInput (p q : Fin 10) (a b : Bool) (r : Fin 11) : Fin 10 → Bool :=
  fun j => if j = p then a else if j = q then b else decide (j.val = r.val)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pair_cofactors_separate :
    ∀ p q : Fin 10, p ≠ q → ∀ a b c d : Bool, (a, b) ≠ (c, d) →
      ∃ r : Fin 11, edge (pairInput p q a b r) ≠ edge (pairInput p q c d r) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux
