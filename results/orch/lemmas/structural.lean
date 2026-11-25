import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_2592

def structuralEdge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def structuralRotate : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]

def structuralExchange : Fin 10 → Fin 10 := ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3]

lemma structural_rotate_edge (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralRotate) = structuralEdge x := by
  dsimp [structuralEdge, structuralRotate, Function.comp_def]
  ac_rfl

lemma structural_exchange_edge (x : Fin 10 → Bool) :
    structuralEdge (x ∘ structuralExchange) = structuralEdge x := by
  dsimp [structuralEdge, structuralExchange, Function.comp_def]
  ac_rfl

lemma structural_rotate_bijective : Function.Bijective structuralRotate := by decide

lemma structural_exchange_bijective : Function.Bijective structuralExchange := by decide

def structuralExtend (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, b]

def structuralDeletedEdge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

lemma structural_cofactor_false (x : Fin 9 → Bool) :
    structuralEdge (structuralExtend x false) = structuralDeletedEdge x := by
  simp [structuralEdge, structuralExtend, structuralDeletedEdge]

lemma structural_cofactor_true (x : Fin 9 → Bool) :
    structuralEdge (structuralExtend x true) =
      (x 4 || x 7 || x 6 ||
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 8 ||
        x 8 && x 5 || x 5 && x 0) := by
  cases h4 : x 4 <;> cases h6 : x 6 <;> cases h7 : x 7 <;>
    simp [structuralEdge, structuralExtend, h4, h6, h7, Bool.or_assoc,
      Bool.or_comm, Bool.or_left_comm, Bool.and_comm]

def structuralNeighbor : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]

lemma structural_each_input_essential : ∀ i : Fin 10,
    structuralEdge (fun j => decide (j = structuralNeighbor i)) = false ∧
    structuralEdge (fun j => decide (j = i ∨ j = structuralNeighbor i)) = true := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma structural_independence_number :
    ∀ x : Fin 10 → Bool, structuralEdge x = false →
      (Finset.univ.filter fun i => x i = true).card ≤ 4 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592
