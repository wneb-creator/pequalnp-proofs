import Mathlib

namespace PEqualNP.Outside.L_meta_2592

def petersenEdges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)}

def petersenValue (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def petersenSupport (x : Fin 10 → Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => x i = true)

def petersenAdjacent (i j : Fin 10) : Prop :=
  (i, j) ∈ petersenEdges ∨ (j, i) ∈ petersenEdges

def petersenNeighbor (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | _ => 4

lemma petersen_edge_count : petersenEdges.card = 15 := by decide

set_option synthInstance.maxSize 100000 in
lemma petersen_triangle_free :
    ∀ a b c : Fin 10,
      petersenAdjacent a b → petersenAdjacent b c → ¬petersenAdjacent c a := by
  unfold petersenAdjacent
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma petersen_square_free :
    ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
      petersenAdjacent a b → petersenAdjacent b c →
      petersenAdjacent c d → ¬petersenAdjacent d a := by
  unfold petersenAdjacent
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersen_independent_set_bound :
    ∀ x : Fin 10 → Bool, petersenValue x = false → (petersenSupport x).card ≤ 4 := by
  decide

lemma petersen_independent_set_witness :
    let x : Fin 10 → Bool := fun i => decide (i ∈ ({0, 2, 8, 9} : Finset (Fin 10)))
    petersenValue x = false ∧ (petersenSupport x).card = 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersen_vertex_cover_bound :
    ∀ x : Fin 10 → Bool,
      (∀ p ∈ petersenEdges, x p.1 || x p.2 = true) → 6 ≤ (petersenSupport x).card := by
  decide

lemma petersen_star_cover_cost (x : Fin 10 → Bool)
    (h : ∀ p ∈ petersenEdges, x p.1 || x p.2 = true) :
    20 ≤ petersenEdges.card + (petersenSupport x).card - 1 := by
  have hc := petersen_vertex_cover_bound x h
  rw [petersen_edge_count]
  omega

lemma petersen_essential_witnesses :
    ∀ i : Fin 10,
      petersenValue (fun j => decide (j = petersenNeighbor i)) = false ∧
      petersenValue (fun j => decide (j = petersenNeighbor i ∨ j = i)) = true := by
  decide

lemma petersen_all_inputs_essential (i : Fin 10) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ petersenValue x ≠ petersenValue y := by
  refine ⟨fun j => decide (j = petersenNeighbor i),
    fun j => decide (j = petersenNeighbor i ∨ j = i), ?_, ?_⟩
  · intro j h
    simp only [h, or_false]
  · rw [(petersen_essential_witnesses i).1, (petersen_essential_witnesses i).2]
    decide

end PEqualNP.Outside.L_meta_2592
