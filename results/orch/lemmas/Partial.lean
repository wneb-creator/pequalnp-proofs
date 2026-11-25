import Mathlib
import PEqualNP.Defs

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
      (∀ p ∈ petersenEdges, (x p.1 || x p.2) = true) → 6 ≤ (petersenSupport x).card := by
  decide

lemma petersen_star_cover_cost (x : Fin 10 → Bool)
    (h : ∀ p ∈ petersenEdges, (x p.1 || x p.2) = true) :
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

lemma petersen_edge_implicant (p : Fin 10 × Fin 10) (hp : p ∈ petersenEdges)
    (x : Fin 10 → Bool) (h : (x p.1 && x p.2) = true) : petersenValue x = true := by
  simp only [petersenEdges, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases Bool.and_eq_true_iff.mp h with ⟨ha, hb⟩
    simp_all [petersenValue]

def petersenSelectedEdges (x : Fin 10 → Bool) : Finset (Fin 10 × Fin 10) :=
  petersenEdges.filter (fun p => (x p.1 && x p.2) = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersen_five_vertices_two_edges :
    ∀ x : Fin 10 → Bool,
      5 ≤ (petersenSupport x).card → 2 ≤ (petersenSelectedEdges x).card := by
  decide

lemma petersen_delete_edge_independence (e : Fin 10 × Fin 10) (x : Fin 10 → Bool)
    (h : ∀ p ∈ petersenEdges.erase e, (x p.1 && x p.2) = false) :
    (petersenSupport x).card ≤ 4 := by
  have hsub : petersenSelectedEdges x ⊆ {e} := by
    intro p hp
    obtain ⟨hpEdge, hpValue⟩ := Finset.mem_filter.mp hp
    have he : p = e := by
      by_contra hne
      have hf := h p (Finset.mem_erase.mpr ⟨hne, hpEdge⟩)
      rw [hf] at hpValue
      contradiction
    exact Finset.mem_singleton.mpr he
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  by_contra! hb
  have ht := petersen_five_vertices_two_edges x (by omega)
  omega

def petersenCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩, ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩, ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩, ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩, ⟨.or, [28, 24]⟩], 29⟩

lemma petersenCircuit_size : petersenCircuit.size = 20 := by rfl

lemma petersenCircuit_fanInTwo : PEqualNP.MetaComplexity.FanInTwo petersenCircuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, petersenCircuit]

lemma petersenCircuit_no_not :
    ∀ g ∈ petersenCircuit.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  simp [petersenCircuit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersenCircuit_correct :
    ∀ x : Fin 10 → Bool, petersenCircuit.eval (List.ofFn x) = petersenValue x := by
  decide

lemma petersen_has_size_twenty : PEqualNP.MetaComplexity.HasCircuitSize 10 petersenValue 20 := by
  exact ⟨petersenCircuit, petersenCircuit_fanInTwo, le_of_eq petersenCircuit_size,
    petersenCircuit_correct⟩

end PEqualNP.Outside.L_meta_2592
