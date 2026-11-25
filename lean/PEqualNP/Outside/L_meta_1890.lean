import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graphEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def coversEdges (s : Finset (Fin 10)) : Prop :=
  ∀ e ∈ graphEdges, e.1 ∈ s ∨ e.2 ∈ s

lemma cover_edge_nat (s : Finset (Fin 10)) (hs : coversEdges s)
    (a b : Fin 10) (he : (a, b) ∈ graphEdges) :
    1 ≤ (if a ∈ s then 1 else 0) + (if b ∈ s then 1 else 0) := by
  rcases hs (a, b) he with h | h <;> simp [h]

lemma every_cover_has_six (s : Finset (Fin 10)) (hs : coversEdges s) : 6 ≤ s.card := by
  have h01 := cover_edge_nat s hs 0 1 (by decide)
  have h12 := cover_edge_nat s hs 1 2 (by decide)
  have h23 := cover_edge_nat s hs 2 3 (by decide)
  have h34 := cover_edge_nat s hs 3 4 (by decide)
  have h40 := cover_edge_nat s hs 4 0 (by decide)
  have h57 := cover_edge_nat s hs 5 7 (by decide)
  have h79 := cover_edge_nat s hs 7 9 (by decide)
  have h96 := cover_edge_nat s hs 9 6 (by decide)
  have h68 := cover_edge_nat s hs 6 8 (by decide)
  have h85 := cover_edge_nat s hs 8 5 (by decide)
  have hcard : s.card = ∑ i : Fin 10, if i ∈ s then 1 else 0 := by simp
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hcard
  change s.card = (if (0 : Fin 10) ∈ s then 1 else 0) + ((if (1 : Fin 10) ∈ s then 1 else 0) + ((if (2 : Fin 10) ∈ s then 1 else 0) + ((if (3 : Fin 10) ∈ s then 1 else 0) + ((if (4 : Fin 10) ∈ s then 1 else 0) + ((if (5 : Fin 10) ∈ s then 1 else 0) + ((if (6 : Fin 10) ∈ s then 1 else 0) + ((if (7 : Fin 10) ∈ s then 1 else 0) + ((if (8 : Fin 10) ∈ s then 1 else 0) + ((if (9 : Fin 10) ∈ s then 1 else 0) + (0)))))))))) at hcard
  omega

lemma six_vertex_cover : coversEdges {1, 3, 4, 5, 6, 7} := by
  unfold coversEdges graphEdges
  decide

lemma six_vertex_cover_card : ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)).card = 6 := by
  decide

lemma star_factoring_cost (s : Finset (Fin 10)) (hs : coversEdges s) :
    20 ≤ graphEdges.length + s.card - 1 := by
  have h := every_cover_has_six s hs
  change 20 ≤ 15 + s.card - 1
  omega

def graphValue (x : Fin 10 → Bool) : Bool :=
  graphEdges.any (fun e => x e.1 && x e.2)

def baseline : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [3, 15]⟩,
    ⟨.or, [0, 9]⟩, ⟨.and, [4, 17]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [19, 8]⟩, ⟨.and, [5, 20]⟩,
    ⟨.or, [9, 8]⟩, ⟨.and, [6, 22]⟩,
    ⟨.or, [2, 9]⟩, ⟨.and, [7, 24]⟩,
    ⟨.or, [13, 16]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [27, 21]⟩,
    ⟨.or, [28, 23]⟩, ⟨.or, [29, 25]⟩], 30⟩

lemma baseline_size : baseline.size = 20 := rfl

lemma baseline_fanin : FanInTwo baseline := by
  intro g hg
  simp only [baseline, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma baseline_correct : ∀ x : Fin 10 → Bool,
    baseline.eval (List.ofFn x ++ [x 0 && x 2]) = graphValue x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    simp [List.ofFn_succ]
  rw [hx]
  dsimp only [baseline, Circuit.eval, Circuit.wires]
  simp only [List.cons_append, List.nil_append]
  repeat
    first
    | rw [List.foldl_cons]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false,
        List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  simp only [List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  simp only [graphValue, graphEdges, List.any_cons, List.any_nil,
    Bool.or_false, Bool.and_or_distrib_left]
  ac_rfl

def maskedBaseline : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [11, 12]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [14, 15]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [17, 6]⟩, ⟨.and, [1, 18]⟩,
    ⟨.or, [3, 5]⟩, ⟨.or, [20, 6]⟩, ⟨.and, [8, 21]⟩,
    ⟨.or, [4, 7]⟩, ⟨.or, [23, 6]⟩, ⟨.and, [9, 24]⟩,
    ⟨.or, [13, 16]⟩, ⟨.or, [26, 19]⟩,
    ⟨.or, [27, 22]⟩, ⟨.or, [28, 25]⟩], 29⟩

lemma maskedBaseline_size : maskedBaseline.size = 19 := rfl

lemma maskedBaseline_fanin : FanInTwo maskedBaseline := by
  intro g hg
  simp only [maskedBaseline, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma maskedBaseline_correct (x : Fin 10 → Bool) :
    maskedBaseline.eval (List.ofFn x ++ [x 0 && x 2]) =
      (graphValue x || (x 0 && x 2)) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    simp [List.ofFn_succ]
  rw [hx]
  dsimp only [maskedBaseline, Circuit.eval, Circuit.wires]
  simp only [List.cons_append, List.nil_append]
  repeat
    first
    | rw [List.foldl_cons]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false,
        List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  simp only [List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  simp only [graphValue, graphEdges, List.any_cons, List.any_nil,
    Bool.or_false, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, Bool.and_comm,
    Bool.or_self_left]

lemma seed_pair_is_negative :
    graphValue (fun i => decide (i = 0 ∨ i = 2)) = false := by
  decide

lemma maskedBaseline_is_not_solution :
    maskedBaseline.eval
      (List.ofFn (fun i : Fin 10 => decide (i = 0 ∨ i = 2)) ++ [true]) ≠
      graphValue (fun i => decide (i = 0 ∨ i = 2)) := by
  decide

end PEqualNP.Outside.L_meta_1890
