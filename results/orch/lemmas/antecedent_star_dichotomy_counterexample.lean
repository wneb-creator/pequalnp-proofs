import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.StarDichotomyCounterexample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev pathGraph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 2), (0, 3), (1, 2)]

def pathTwoJunk : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [7, 8]⟩], 9⟩

def pathFourGate : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

lemma pathTwoJunk_isAO2 : IsAO2 4 pathTwoJunk := by decide
lemma pathFourGate_isAO2 : IsAO2 4 pathFourGate := by decide
lemma path_noFourCycle : NoFourCycle pathGraph := by decide
lemma path_bipartite : ∀ u v : Fin 4, pathGraph.Adj u v →
    decide (u.val < 2) ≠ decide (v.val < 2) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathTwoJunk_computes :
    circuitFun 4 pathTwoJunk = graphFun pathGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathFourGate_computes :
    circuitFun 4 pathFourGate = graphFun pathGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathTwoJunk_junk : junk pathGraph pathTwoJunk = {3, 4} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathTwoJunk_cleaners :
    wmax pathGraph pathTwoJunk 3 = {2, 3} ∧
    wmax pathGraph pathTwoJunk 4 = {0, 2} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathTwoJunk_product_semantics :
    (∀ x : Fin 4 → Bool, gateVal 4 pathTwoJunk 3 x =
      ((x 0 || x 1) && (x 0 || x 2))) ∧
    (∀ x : Fin 4 → Bool, gateVal 4 pathTwoJunk 4 x =
      ((x 0 || x 1) && (x 2 || x 3))) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pathTwoJunk_both_guard_every_edge :
    ∀ k ∈ ({3, 4} : Finset ℕ), ∀ u v : Fin 4, pathGraph.Adj u v →
      gateVal 4 pathTwoJunk k (pairInput u v) = true ∧
      (u ∈ wmax pathGraph pathTwoJunk k ∨ v ∈ wmax pathGraph pathTwoJunk k) := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl <;> decide

lemma path_edges_not_one_star :
    ∀ z : Fin 4, ∃ u v : Fin 4, pathGraph.Adj u v ∧ u ≠ z ∧ v ≠ z := by decide

lemma path_residual_edges_not_one_star :
    ∀ z : Fin 4, ∃ u v : Fin 4, pathGraph.Adj u v ∧
      ({u, v} : Finset (Fin 4)) ≠ {0, 2} ∧ u ≠ z ∧ v ≠ z := by decide

lemma path_first_product_not_disjoint :
    ¬ Disjoint ({0, 1} : Finset (Fin 4)) {0, 2} := by decide

lemma pathTwoJunk_not_least : ¬ IsLeastAO pathGraph pathTwoJunk := by
  intro h
  have hs := h.2.2 pathFourGate pathFourGate_isAO2 pathFourGate_computes
  change 6 ≤ 4 at hs
  omega

end PEqualNP.Outside.L_meta_5012.StarDichotomyCounterexample
