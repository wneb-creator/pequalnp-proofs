import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.CyclicCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core

abbrev adj6 (u v : Fin 6) : Bool :=
  (u == 0 && (v == 3 || v == 5)) || ((u == 3 || u == 5) && v == 0) ||
  (u == 1 && (v == 3 || v == 4)) || ((u == 3 || u == 4) && v == 1) ||
  (u == 2 && (v == 4 || v == 5)) || ((u == 4 || u == 5) && v == 2)

abbrev graph : SimpleGraph (Fin 6) where
  Adj u v := adj6 u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

def colors (i : Fin 6) : Bool := decide (3 ≤ i.val)

def circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [1, 17]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [2, 19]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [21, 20]⟩
  ], 22⟩

def cover : Finset (Fin 6) := {0, 1, 2}

def edges : Finset (Sym2 (Fin 6)) :=
  {s(0, 3), s(0, 5), s(1, 3), s(1, 4), s(2, 4), s(2, 5)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma bipartite : ∀ u v : Fin 6, graph.Adj u v → colors u ≠ colors v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma no_four_cycle : NoFourCycle graph := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma ao2 : IsAO2 6 circuit := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma correct : circuitFun 6 circuit = graphFun graph ∅ := by
  funext x
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma lift_fixed : IsLiftFixedPoint graph circuit := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma maximal_cores : maximalCores graph circuit = {8} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma accepted_edges : (maximalCores graph circuit).biUnion (gammaE graph circuit) = edges := by
  rw [maximal_cores]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cone_union : (maximalCores graph circuit).biUnion (coneSet 6 circuit) = Finset.range 9 := by
  rw [maximal_cores]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma minimum_cover : IsMinCover graph cover := by
  unfold IsMinCover SimpleGraph.IsVertexCover
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma residual_empty_cover : IsMinCover
    (graph.deleteEdges (((maximalCores graph circuit).biUnion (gammaE graph circuit)
      : Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))) ∅ := by
  rw [accepted_edges]
  refine ⟨?_, ?_⟩
  · intro u v huv
    rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe] at huv
    revert u v huv
    decide +kernel
  · intro S hS
    simp

theorem cyclic_core_near_tight :
    (∀ u v : Fin 6, graph.Adj u v → colors u ≠ colors v) ∧
    NoFourCycle graph ∧ IsAO2 6 circuit ∧
    circuitFun 6 circuit = graphFun graph ∅ ∧ IsLiftFixedPoint graph circuit ∧
    IsMinCover graph cover ∧
    IsMinCover
      (graph.deleteEdges (((maximalCores graph circuit).biUnion (gammaE graph circuit)
        : Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))) ∅ ∧
    ((maximalCores graph circuit).biUnion (gammaE graph circuit)).card = 6 ∧
    ((maximalCores graph circuit).biUnion (coneSet 6 circuit)).card = 9 ∧
    (maximalCores graph circuit).card = 1 ∧
    ((maximalCores graph circuit).biUnion (gammaE graph circuit)).card + cover.card + 1 =
      ((maximalCores graph circuit).biUnion (coneSet 6 circuit)).card +
      (maximalCores graph circuit).card + (∅ : Finset (Fin 6)).card := by
  refine ⟨bipartite, no_four_cycle, ao2, correct, lift_fixed, minimum_cover,
    residual_empty_cover, ?_, ?_, ?_, ?_⟩
  · rw [accepted_edges]; decide +kernel
  · rw [cone_union]; decide +kernel
  · rw [maximal_cores]; decide +kernel
  · rw [accepted_edges, cone_union, maximal_cores]; decide +kernel

end PEqualNP.Outside.L_meta_2962_aux.CyclicCore
