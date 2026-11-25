import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.CountingTight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core

abbrev path : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun u v : Fin 4 => u.val + 1 = v.val)

/-- The first four gates are dead. The last four form the live path circuit. -/
def circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩,
    ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩,
    ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

theorem path_bipartite : ∀ u v : Fin 4, path.Adj u v →
    decide (u.val % 2 = 0) ≠ decide (v.val % 2 = 0) := by decide

theorem path_no_four_cycle : NoFourCycle path := by decide

theorem circuit_AO2 : IsAO2 4 circuit := by decide

theorem circuit_computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = graphFun path ∅ x := by decide

set_option maxRecDepth 100000 in
theorem circuit_fixed : IsLiftFixedPoint path circuit := by decide

set_option maxRecDepth 100000 in
theorem circuit_maximal : maximalCores path circuit = {3} := by decide

theorem core_cone : coneSet 4 circuit 3 = {0, 1, 2, 3} := by decide

theorem core_is_dead : ¬ InOutputCone 4 circuit 3 := by decide

set_option maxRecDepth 100000 in
theorem union_edges :
    (maximalCores path circuit).biUnion (gammaE path circuit) = path.edgeFinset := by decide

theorem path_min_cover : IsMinCover path {1, 2} := by decide

set_option maxRecDepth 100000 in
theorem residual_min_cover :
    IsMinCover (path.deleteEdges
      (((maximalCores path circuit).biUnion (gammaE path circuit) :
        Finset (Sym2 (Fin 4))) : Set (Sym2 (Fin 4)))) ∅ := by decide

set_option maxRecDepth 100000 in
/-- All posted hypotheses hold, and the proposed inequality is exactly tight. -/
theorem exact_equality :
    ((maximalCores path circuit).biUnion (gammaE path circuit)).card +
      ({1, 2} : Finset (Fin 4)).card =
    ((maximalCores path circuit).biUnion (coneSet 4 circuit)).card +
      (maximalCores path circuit).card + (∅ : Finset (Fin 4)).card := by decide

end PEqualNP.Outside.L_meta_2962_aux.CountingTight
