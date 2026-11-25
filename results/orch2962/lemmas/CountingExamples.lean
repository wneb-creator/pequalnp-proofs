import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.CountingExamples

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core

abbrev oneEdge : SimpleGraph (Fin 2) := ⊤

def repeatedEdge : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 0]⟩], 3⟩

theorem oneEdge_bipartite : ∀ u v : Fin 2, oneEdge.Adj u v →
    decide (u = 0) ≠ decide (v = 0) := by decide

theorem oneEdge_no_four_cycle : NoFourCycle oneEdge := by decide

theorem repeatedEdge_AO2 : IsAO2 2 repeatedEdge := by decide

theorem repeatedEdge_computes : ∀ x : Fin 2 → Bool,
    circuitFun 2 repeatedEdge x = graphFun oneEdge ∅ x := by decide

theorem repeatedEdge_fixed : IsLiftFixedPoint oneEdge repeatedEdge := by decide

/-- A core may have one implicant operand under the posted definition. -/
theorem repeatedEdge_one_implicant_operand :
    IsCore oneEdge repeatedEdge 1 ∧
    IsImpOperand oneEdge repeatedEdge (opnd repeatedEdge 1 0) ∧
    ¬ IsImpOperand oneEdge repeatedEdge (opnd repeatedEdge 1 1) := by decide

theorem repeatedEdge_maximal : maximalCores oneEdge repeatedEdge = {1} := by decide

theorem repeatedEdge_union_cone :
    (maximalCores oneEdge repeatedEdge).biUnion (coneSet 2 repeatedEdge) = {0, 1} := by decide

theorem repeatedEdge_union_edges :
    (maximalCores oneEdge repeatedEdge).biUnion (gammaE oneEdge repeatedEdge) =
      oneEdge.edgeFinset := by decide

theorem oneEdge_min_cover : IsMinCover oneEdge {0} := by decide

theorem repeatedEdge_residual_min_cover :
    IsMinCover (oneEdge.deleteEdges
      (((maximalCores oneEdge repeatedEdge).biUnion (gammaE oneEdge repeatedEdge) :
        Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2)))) ∅ := by decide

/-- The right side exceeds the left side by exactly one in this example. -/
theorem repeatedEdge_margin :
    ((maximalCores oneEdge repeatedEdge).biUnion (gammaE oneEdge repeatedEdge)).card +
      ({0} : Finset (Fin 2)).card + 1 =
    ((maximalCores oneEdge repeatedEdge).biUnion (coneSet 2 repeatedEdge)).card +
      (maximalCores oneEdge repeatedEdge).card + (∅ : Finset (Fin 2)).card := by decide

end PEqualNP.Outside.L_meta_2962_aux.CountingExamples
