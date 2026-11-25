import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.CountingShared

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core

abbrev oneEdge : SimpleGraph (Fin 2) := ⊤

def sharedDead : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 0]⟩,
    ⟨GateOp.and, [2, 1]⟩], 2⟩

def sharedOneLive : Circuit := { sharedDead with output := 3 }

theorem sharedDead_AO2 : IsAO2 2 sharedDead := by decide

theorem sharedDead_computes : ∀ x : Fin 2 → Bool,
    circuitFun 2 sharedDead x = graphFun oneEdge ∅ x := by decide

theorem sharedDead_fixed : IsLiftFixedPoint oneEdge sharedDead := by decide

theorem sharedDead_maximal : maximalCores oneEdge sharedDead = {1, 2} := by decide

theorem sharedDead_cones : coneSet 2 sharedDead 1 = {0, 1} ∧
    coneSet 2 sharedDead 2 = {0, 2} := by decide

theorem sharedDead_shared_gate :
    coneSet 2 sharedDead 1 ∩ coneSet 2 sharedDead 2 = {0} := by decide

theorem sharedDead_cores_dead :
    ¬ InOutputCone 2 sharedDead 1 ∧ ¬ InOutputCone 2 sharedDead 2 := by decide

theorem sharedDead_union_edges :
    (maximalCores oneEdge sharedDead).biUnion (gammaE oneEdge sharedDead) =
      oneEdge.edgeFinset := by decide

theorem sharedDead_covers : IsMinCover oneEdge {0} ∧
    IsMinCover (oneEdge.deleteEdges
      (((maximalCores oneEdge sharedDead).biUnion (gammaE oneEdge sharedDead) :
        Finset (Sym2 (Fin 2))) : Set (Sym2 (Fin 2)))) ∅ := by decide

theorem sharedDead_margin :
    ((maximalCores oneEdge sharedDead).biUnion (gammaE oneEdge sharedDead)).card +
      ({0} : Finset (Fin 2)).card + 3 =
    ((maximalCores oneEdge sharedDead).biUnion (coneSet 2 sharedDead)).card +
      (maximalCores oneEdge sharedDead).card + (∅ : Finset (Fin 2)).card := by decide

/-- Dead maximal cores can make the union-plus-root count exceed size plus one. -/
theorem sharedDead_companion_fails : sharedDead.size + 1 <
    ((maximalCores oneEdge sharedDead).biUnion (coneSet 2 sharedDead)).card +
      (maximalCores oneEdge sharedDead).card := by decide

theorem sharedOneLive_computes : ∀ x : Fin 2 → Bool,
    circuitFun 2 sharedOneLive x = graphFun oneEdge ∅ x := by decide

theorem sharedOneLive_fixed : IsLiftFixedPoint oneEdge sharedOneLive := by decide

theorem sharedOneLive_maximal : maximalCores oneEdge sharedOneLive = {1, 2} := by decide

theorem sharedOneLive_status :
    InOutputCone 2 sharedOneLive 1 ∧ ¬ InOutputCone 2 sharedOneLive 2 := by decide

end PEqualNP.Outside.L_meta_2962_aux.CountingShared
