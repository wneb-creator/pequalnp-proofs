import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.DuplicateGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel fun a b : Fin 6 => a.val / 2 = b.val / 2

def circuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [9, 10]⟩,
    ⟨.and, [4, 5]⟩, ⟨.or, [8, 12]⟩], 13⟩

def cover : Finset (Fin 6) := {0, 2, 4}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma graph_properties :
    NoFourCycle graph ∧ (∀ u v : Fin 6, graph.Adj u v →
      decide (u.val % 2 = 0) ≠ decide (v.val % 2 = 0)) ∧
      IsMinCover graph cover ∧ cover.card = 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma circuit_properties :
    IsAO2 6 circuit ∧ IsLiftFixedPoint graph circuit ∧
      maximalCores graph circuit = {5} ∧
      ((maximalCores graph circuit).biUnion (coneSet 6 circuit)).card = 6 ∧
      (maximalCores graph circuit).biUnion (gammaE graph circuit) = graph.edgeFinset ∧
      (((maximalCores graph circuit).biUnion (gammaE graph circuit)).biUnion Sym2.toFinset).card = 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma circuit_correct : circuitFun 6 circuit = graphFun graph ∅ := by
  funext x
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma unique_reused_wire : coneSet 6 circuit 5 = Finset.range 6 ∧
    ∀ w : Fin 12, ((circuit.gates.take 6).flatMap Gate.inputs).count w.val =
      if w.val = 8 then 2 else if w.val = 11 then 0 else 1 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2962_aux.DuplicateGate
