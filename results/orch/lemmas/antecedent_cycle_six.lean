import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev cycleSixGraph : SimpleGraph (Fin 6) :=
  edgeGraph 6 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]

def cycleSixCircuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 8]⟩,
    ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩

lemma cycleSix_isAO2 : IsAO2 6 cycleSixCircuit := by decide

lemma cycleSix_size : cycleSixCircuit.size = 8 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cycleSix_computes :
    circuitFun 6 cycleSixCircuit = graphFun cycleSixGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cycleSix_junk_empty : junk cycleSixGraph cycleSixCircuit = ∅ := by decide

lemma cycleSix_noFourCycle : NoFourCycle cycleSixGraph := by decide

lemma cycleSix_bipartite :
    ∀ u v : Fin 6, cycleSixGraph.Adj u v →
      decide (u.val % 2 = 0) ≠ decide (v.val % 2 = 0) := by decide

end PEqualNP.Outside.L_meta_5012
