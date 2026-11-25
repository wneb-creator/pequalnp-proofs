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

def cycleSixTwoJunkCircuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.and, [14, 15]⟩], 16⟩

lemma cycleSixTwoJunk_isAO2 : IsAO2 6 cycleSixTwoJunkCircuit := by decide

lemma cycleSixTwoJunk_size : cycleSixTwoJunkCircuit.size = 11 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cycleSixTwoJunk_computes :
    circuitFun 6 cycleSixTwoJunkCircuit = graphFun cycleSixGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cycleSixTwoJunk_junk : junk cycleSixGraph cycleSixTwoJunkCircuit = {2, 5} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cycleSixTwoJunk_top_clean : BelowF cycleSixGraph cycleSixTwoJunkCircuit 10 := by decide

lemma cycleSixTwoJunk_top_hits_matching :
    gateVal 6 cycleSixTwoJunkCircuit 10 (pairInput (0 : Fin 6) 1) = true ∧
    gateVal 6 cycleSixTwoJunkCircuit 10 (pairInput (2 : Fin 6) 3) = true ∧
    gateVal 6 cycleSixTwoJunkCircuit 10 (pairInput (4 : Fin 6) 5) = true := by decide

lemma cycleSixTwoJunk_not_least : ¬ IsLeastAO cycleSixGraph cycleSixTwoJunkCircuit := by
  intro h
  have hs := h.2.2 cycleSixCircuit cycleSix_isAO2 cycleSix_computes
  change 11 ≤ 8 at hs
  omega

end PEqualNP.Outside.L_meta_5012
