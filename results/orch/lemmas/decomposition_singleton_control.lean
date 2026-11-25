import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.SingletonControl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.Core PEqualNP.ReadK

abbrev graph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 2), (0, 3), (1, 2)]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def improved : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma normalized_non_read_one :
    NoFourCycle graph ∧ IsAO2 4 circuit ∧
    (∀ x : Fin 4 → Bool, circuitFun 4 circuit x = graphFun graph ∅ x) ∧
    IsLiftFixedPoint graph circuit ∧ TopForm graph circuit ∧
    (∀ j : Fin 5, (gateAt circuit j.val).op = GateOp.and →
      ∀ w : Fin 9, w.val ∈ (gateAt circuit j.val).inputs →
        ¬ WireBelowOutput 4 circuit w.val) ∧
    (∀ j < circuit.gates.length, InOutputCone 4 circuit j) ∧
    (∀ j < circuit.gates.length, ∃ u v : Fin 4,
      graph.Adj u v ∧ gateVal 4 circuit j (pairInput u v) = true) ∧
    (∀ j : Fin 5, (gateAt circuit j.val).op = GateOp.and →
      ∀ u : Fin 4, gateVal 4 circuit j.val (pairInput u u) = false) ∧
    (∀ j : Fin 5, (gateAt circuit j.val).op = GateOp.or → ∀ b : Fin 2,
      ∃ u v : Fin 4, graph.Adj u v ∧
        (circuit.wires (List.ofFn (pairInput u v))).getD (opnd circuit j.val b) false = true ∧
        (circuit.wires (List.ofFn (pairInput u v))).getD (opnd circuit j.val (1 - b)) false = false) ∧
    ¬ IsReadK 4 circuit 1 := by
  letI := gateOpDecEq
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma strict_improvement :
    IsAO2 4 improved ∧
    (∀ x : Fin 4 → Bool, circuitFun 4 improved x = circuitFun 4 circuit x) ∧
    improved.size = 4 ∧ circuit.size = 5 ∧ IsReadK 4 improved 1 := by
  decide

end PEqualNP.Outside.L_meta_2583.SingletonControl
