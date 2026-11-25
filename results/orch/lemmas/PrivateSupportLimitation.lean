import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.PrivateSupportExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0, 1), (2, 3), (4, 0), (4, 2), (5, 1),
    (5, 3), (6, 0), (6, 3), (7, 1), (7, 2)]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [11, 12]⟩,
    ⟨.and, [10, 13]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [5, 9]⟩,
    ⟨.and, [6, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [14, 15]⟩,
    ⟨.or, [16, 17]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [21, 18]⟩], 22⟩

lemma model : IsAO2 8 circuit := by decide

lemma triangle_free :
    ∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬graph.Adj c a := by decide

lemma no_four_cycle : NoFourCycle graph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma correct : circuitFun 8 circuit = graphFun graph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma top_form : TopForm graph circuit := by decide

lemma first_and : ∀ i < 2, (gateAt circuit i).op = GateOp.or := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma owns_disjoint : Owns 8 circuit 2 0 1 ∧ Owns 8 circuit 2 2 3 := by decide

lemma pivotal_disjoint :
    circuitFun 8 ⟨circuit.gates.set 2 ⟨.or, []⟩, circuit.output⟩ (pairInput 0 1) = false ∧
    circuitFun 8 ⟨circuit.gates.set 2 ⟨.or, []⟩, circuit.output⟩ (pairInput 2 3) = false := by decide

lemma supports_shared :
    opnd circuit 2 0 = 8 ∧ opnd circuit 2 1 = 9 ∧
    readers 8 circuit 0 = {2, 7} ∧ readers 8 circuit 1 = {2, 8} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma additional_readers_clean :
    (gateAt circuit 7).op = GateOp.and ∧ BelowF graph circuit 7 ∧
    (gateAt circuit 8).op = GateOp.and ∧ BelowF graph circuit 8 := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma size : circuit.size = 15 := rfl

lemma or_count :
    (circuit.gates.filter fun g => match g.op with | .or => true | _ => false).length = 8 := rfl

lemma edge_count : graph.edgeFinset.card = 10 := by decide

lemma or_count_below_edges_minus_one :
    (circuit.gates.filter fun g => match g.op with | .or => true | _ => false).length + 1 <
      graph.edgeFinset.card := by rw [or_count, edge_count]; decide

end PEqualNP.Outside.L_meta_2448_aux.PrivateSupportExample
