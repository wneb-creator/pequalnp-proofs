import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.CounterExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.EdgeOwnership PEqualNP.CircuitMoves PEqualNP.ReadK

abbrev path : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun a b : Fin 5 => a.val + 1 = b.val)

def circuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [11, 3]⟩,
    ⟨.and, [10, 12]⟩], 13⟩

def shorter : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [7, 8]⟩], 9⟩

lemma bipartite : ∀ u v : Fin 5, path.Adj u v →
    decide (u.val % 2 = 0) ≠ decide (v.val % 2 = 0) := by decide

lemma no_four_cycle : NoFourCycle path := by decide

lemma ao2 : IsAO2 5 circuit := by decide

lemma computes : circuitFun 5 circuit = graphFun path ∅ := by
  funext x
  revert x
  decide

lemma shorter_ao2 : IsAO2 5 shorter := by decide

lemma shorter_computes : circuitFun 5 shorter = graphFun path ∅ := by
  funext x
  revert x
  decide

lemma sizes : circuit.size = 9 ∧ shorter.size = 5 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma top_form : TopForm path circuit := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma lift_fixed : IsLiftFixedPoint path circuit := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma all_gates_live : ∀ k < circuit.gates.length, InOutputCone 5 circuit k := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma junk_exact : junk path circuit = {3, 5} := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma junk_accepts_four : ∀ j ∈ junk path circuit, (gammaE path circuit j).card = 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma all_gates_edge_pivotal : ∀ j < circuit.gates.length,
    ∃ u v : Fin 5, path.Adj u v ∧
      circuitFun 5 circuit (pairInput u v) = true ∧
      circuitFun 5 (eraseGate 5 circuit j 14) (pairInput u v) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma no_edge_covers_junk : ∀ j ∈ junk path circuit, ∀ u v : Fin 5,
    path.Adj u v → ∃ p l : Fin 5, path.Adj p l ∧
      gateVal 5 circuit j (pairInput p l) = true ∧
      p ≠ u ∧ p ≠ v ∧ l ≠ u ∧ l ≠ v := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma not_read_one : ¬ IsReadK 5 circuit 1 := by decide +kernel

lemma not_least : ¬ IsLeastAO path circuit := by
  intro h
  have hle := h.2.2 shorter shorter_ao2 shorter_computes
  have hs := sizes
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma every_operand_bypass_changes : ∀ j < circuit.gates.length, ∀ b : Fin 2,
    ∃ x : Fin 5 → Bool,
      circuitFun 5 (eraseGate 5 circuit j (opnd circuit j b)) x ≠
        circuitFun 5 circuit x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2583.CounterExample
