import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.TwoDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

abbrev graph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (2, 3)]

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩], 10⟩

def direct : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma legal : Monotone2 circuit := by
  simp [Monotone2, circuit]

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = ((x 0 && x 1) || (x 2 && x 3)) := by
  decide +kernel

lemma computes_graph : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = decide (∃ u v : Fin 4, graph.Adj u v ∧ x u = true ∧ x v = true) := by
  decide +kernel

lemma no_triangles : ∀ a b c : Fin 4,
    graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  decide +kernel

lemma no_four_cycles : ∀ a b c d : Fin 4,
    graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a → a = c ∨ b = d := by
  decide +kernel

lemma both_own : Owns 4 circuit 2 0 1 ∧ Owns 4 circuit 2 2 3 ∧
    Owns 4 circuit 5 0 1 ∧ Owns 4 circuit 5 2 3 := by
  decide +kernel

lemma no_common_center : ¬ ∃ c : Fin 4, (0 = c ∨ 1 = c) ∧ (2 = c ∨ 3 = c) := by
  decide +kernel

lemma not_star : ¬ HasStarProfile 4 graph circuit := by
  decide +kernel

lemma final_owns_none : ∀ u v : Fin 4, graph.Adj u v → ¬ Owns 4 circuit 6 u v := by
  decide +kernel

lemma dirty_witnesses : gateVal 4 circuit 2 (pairInput 0 3) = true ∧ ¬ graph.Adj 0 3 ∧
    gateVal 4 circuit 5 (pairInput 0 2) = true ∧ ¬ graph.Adj 0 2 := by
  decide +kernel

lemma final_sound : ∀ x : Fin 4 → Bool,
    gateVal 4 circuit 6 x = true → (x 0 && x 1) || (x 2 && x 3) = true := by
  decide +kernel

lemma every_gate_essential : ∀ t : Fin 7,
    gateVal 4 circuit t (pairInput 0 1) = true ∧
      circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit t 11) (pairInput 0 1) = false := by
  decide +kernel

lemma no_earlier_bypass : ∀ t : Fin 7, ∀ r : Fin (4 + t.val), ∃ x : Fin 4 → Bool,
    circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit t r) x ≠ circuitFun 4 circuit x := by
  decide +kernel

lemma cheaper : direct.size < circuit.size ∧
    ∀ x : Fin 4 → Bool, circuitFun 4 direct x = circuitFun 4 circuit x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031_aux.TwoDirty
