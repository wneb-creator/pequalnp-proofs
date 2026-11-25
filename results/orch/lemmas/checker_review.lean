import PEqualNP.Defs.CircuitMoves
import PEqualNP.Defs.EdgeOwnership

namespace PEqualNP.Outside.L_meta_1031_aux.PivotalObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

def chain : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2]⟩], 3⟩

lemma chain_mono : ∀ g ∈ chain.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

lemma chain_computes : ∀ x : Fin 2 → Bool,
    chain.eval (List.ofFn x) = decide (∃ u v : Fin 2,
      (edgeGraph 2 [(0, 1)]).Adj u v ∧ x u = true ∧ x v = true) := by
  decide

lemma each_gate_pivotal : ∀ j : Fin 2,
    ∃ u v : Fin 2, (edgeGraph 2 [(0, 1)]).Adj u v ∧
      gateVal 2 chain j (pairInput u v) = true ∧
      PEqualNP.MetaComplexity.circuitFun 2
        (PEqualNP.CircuitMoves.eraseGate 2 chain j (2 + chain.gates.length))
        (pairInput u v) = false := by
  decide

lemma last_gate_owns_nothing : ∀ u v : Fin 2, ¬ Owns 2 chain 1 u v := by
  decide

end PEqualNP.Outside.L_meta_1031_aux.PivotalObstruction
