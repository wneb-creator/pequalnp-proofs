import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.CycleWitness

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 3]⟩,
    ⟨.and, [2, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

lemma size_seven : circuit.size = 7 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma computes_cycle : ∀ x : Fin 5 → Bool,
    circuit.eval (List.ofFn x) =
      decide (∃ u v : Fin 5, (u + 1 = v ∨ v + 1 = u) ∧
        x u = true ∧ x v = true) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma every_and_sound : ∀ (x : Fin 5 → Bool) (t : Fin 7),
    (t.val = 1 ∨ t.val = 3 ∨ t.val = 4) →
    (circuit.wires (List.ofFn x)).getD (5 + t.val) false = true →
    circuit.eval (List.ofFn x) = true := by
  decide

lemma monotone_binary : ∀ g ∈ circuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1031_aux.CycleWitness
