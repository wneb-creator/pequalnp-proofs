import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.ExchangeCircuit

open PEqualNP.CircuitLowerBounds

def before : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩

def after : Circuit :=
  ⟨[⟨GateOp.and, [2, 1]⟩, ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

theorem before_size : before.size = 3 := rfl

theorem after_size : after.size = 3 := rfl

theorem before_binary_monotone : ∀ g ∈ before.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [before, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem after_binary_monotone : ∀ g ∈ after.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [after, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem eval_eq_of_implies (A B a d : Bool)
    (ha : a = true → A = true) (hd : d = true → B = true) :
    before.eval [A, B, a, d] = after.eval [A, B, a, d] := by
  cases A <;> cases B <;> cases a <;> cases d <;>
    first | rfl | exact Bool.noConfusion (ha rfl) | exact Bool.noConfusion (hd rfl)

end PEqualNP.Outside.L_meta_1031_aux.ExchangeCircuit
