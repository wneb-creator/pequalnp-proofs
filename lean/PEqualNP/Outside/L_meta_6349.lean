import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_6349
