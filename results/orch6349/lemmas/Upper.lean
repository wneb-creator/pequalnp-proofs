import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩

lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma witness_rep : Represents (fun u v : Fin 4 => (5805 : ℕ).testBit (4*u.val+v.val)) witness := by
  decide +kernel

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (5805 : ℕ).testBit (4*u.val+v.val)) 10 := by
  exact ⟨witness, witness_mono, by decide +kernel, witness_rep⟩

end PEqualNP.Outside.L_meta_6349
