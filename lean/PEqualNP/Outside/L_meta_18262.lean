import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18262
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [6, 16]⟩, ⟨GateOp.or, [7, 17]⟩, ⟨GateOp.or, [8, 18]⟩, ⟨GateOp.or, [9, 19]⟩, ⟨GateOp.and, [20, 29]⟩, ⟨GateOp.or, [20, 29]⟩, ⟨GateOp.or, [31, 21]⟩, ⟨GateOp.or, [32, 22]⟩, ⟨GateOp.or, [23, 24]⟩, ⟨GateOp.or, [34, 25]⟩, ⟨GateOp.or, [26, 27]⟩, ⟨GateOp.or, [36, 28]⟩, ⟨GateOp.or, [31, 23]⟩, ⟨GateOp.or, [38, 26]⟩, ⟨GateOp.or, [21, 24]⟩, ⟨GateOp.or, [40, 27]⟩, ⟨GateOp.or, [22, 25]⟩, ⟨GateOp.or, [42, 28]⟩, ⟨GateOp.or, [35, 37]⟩, ⟨GateOp.and, [35, 37]⟩, ⟨GateOp.and, [33, 44]⟩, ⟨GateOp.or, [46, 45]⟩, ⟨GateOp.or, [41, 43]⟩, ⟨GateOp.and, [41, 43]⟩, ⟨GateOp.and, [39, 48]⟩, ⟨GateOp.or, [50, 49]⟩, ⟨GateOp.or, [47, 51]⟩, ⟨GateOp.or, [30, 52]⟩], 53⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun u v : Fin 10 => decide (u ≠ v)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_18262

theorem PEqualNP.Outside.L_meta_18262 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 10 => decide (u ≠ v)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_18262.circ, PEqualNP.Outside.L_meta_18262.mono, by decide, PEqualNP.Outside.L_meta_18262.rep⟩
