import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18229 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => decide (4 ≤ (List.ofFn x).count true)) 26 := by
  unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [15, 11]⟩, ⟨.and, [17, 13]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [19, 21]⟩, ⟨.and, [18, 20]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [9, 24]⟩, ⟨.and, [27, 25]⟩, ⟨.and, [28, 23]⟩, ⟨.or, [28, 23]⟩, ⟨.or, [26, 29]⟩, ⟨.and, [31, 30]⟩], 32⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
