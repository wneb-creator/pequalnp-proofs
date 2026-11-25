import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.BoundaryGadget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hood : Fin 11 → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

def circuit : Circuit :=
  { gates :=
      [⟨.or, [7, 10]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [11, 12]⟩,
       ⟨.or, [5, 10]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [2, 15]⟩,
       ⟨.or, [9, 10]⟩, ⟨.and, [0, 17]⟩,
       ⟨.or, [8, 13]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [19, 20]⟩,
       ⟨.or, [4, 8]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [22, 23]⟩,
       ⟨.or, [6, 7]⟩, ⟨.and, [3, 25]⟩,
       ⟨.or, [16, 18]⟩, ⟨.or, [27, 21]⟩,
       ⟨.or, [28, 24]⟩, ⟨.or, [29, 26]⟩]
    output := 30 }

lemma ao2 : PEqualNP.TopForm.IsAO2 11 circuit := by decide

lemma size_twenty : circuit.size = 20 := by decide

lemma misses_edge :
    (hood 6).testBit 7 = true ∧
      circuitFun 11 circuit (fun i => decide (i = 6 ∨ i = 7)) = false := by decide

set_option maxRecDepth 4096 in
lemma not_exact_edge_function :
    ¬ ∀ x : Fin 11 → Bool, circuitFun 11 circuit x =
      decide (∃ u v : Fin 11, (hood u).testBit v.val = true ∧ x u = true ∧ x v = true) := by
  intro h
  have he := h (fun i => decide (i = 6 ∨ i = 7))
  rw [misses_edge.2] at he
  have ht : decide (∃ u v : Fin 11, (hood u).testBit v.val = true ∧
      decide (u = 6 ∨ u = 7) = true ∧ decide (v = 6 ∨ v = 7) = true) = true := by
    rw [decide_eq_true_eq]
    exact ⟨6, 7, misses_edge.1, by decide, by decide⟩
  rw [ht] at he
  contradiction

lemma not_bipartite :
    ¬ ∃ color : Fin 11 → Bool, ∀ u v : Fin 11,
      (hood u).testBit v.val = true → color u ≠ color v := by
  rintro ⟨color, h⟩
  have a := h 1 4 (by decide)
  have b := h 4 8 (by decide)
  have c := h 8 1 (by decide)
  cases h1 : color 1 <;> cases h4 : color 4 <;> cases h8 : color 8 <;> simp_all

end PEqualNP.Outside.L_meta_2583_aux.BoundaryGadget
