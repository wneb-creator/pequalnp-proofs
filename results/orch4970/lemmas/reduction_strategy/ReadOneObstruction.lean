import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def repeatedStar : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [0, 4]⟩], 5⟩

def starEdges : Finset (Fin 1 × Fin 2) := Finset.univ

theorem repeatedStar_ao2 : PEqualNP.TopForm.IsAO2 3 repeatedStar := by decide

theorem repeatedStar_zero_twoColour :
    PEqualNP.TwoColour.tCount 3 repeatedStar (fun i => decide (1 ≤ i)) = 0 := by decide

theorem repeatedStar_computes : ∀ x : Fin 3 → Bool,
    circuitFun 3 repeatedStar x = decide (∃ a : Fin 1, ∃ b : Fin 2,
      (a, b) ∈ starEdges ∧ x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 1 b) = true) := by decide

theorem starEdges_no_square : ∀ (a a' : Fin 1) (b b' : Fin 2),
    a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ starEdges ∧ (a, b') ∈ starEdges ∧
      (a', b) ∈ starEdges ∧ (a', b') ∈ starEdges) := by decide

theorem repeatedStar_starOR : ∀ (a : Fin 1) (b : Fin 2), (a, b) ∈ starEdges →
    ∃ (j : ℕ) (Q : Finset (Fin 2)), j < repeatedStar.gates.length ∧
      (NestedCover.gateAt repeatedStar j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ starEdges) ∧ ∀ x : Fin 3 → Bool,
        (repeatedStar.wires (List.ofFn x)).getD (3 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  intro a b _
  refine ⟨0, Finset.univ, by decide, rfl, by decide, Finset.mem_univ b, ?_, ?_⟩
  · intro b' _
    exact Finset.mem_univ (a, b')
  · decide

theorem repeatedStar_not_read_one : ¬ PEqualNP.ReadK.IsReadK 3 repeatedStar 1 := by decide

end PEqualNP.Outside.L_meta_4970_aux
