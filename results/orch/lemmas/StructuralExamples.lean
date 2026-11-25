import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_aux

def p4Circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩], 7⟩

def p4Edges : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 1)}

lemma p4_no_four_cycle :
    ∀ (a a' : Fin 2) (b b' : Fin 2), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ p4Edges ∧ (a, b') ∈ p4Edges ∧
         (a', b) ∈ p4Edges ∧ (a', b') ∈ p4Edges) := by
  decide

lemma p4_is_ao : PEqualNP.TopForm.IsAO2 4 p4Circuit := by
  decide

lemma p4_computes :
    ∀ x : Fin (2 + 2) → Bool,
      PEqualNP.MetaComplexity.circuitFun (2 + 2) p4Circuit x =
        decide (∃ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges ∧
          x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

lemma p4_no_two_colour :
    PEqualNP.TwoColour.tCount 4 p4Circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide

lemma p4_not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 p4Circuit 1 := by
  decide

def p4BufferedCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [6, 7]⟩], 8⟩

lemma p4_buffered_is_ao : PEqualNP.TopForm.IsAO2 4 p4BufferedCircuit := by
  decide

lemma p4_buffered_computes :
    ∀ x : Fin (2 + 2) → Bool,
      PEqualNP.MetaComplexity.circuitFun (2 + 2) p4BufferedCircuit x =
        decide (∃ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges ∧
          x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

lemma p4_buffered_no_two_colour :
    PEqualNP.TwoColour.tCount 4 p4BufferedCircuit (fun i => decide (2 ≤ i)) = 0 := by
  decide

lemma p4_buffered_dirty_at_zero :
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (fun i => decide (i = 0)) = true ∧
    PEqualNP.MetaComplexity.circuitFun 4 p4BufferedCircuit
      (fun i => decide (i = 0)) = false := by
  decide

lemma p4_buffered_accepts_two_repeated_edges :
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (PEqualNP.EdgeOwnership.pairInput 0 2) = true ∧
    PEqualNP.EdgeOwnership.gateVal 4 p4BufferedCircuit 0
      (PEqualNP.EdgeOwnership.pairInput 0 3) = true ∧
    PEqualNP.ReadK.readsAtMost p4BufferedCircuit 4 [0, 2] 1 = false ∧
    PEqualNP.ReadK.readsAtMost p4BufferedCircuit 4 [0, 3] 1 = false := by
  decide

end PEqualNP.Outside.L_meta_4675_aux
