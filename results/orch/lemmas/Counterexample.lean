import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_sanity

open PEqualNP.CircuitLowerBounds

def p4Circuit : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩], 7⟩

def p4Edges : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 1)}

lemma p4_isAO2 : PEqualNP.TopForm.IsAO2 4 p4Circuit := by decide

lemma p4_no_four_cycle :
    ∀ (a a' : Fin 2) (b b' : Fin 2), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ p4Edges ∧ (a, b') ∈ p4Edges ∧
        (a', b) ∈ p4Edges ∧ (a', b') ∈ p4Edges) := by decide

lemma p4_computes :
    ∀ x : Fin 4 → Bool, PEqualNP.MetaComplexity.circuitFun 4 p4Circuit x =
      decide (∃ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges ∧
        x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 2 b) = true) := by decide

lemma p4_no_mixing :
    PEqualNP.TwoColour.tCount 4 p4Circuit (fun i => decide (2 ≤ i)) = 0 := by decide

lemma p4_size : p4Circuit.size = 4 := by decide

lemma p4_and_output :
    (PEqualNP.MetaComplexity.NestedCover.gateAt p4Circuit 3).op = GateOp.and := by rfl

lemma p4_bound_tight :
    ∃ S : Finset (Fin 4),
      (∀ (a : Fin 2) (b : Fin 2), (a, b) ∈ p4Edges →
        Fin.castAdd 2 a ∈ S ∨ Fin.natAdd 2 b ∈ S) ∧
      p4Edges.card + S.card = p4Circuit.size + 1 := by
  refine ⟨{0, 1}, ?_, ?_⟩
  · decide
  · decide

end PEqualNP.Outside.L_meta_4675_sanity
