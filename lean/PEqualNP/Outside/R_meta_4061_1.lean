import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4061_1
    (hA : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
          ∀ v : Fin 26, v = 0 ∨ v = 1 ∨ v = 14 →
            PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 v) = false)
    (hB : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (0 : ℕ) ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
          ∀ v : Fin 26, v = 0 ∨ v = 1 ∨ v = 14 →
            PEqualNP.EdgeOwnership.gateVal 26 C j (PEqualNP.EdgeOwnership.pairInput 0 v) = false) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x9 : Fin (26 : ℕ)), x9 = (0 : Fin (26 : ℕ)) ∨ x9 = (1 : Fin (26 : ℕ)) ∨ x9 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x9) = Bool.false := by
  intro G _ adj C least j hj hop v hv
  by_cases hmem : (0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs
  · exact hA G adj C least j hj hop hmem v hv
  · exact hB G adj C least j hj hop hmem v hv
