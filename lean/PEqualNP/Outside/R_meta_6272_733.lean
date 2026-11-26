import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-6272 by the presence of an AND gate.  A circuit with no AND gate is a single
-- OR of the input wires, so the negative side is a genuinely restricted class and the
-- positive side is the case where the AND structure carries the argument.
theorem PEqualNP.Outside.R_meta_6272_733
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (39 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (¬ (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → (39 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (39 : ℕ) ≤ x1.size := by
  intro x1 hp1 hp2
  by_cases h : (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · exact h1 x1 hp1 hp2 h
  · exact h2 x1 hp1 hp2 h
