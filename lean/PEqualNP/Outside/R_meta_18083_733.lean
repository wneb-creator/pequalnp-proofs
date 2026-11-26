import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-18083 by the presence of an AND gate.  A fan-in-two circuit with no AND gate
-- is a single OR of the input wires, so the negative side is a genuinely restricted class
-- and the positive side is the case where the AND structure carries the argument.
theorem PEqualNP.Outside.R_meta_18083_733
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ))))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (¬ (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (10 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (10 : ℕ) (x5 % (10 : ℕ))) := by
  intro x1 hp1 hp2
  by_cases h : (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · exact h1 x1 hp1 hp2 h
  · exact h2 x1 hp1 hp2 h
