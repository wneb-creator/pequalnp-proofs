import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.TopFormMinimization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour

lemma exists_min_andPairs (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (f : (Fin n → Bool) → Bool) (hAO : IsAO2 n C)
    (hf : circuitFun n C = f) (hz : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧ ∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f →
        tCount n D' s = 0 → D'.size ≤ C.size → andPairs n D ≤ andPairs n D' := by
  classical
  let Good (D : Circuit) : Prop := IsAO2 n D ∧ circuitFun n D = f ∧
    tCount n D s = 0 ∧ D.size ≤ C.size
  have hex : ∃ k : ℕ, ∃ D : Circuit, Good D ∧ andPairs n D = k :=
    ⟨andPairs n C, C, ⟨hAO, hf, hz, le_rfl⟩, rfl⟩
  obtain ⟨D, hD, hk⟩ := Nat.find_spec hex
  refine ⟨D, hD.1, hD.2.1, hD.2.2.1, hD.2.2.2, ?_⟩
  intro D' hAO' hf' hz' hsize
  rw [hk]
  exact Nat.find_min' hex ⟨D', ⟨hAO', hf', hz', hsize⟩, rfl⟩

end PEqualNP.Outside.L_meta_4675.TopFormMinimization
