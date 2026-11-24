import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_least_circuit (n : ℕ) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧
      ∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size := by
  classical
  let p : ℕ → Prop := fun s =>
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧ D.size = s
  have hp : ∃ s, p s := ⟨C.size, C, hC, hf, rfl⟩
  obtain ⟨D, hD, hDf, hsize⟩ := Nat.find_spec hp
  refine ⟨D, hD, hDf, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hp ⟨C, hC, hf, rfl⟩
  · intro E hE hEf
    rw [hsize]
    exact Nat.find_min' hp ⟨E, hE, hEf, rfl⟩

lemma false_circuit_read (n k : ℕ) (C : Circuit)
    (hC : ∀ x : Fin n → Bool, circuitFun n C x = false) :
    PEqualNP.ReadK.IsReadK n C k := by
  intro S hS
  have htrue := hS.1
  rw [hC] at htrue
  cases htrue

lemma normalize_of_least_read (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hread : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = f →
      (∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size) → PEqualNP.ReadK.IsReadK n D 2)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK n D 2 := by
  obtain ⟨D, hD, hDf, hsize, hleast⟩ := exists_least_circuit n f C hC hf
  exact ⟨D, hD, hDf, hsize, hread D hD hDf hleast⟩

end PEqualNP.Outside.L_meta_2584
