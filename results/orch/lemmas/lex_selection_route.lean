import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.normalmin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma least_measure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (measure : Circuit → ℕ) (C₀ : Circuit)
    (minimum₀ : IsMinimalMonoCircuit n C₀)
    (correct₀ : circuitFun n C₀ = graphFun G ∅) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
      C.size = C₀.size ∧
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
        D.size ≤ C.size → measure C ≤ measure D := by
  classical
  let admissible (k : ℕ) := ∃ D : Circuit,
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C₀.size ∧ measure D = k
  have feasible : ∃ k : ℕ, admissible k :=
    ⟨measure C₀, C₀, minimum₀.1, correct₀, le_rfl, rfl⟩
  obtain ⟨C, mono, correct, bound, value⟩ := Nat.find_spec feasible
  have size : C.size = C₀.size :=
    Nat.le_antisymm bound (minimum₀.2 C mono (correct.trans correct₀.symm))
  have minimum : IsMinimalMonoCircuit n C := by
    refine ⟨mono, ?_⟩
    intro D monoD same
    exact bound.trans (minimum₀.2 D monoD (same.trans (correct.trans correct₀.symm)))
  refine ⟨C, minimum, correct, size, ?_⟩
  intro D monoD correctD boundD
  rw [value]
  apply Nat.find_min' feasible
  exact ⟨D, monoD, correctD, boundD.trans bound, rfl⟩

lemma least_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C₀ : Circuit) (minimum₀ : IsMinimalMonoCircuit n C₀)
    (correct₀ : circuitFun n C₀ = graphFun G ∅) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
      C.size = C₀.size ∧
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
        D.size ≤ C.size → (junk G C).card ≤ (junk G D).card :=
  least_measure G (fun D => (junk G D).card) C₀ minimum₀ correct₀

end PEqualNP.Outside.L_meta_1772_aux.normalmin
