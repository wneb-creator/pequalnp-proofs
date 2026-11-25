import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

def IsMonotoneBinary (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma exists_minimum_of_nonempty (n : ℕ) (f : (Fin n → Bool) → Bool)
    (h : ∃ C : Circuit, IsMonotoneBinary C ∧ ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ C : Circuit, IsMonotoneBinary C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧
      ∀ D : Circuit, IsMonotoneBinary D → (∀ x, D.eval (List.ofFn x) = f x) →
        C.size ≤ D.size := by
  classical
  have hex : ∃ s : ℕ, ∃ C : Circuit, IsMonotoneBinary C ∧
      (∀ x, C.eval (List.ofFn x) = f x) ∧ C.size = s := by
    obtain ⟨C, hC, hf⟩ := h
    exact ⟨C.size, C, hC, hf, rfl⟩
  obtain ⟨C, hC, hf, hs⟩ := Nat.find_spec hex
  refine ⟨C, hC, hf, ?_⟩
  intro D hD hDf
  rw [hs]
  exact Nat.find_min' hex ⟨D, hD, hDf, rfl⟩

end PEqualNP.Outside.L_meta_1031
