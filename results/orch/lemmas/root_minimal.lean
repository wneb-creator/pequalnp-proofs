import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_minimum (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hC : Monotone2 C) (hCf : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ D : Circuit, Monotone2 D ∧ (∀ x, D.eval (List.ofFn x) = f x) ∧
      ∀ E : Circuit, Monotone2 E → (∀ x, E.eval (List.ofFn x) = f x) →
        D.size ≤ E.size := by
  classical
  have hex : ∃ s : ℕ, ∃ D : Circuit,
      Monotone2 D ∧ (∀ x, D.eval (List.ofFn x) = f x) ∧ D.size = s :=
    ⟨C.size, C, hC, hCf, rfl⟩
  obtain ⟨D, hD, hf, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hf, fun E hE hEf => ?_⟩
  rw [hs]
  exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩

lemma edgeless (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : ∀ a b, ¬ G.Adj a b) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
      (∀ E : Circuit, Monotone2 E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) =
          decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) →
        D.size ≤ E.size) ∧
      ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
  · simp [Monotone2]
  · intro x
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hedge]
  · intro E _ _
    exact Nat.zero_le _
  · intro j g h
    simp at h

end PEqualNP.Outside.L_meta_1904
