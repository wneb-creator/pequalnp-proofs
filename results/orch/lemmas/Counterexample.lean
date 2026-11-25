import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

lemma edgeless_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ u v : Fin n, ¬ G.Adj u v) :
    ∃ C : Circuit, C.gates = [] ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit, C.size ≤ D.size := by
  refine ⟨⟨[], n⟩, rfl, ?_, ?_⟩
  · intro x
    have hfalse : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
      rintro ⟨i, j, hij, _, _⟩
      exact hG i j hij
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hfalse]
  · intro D
    simp [Circuit.size]

end PEqualNP.Outside.L_meta_1031
