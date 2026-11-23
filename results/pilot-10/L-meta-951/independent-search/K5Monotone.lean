import Mathlib
import PEqualNP.Outside.L_meta_924

namespace Pilot10Independent

def k5Stars : Fin 5 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {0, 4, 5, 6}, {1, 4, 7, 8}, {2, 5, 7, 9}, {3, 6, 8, 9}]

lemma k5Stars_card : ∀ i : Fin 5, (k5Stars i).card = 3 + 1 := by
  decide

lemma k5Stars_inter : ∀ i j : Fin 5, i ≠ j →
    (k5Stars i ∩ k5Stars j).card = 1 := by
  decide

theorem k5Stars_monotone_bound
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 5 → ℕ)
    (hgate : ∀ g ∈ gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (w : Fin 5) (x : Fin 10 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ k5Stars w, x v = true)) :
    15 ≤ gates.length := by
  exact PEqualNP.Outside.L_meta_924 3 10 5 10 0 k5Stars
    (by decide) (by decide) k5Stars_card k5Stars_inter gates out hgate
    (fun w x _ => hout w x) 3 (by decide) (by decide)

end Pilot10Independent
