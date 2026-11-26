import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3837_1
    (inverted :
      have edge : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      have input : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ C : Circuit, FanInTwo C → C.size = 13 → ∀ j : Fin 11,
        ∃ x : Fin 9 → Bool, C.eval (input x ++ [!(input x).getD j.val false]) ≠ edge x)
    (bypass :
      ∀ C : Circuit, FanInTwo C → ∀ j : Fin 11,
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (w : List Bool) (b : Bool), w.length = 10 →
            D.eval (w ++ [b]) = C.eval (w ++ [w.getD j.val false])) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8 := by
  dsimp only
  intro C hC hsize j inv
  cases inv
  · obtain ⟨D, hD, hsz, heval⟩ := bypass C hC j
    obtain ⟨x, hx⟩ := inverted D hD (hsz.trans hsize) 0
    let w := List.ofFn x ++ [x 0 || x 6]
    have h := heval w (!(w.getD 0 false)) (by simp [w])
    refine ⟨x, ?_⟩
    simp only [Bool.false_bne]
    change C.eval (w ++ [w.getD j.val false]) ≠ _
    rw [← h]
    exact hx
  · simpa only [Bool.true_bne] using inverted C hC hsize j
