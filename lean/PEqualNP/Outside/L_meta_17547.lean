import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17547_aux

theorem key (x3 : List ℕ → Bool × Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ) :
    ∀ (x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x1 : List ℕ) (i : ℕ), i < x1.length →
    (List.foldl (fun (x5 : List ℕ) (x6 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ++ [x3 x5 x6]) x1 x2).getD i (0 : ℕ) = x1.getD i (0 : ℕ) := by
  intro x2
  induction x2 with
  | nil => intro x1 i h; rfl
  | cons a t ih =>
    intro x1 i h
    simp only [List.foldl_cons]
    rw [ih (x1 ++ [x3 x1 a]) i (by simp; omega)]
    rw [List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_17547_aux

theorem PEqualNP.Outside.L_meta_17547 : ∀ (x1 : List ℕ) (x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x3 : List ℕ → Bool × Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ) (x4 : Fin x1.length), (List.foldl (fun (x5 : List ℕ) (x6 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ++ [x3 x5 x6]) x1 x2).getD ↑x4 (0 : ℕ) = x1.getD ↑x4 (0 : ℕ) := by
  intro x1 x2 x3 x4
  exact PEqualNP.Outside.L_meta_17547_aux.key x3 x2 x1 x4 x4.isLt
