import Mathlib

namespace PEqualNP.Outside.L_meta_3178_support

def edge (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def mask (j i : Fin 9) : Nat :=
  (if i = j then [0, 1, 9, 5, 1, 1, 257, 5, 9]
   else [0, 1, 2, 4, 1, 1, 2, 4, 8]).getD i.val 0

def lower (j i k : Fin 9) : Bool :=
  (mask j i).testBit k.val

def upper (j i : Fin 9) : Fin 9 → Bool :=
  Function.update (lower j i) i true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma certificate : ∀ j i : Fin 9, j ≠ 0 → i ≠ 0 →
    lower j i i = false ∧ upper j i i = true ∧
    (∀ k : Fin 9, k ≠ i → lower j i k = upper j i k) ∧
    (!(lower j i 0)) = (!(upper j i 0)) ∧
    (lower j i 0 || lower j i j) = (upper j i 0 || upper j i j) ∧
    edge (lower j i) ≠ edge (upper j i) := by
  decide +kernel

end PEqualNP.Outside.L_meta_3178_support

theorem PEqualNP.Outside.L_meta_3178_support :
    ∀ j i : Fin 9, j ≠ 0 → i ≠ 0 →
      ∃ x y : Fin 9 → Bool,
        x i = false ∧ y i = true ∧
        (∀ k : Fin 9, k ≠ i → x k = y k) ∧
        (!x 0) = (!y 0) ∧ (x 0 || x j) = (y 0 || y j) ∧
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
         x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
         x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 ||
         y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 ||
         y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5) := by
  intro j i hj hi
  exact ⟨PEqualNP.Outside.L_meta_3178_support.lower j i, PEqualNP.Outside.L_meta_3178_support.upper j i,
    PEqualNP.Outside.L_meta_3178_support.certificate j i hj hi⟩
