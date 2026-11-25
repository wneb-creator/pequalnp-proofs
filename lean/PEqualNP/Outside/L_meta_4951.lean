import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4951

def wit : List ℕ := [2, 20, 2, 16, 10, 130, 2, 20, 10, 20, 1, 9, 4, 1, 1, 257, 4, 9, 2, 9, 2, 18, 8, 9, 2, 34, 8, 16, 4, 18, 4, 5, 5, 18, 4, 36, 10, 1, 8, 5, 1, 1, 10, 5, 8, 130, 1, 9, 5, 1, 1, 130, 5, 9, 2, 257, 2, 18, 10, 130, 2, 34, 10, 20, 4, 34, 4, 5, 5, 34, 4, 32, 10, 9, 8, 36, 8, 9, 10, 32, 8]

end PEqualNP.Outside.L_meta_4951

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_4951 : ∀ (x1 x2 : Fin (9 : ℕ)),   ∃ (x3 : Fin (9 : ℕ) → Bool),     have x4 : (Fin (9 : ℕ) → Bool) → Bool := fun (x4 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (10 : ℕ)));     x4 x3 = Bool.false ∧ (x4 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = x1) || x3 x5) = Bool.true ∧ (x4 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = x2) || x3 x5) = Bool.true := by
  intro x1 x2
  refine ⟨fun i => (PEqualNP.Outside.L_meta_4951.wit.getD (9 * x1.val + x2.val) 0).testBit i.val, ?_⟩
  revert x1 x2
  decide
