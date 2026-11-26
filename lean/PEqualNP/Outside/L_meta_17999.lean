import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17999_aux

set_option maxRecDepth 9000 in
set_option maxHeartbeats 2400000 in
theorem Ant_R_meta_8913_645_intersection : (
      let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      ∀ p q l m : Fin 13, p ≠ q → I p l → I q l → I p m → I q m → l = m) := by
  set_option maxHeartbeats 20000 in
  first
  | omega
  | (intros; omega)
  | decide
  | (intros; simp_all)
  | (intros; simp_all; omega)
  | (intros; aesop)

end PEqualNP.Outside.L_meta_17999_aux

theorem PEqualNP.Outside.L_meta_17999 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 ≠ x3 → x1 x2 x4 → x1 x3 x4 → x1 x2 x5 → x1 x3 x5 → x4 = x5 := by
  first
  | exact PEqualNP.Outside.L_meta_17999_aux.Ant_R_meta_8913_645_intersection
  | (intros; apply PEqualNP.Outside.L_meta_17999_aux.Ant_R_meta_8913_645_intersection <;> assumption)
  | simpa using PEqualNP.Outside.L_meta_17999_aux.Ant_R_meta_8913_645_intersection
