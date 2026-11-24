import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.StructuralTwoCenters

lemma filtered_product_identity (u v a b : Bool)
    (ha : a = true → u = true) (hb : b = true → v = true) :
    ((u && v) && (a || b)) = ((a && v) || (b && u)) := by
  cases u <;> cases v <;> cases a <;> cases b <;> simp_all

lemma filtered_product_of_membership {n : ℕ} (A B : Finset (Fin n))
    (a b : Fin n) (ha : a ∈ A) (hb : b ∈ B) (x : Fin n → Bool) :
    (((decide (∃ u ∈ A, x u = true)) && (decide (∃ v ∈ B, x v = true))) &&
      (x a || x b)) =
      ((x a && decide (∃ v ∈ B, x v = true)) ||
      (x b && decide (∃ u ∈ A, x u = true))) := by
  apply filtered_product_identity
  · intro h
    exact decide_eq_true ⟨a, ha, h⟩
  · intro h
    exact decide_eq_true ⟨b, hb, h⟩

lemma center_and_product (u v a : Bool) (ha : a = true → u = true) :
    (a && (u && v)) = (a && v) := by
  cases u <;> cases v <;> cases a <;> simp_all

lemma one_center_mixed_product (u v a s : Bool) (ha : a = true → u = true) :
    (a && (s || (u && v))) = (a && (s || v)) := by
  cases u <;> cases v <;> cases a <;> cases s <;> simp_all

end PEqualNP.Outside.L_meta_1477.StructuralTwoCenters
