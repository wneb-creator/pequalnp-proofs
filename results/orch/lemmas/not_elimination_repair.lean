import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma polarized_repair_bool (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (a b : Bool) (hba : b ≤ a)
    (hmono : G a b ≤ G true false) (x : Bool) :
    G (x || a) ((!x) && b) = G (x || a) b := by
  have hUp : G true false ≤ G true true := hG true (by decide)
  cases a <;> cases b <;> cases x
  all_goals try rfl
  all_goals try exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hba)
  exact le_antisymm hUp hmono

lemma polarized_repair {Y : Type*} (G : Y → Bool → Bool → Bool)
    (A B : Y → Bool) (hG : ∀ y p, Monotone (G y p))
    (hBA : ∀ y, B y ≤ A y)
    (hmono : ∀ y, G y (A y) (B y) ≤ G y true false) :
    ∀ y x, G y (x || A y) ((!x) && B y) = G y (x || A y) (B y) := by
  intro y x
  exact polarized_repair_bool (G y) (hG y) (A y) (B y) (hBA y) (hmono y) x

lemma nested_positive_repair (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (a : Bool)
    (hmono : G a a ≤ G true false) (x : Bool) :
    G (x || a) ((!x) && (x || a)) = G (x || a) a := by
  have hEq : ((!x) && (x || a)) = ((!x) && a) := by
    cases x <;> cases a <;> rfl
  rw [hEq]
  exact polarized_repair_bool G hG a a (le_refl a) hmono x

lemma nested_negative_repair (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (b : Bool)
    (hmono : G b b ≤ G true false) (x : Bool) :
    G (x || ((!x) && b)) ((!x) && b) = G (x || b) b := by
  have hEq : (x || ((!x) && b)) = (x || b) := by
    cases x <;> cases b <;> rfl
  rw [hEq]
  exact polarized_repair_bool G hG b b (le_refl b) hmono x

end PEqualNP.Outside.L_meta_2592_aux
