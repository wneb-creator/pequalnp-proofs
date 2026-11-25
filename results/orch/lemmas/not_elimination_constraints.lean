import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma neutral_pin_false (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (a b : Bool)
    (h0 : G a b = false) (h1 : G true false = true) : a = false := by
  cases a with
  | false => rfl
  | true =>
    have hfb : (false : Bool) ≤ b := by cases b <;> decide
    have h := hG true hfb
    rw [h0, h1] at h
    exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)

lemma neutral_pin_not_sensitive (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (b : Bool) :
    ¬ (G true b = false ∧ G true false = true) := by
  rintro ⟨h0, h1⟩
  have h := neutral_pin_false G hG true b h0 h1
  cases h

end PEqualNP.Outside.L_meta_2592_aux
