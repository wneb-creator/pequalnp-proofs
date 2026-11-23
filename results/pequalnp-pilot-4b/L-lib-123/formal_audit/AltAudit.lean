import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.Library

lemma alt_constant (j s : ℕ) (P : Prop) : Alt j s (fun _ => P) ↔ P := by
  classical
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
    simp only [Alt, ih, not_not]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      exact ⟨List.replicate s false, by simp, h⟩

lemma alt_three (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ y : List Bool, y.length = s ∧
      ∀ z : List Bool, z.length = s →
        ∃ w : List Bool, w.length = s ∧ P (y ++ z ++ w) := by
  classical
  simp [Alt, List.append_assoc]

lemma alt_congr_on_length (j s : ℕ) (P Q : List Bool → Prop)
    (h : ∀ w : List Bool, w.length = j * s → (P w ↔ Q w)) :
    Alt j s P ↔ Alt j s Q := by
  classical
  induction j generalizing P Q with
  | zero =>
    simpa only [Alt] using h [] (by simp)
  | succ j ih =>
    simp only [Alt]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    apply not_congr
    apply ih
    intro w hw
    apply not_congr
    apply h
    simp only [List.length_append, hy, hw, Nat.succ_mul]
    omega

lemma alt_constant_on_length (j s : ℕ) (P : List Bool → Prop) (A : Prop)
    (h : ∀ w : List Bool, w.length = j * s → (P w ↔ A)) :
    Alt j s P ↔ A :=
  (alt_congr_on_length j s P (fun _ => A) h).trans (alt_constant j s A)

end PEqualNP.Outside.L_lib_123_Audit
