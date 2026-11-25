import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2592_aux

lemma remove_not_from_true_certificates {α : Type*} (r : α → α → Prop)
    (F H : α → Bool) (Q : α → Bool → Bool)
    (mono : ∀ b x y, r x y → Q x b = true → Q y b = true)
    (bitMono : ∀ x, Q x false = true → Q x true = true)
    (correct : ∀ x, Q x (!H x) = F x)
    (covered : ∀ x, F x = true → ∃ y, r y x ∧ F y = true ∧ H y = true) :
    ∀ x, Q x false = F x := by
  intro x
  cases hx : F x with
  | false =>
    cases hq : Q x false with
    | false => rfl
    | true =>
      have ht : Q x (!H x) = true := by
        cases hh : H x with
        | false => simpa [hh] using bitMono x hq
        | true => simpa [hh] using hq
      have : F x = true := (correct x).symm.trans ht
      simp [hx] at this
  | true =>
    obtain ⟨y, hyx, hy, hh⟩ := covered x hx
    have hq : Q y false = true := by
      simpa [hh] using (correct y).trans hy
    exact mono false y x hyx hq

lemma remove_not_from_false_certificates {α : Type*} (r : α → α → Prop)
    (F H : α → Bool) (Q : α → Bool → Bool)
    (mono : ∀ b x y, r x y → Q x b = true → Q y b = true)
    (bitMono : ∀ x, Q x false = true → Q x true = true)
    (correct : ∀ x, Q x (!H x) = F x)
    (covered : ∀ x, F x = false → ∃ y, r x y ∧ F y = false ∧ H y = false) :
    ∀ x, Q x true = F x := by
  intro x
  cases hx : F x with
  | false =>
    obtain ⟨y, hxy, hy, hh⟩ := covered x hx
    have hq : Q y true = false := by
      simpa [hh] using (correct y).trans hy
    cases hxt : Q x true with
    | false => rfl
    | true =>
      have : Q y true = true := mono true x y hxy hxt
      simp [hq] at this
  | true =>
    have hq : Q x (!H x) = true := (correct x).trans hx
    cases hh : H x with
    | false => simpa [hh] using hq
    | true => exact bitMono x (by simpa [hh] using hq)

lemma final_and_after_not_fails (H A : (Fin 10 → Bool) → Bool)
    (hH : H (fun _ => true) = true) :
    (!(H (fun _ => true)) && A (fun _ => true)) ≠ true := by
  simp [hH]

lemma final_or_after_not_fails (H A : (Fin 10 → Bool) → Bool)
    (hH : H (fun _ => false) = false) :
    (!(H (fun _ => false)) || A (fun _ => false)) ≠ false := by
  simp [hH]

end PEqualNP.Outside.L_meta_2592_aux
