import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2592

lemma input_not_irrelevant {n : ℕ} (i : Fin n)
    (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hmono : Monotone (fun x => H x (!(x i))))
    (hgate : ∀ x, Monotone (H x)) :
    ∀ x, H x false = H x true := by
  intro x
  apply le_antisymm
  · exact hgate x (by decide)
  · have hab : Function.update x i false ≤ Function.update x i true := by
      intro j
      by_cases hj : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hj]
    have h := hmono hab
    simpa only [Function.update_self, Bool.not_false, Bool.not_true, hignore] using h

lemma input_not_replace_false {n : ℕ} (i : Fin n)
    (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hmono : Monotone (fun x => H x (!(x i))))
    (hgate : ∀ x, Monotone (H x)) :
    ∀ x, H x (!(x i)) = H x false := by
  intro x
  cases hi : x i
  · simpa only [Bool.not_false] using (input_not_irrelevant i H hignore hmono hgate x).symm
  · simp

lemma input_not_cannot_compute {n : ℕ} (i : Fin n)
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hf : Monotone f)
    (hdep : ∃ x, f (Function.update x i false) ≠ f (Function.update x i true))
    (hgate : ∀ x, Monotone (H x)) :
    ¬ ∀ x, H x (!(x i)) = f x := by
  intro correct
  have hmono : Monotone (fun x => H x (!(x i))) := by
    simpa only [correct] using hf
  obtain ⟨x, hdiff⟩ := hdep
  apply hdiff
  rw [← correct, ← correct]
  simpa only [Function.update_self, Bool.not_false, Bool.not_true, hignore] using
    (input_not_irrelevant i H hignore hmono hgate x).symm

end PEqualNP.Outside.L_meta_2592
