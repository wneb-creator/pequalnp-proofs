import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.SemanticFactorization

def binary (op a b : Bool) : Bool := if op then a || b else a && b

lemma mate_at_sensitive_input {n : ℕ} (v : Fin n) (op : Bool)
    (F H : (Fin n → Bool) → Bool) (Q : (Fin n → Bool) → Bool → Bool)
    (H_independent : ∀ x, H (Function.update x v true) = H x)
    (Q_independent : ∀ x b, Q (Function.update x v true) b = Q x b)
    (computes : ∀ x, Q x (binary op (x v) (H x)) = F x)
    (x : Fin n → Bool) (input_false : x v = false)
    (output_false : F x = false) (output_true : F (Function.update x v true) = true) :
    H x = !op := by
  have initial := computes x
  have changed := computes (Function.update x v true)
  rw [input_false, output_false] at initial
  simp [H_independent, Q_independent, output_true] at changed
  cases op <;> cases hh : H x <;> simp_all [binary]

lemma pull_absorbed_term {α : Type*} (F H X : α → Bool) (Q : α → Bool → Bool)
    (computes : ∀ x, Q x (X x || H x) = F x)
    (absorbed : ∀ x, H x = true → F x = true) :
    ∀ x, F x = (H x || Q x (X x)) := by
  intro x
  cases hx : H x with
  | false => simpa [hx] using (computes x).symm
  | true => simp [absorbed x hx]

end PEqualNP.Outside.L_meta_2592_aux.SemanticFactorization
