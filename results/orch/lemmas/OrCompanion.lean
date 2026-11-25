import Mathlib

namespace PEqualNP.Outside.L_meta_2592_aux.OrCompanion

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def inputBelow (x y : Fin 10 → Bool) : Prop := ∀ i, x i = true → y i = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma extend_small_independent : ∀ x : Fin 10 → Bool,
    x 0 = false → target x = false → (List.ofFn x).count true ≤ 2 →
      ∃ v : Fin 10, (v = 1 ∨ v = 4 ∨ v = 5) ∧
        let y := Function.update x v true
        y 0 = false ∧ inputBelow x y ∧ target y = false ∧
          target (Function.update y 0 true) = true := by
  unfold inputBelow
  decide +kernel

lemma companion_zero_at_sensitive_inputs
    (A B : (Fin 10 → Bool) → Bool)
    (R : (Fin 10 → Bool) → Bool → Bool → Bool)
    (mono : ∀ x, R x true false = true → R x true true = true)
    (cofactor0 : ∀ x, x 0 = false → R x (A x) (B x) = target x)
    (cofactor1 : ∀ x, x 0 = false → R x true false = target (Function.update x 0 true))
    (x : Fin 10 → Bool) (hx : x 0 = false) (zero : target x = false)
    (one : target (Function.update x 0 true) = true) : A x = false := by
  cases ha : A x with
  | false => rfl
  | true =>
    have hlow : R x true false = true := (cofactor1 x hx).trans one
    have hfull : R x true (B x) = true := by
      cases hb : B x with
      | false => exact hlow
      | true => exact mono x hlow
    have hzero : R x true (B x) = false := by
      simpa [ha] using (cofactor0 x hx).trans zero
    rw [hzero] at hfull
    contradiction

lemma companion_zero_on_small_independent
    (A B : (Fin 10 → Bool) → Bool)
    (R : (Fin 10 → Bool) → Bool → Bool → Bool)
    (monoA : ∀ x y, inputBelow x y → A x = true → A y = true)
    (monoR : ∀ x, R x true false = true → R x true true = true)
    (cofactor0 : ∀ x, x 0 = false → R x (A x) (B x) = target x)
    (cofactor1 : ∀ x, x 0 = false → R x true false = target (Function.update x 0 true)) :
    ∀ x, x 0 = false → target x = false → (List.ofFn x).count true ≤ 2 → A x = false := by
  intro x hx ht hc
  obtain ⟨v, _, hy0, hxy, hy, hy'⟩ := extend_small_independent x hx ht hc
  have hz := companion_zero_at_sensitive_inputs A B R monoR cofactor0 cofactor1
    (Function.update x v true) hy0 hy hy'
  cases ha : A x with
  | false => rfl
  | true =>
    have := monoA x (Function.update x v true) hxy ha
    rw [hz] at this
    contradiction

end PEqualNP.Outside.L_meta_2592_aux.OrCompanion
