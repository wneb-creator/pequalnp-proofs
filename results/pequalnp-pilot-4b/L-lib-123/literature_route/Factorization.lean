import Mathlib

namespace PEqualNP.Outside.LiteratureRoute

lemma equality_not_a_rectangle :
    ¬ ∃ P Q : Bool → Prop, ∀ x y : Bool, (x = y ↔ P x ∧ Q y) := by
  rintro ⟨P, Q, h⟩
  have hfalse := (h false false).mp rfl
  have htrue := (h true true).mp rfl
  have hbad := (h false true).mpr ⟨hfalse.1, htrue.2⟩
  cases hbad

lemma checkpoint_balance (b L T C : ℕ)
    (hvisits : T ≤ b * C) (hlocal : b * T ≤ L * C) (htrace : L ≤ C) :
    T * T ≤ C * C * C := by
  have h₁ := Nat.mul_le_mul_right T hvisits
  have h₂ := Nat.mul_le_mul_left C hlocal
  have h₃ := Nat.mul_le_mul_right (C * C) htrace
  nlinarith

lemma quadratic_normalization_erases_two_thirds (T C : ℕ)
    (h : (T * T) * (T * T) ≤ C * C * C) (hT : 1 ≤ T) : T ≤ C := by
  by_contra hnot
  have hlt : C < T := by omega
  have hC : C * C * C < T * T * T := by
    simpa [pow_succ] using Nat.pow_lt_pow_left hlt (by decide : 3 ≠ 0)
  have hTpow : T * T * T ≤ T * T * (T * T) := by
    have : T ≤ T * T := by nlinarith
    nlinarith
  nlinarith

lemma equality_cover_injection (A C : Type*)
    (P Q : C → A → Prop)
    (hsound : ∀ c x y, P c x → Q c y → x = y)
    (hcomplete : ∀ x, ∃ c, P c x ∧ Q c x) :
    ∃ f : A → C, Function.Injective f := by
  classical
  choose f hf using hcomplete
  refine ⟨f, ?_⟩
  intro x y hxy
  exact hsound (f x) x y (hf x).1 (hxy ▸ (hf y).2)

lemma equality_cover_card (A C : Type*) [Fintype A] [Fintype C]
    (P Q : C → A → Prop)
    (hsound : ∀ c x y, P c x → Q c y → x = y)
    (hcomplete : ∀ x, ∃ c, P c x ∧ Q c x) :
    Fintype.card A ≤ Fintype.card C := by
  obtain ⟨f, hf⟩ := equality_cover_injection A C P Q hsound hcomplete
  exact Fintype.card_le_of_injective f hf

lemma equality_cover_bits (b g : ℕ)
    (P Q : (Fin g → Bool) → (Fin b → Bool) → Prop)
    (hsound : ∀ c x y, P c x → Q c y → x = y)
    (hcomplete : ∀ x, ∃ c, P c x ∧ Q c x) : b ≤ g := by
  have hc := equality_cover_card (Fin b → Bool) (Fin g → Bool) P Q hsound hcomplete
  have hpow : 2 ^ b ≤ 2 ^ g := by simpa using hc
  by_contra hnot
  have hlt : g < b := by omega
  have := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
  omega

end PEqualNP.Outside.LiteratureRoute
