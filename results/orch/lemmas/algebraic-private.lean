import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

def rowNegative {p l : ℕ} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    Fin (p + l) → Bool :=
  Fin.addCases (fun a => decide ((a, b) ∉ E)) (fun j => decide (j = b))

lemma singleton_mem_row {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (a : Fin p) (b : Fin l)
    (ha : f (fun i => decide (i = Fin.castAdd l a)) = true)
    (hb : f (rowNegative E b) = false) : (a, b) ∈ E := by
  by_contra hab
  have hlift : ∀ i : Fin (p + l), decide (i = Fin.castAdd l a) = true →
      rowNegative E b i = true := by
    intro i hi
    have he : i = Fin.castAdd l a := of_decide_eq_true hi
    subst i
    simp [rowNegative, hab]
  have bad := hmono _ _ hlift ha
  rw [hb] at bad
  contradiction

lemma two_rows_support_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (b b' : Fin l) (hne : b ≠ b')
    (hb : f (rowNegative E b) = false)
    (hb' : f (rowNegative E b') = false) :
    (Finset.univ.filter fun a : Fin p =>
      f (fun i => decide (i = Fin.castAdd l a)) = true).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  have hon := (Finset.mem_filter.mp ha).2
  have hon' := (Finset.mem_filter.mp ha').2
  by_contra hne'
  exact h4 a a' b b' hne' hne
    ⟨singleton_mem_row E f hmono a b hon hb,
      singleton_mem_row E f hmono a b' hon hb',
      singleton_mem_row E f hmono a' b hon' hb,
      singleton_mem_row E f hmono a' b' hon' hb'⟩

end PEqualNP.Outside.L_meta_4675
