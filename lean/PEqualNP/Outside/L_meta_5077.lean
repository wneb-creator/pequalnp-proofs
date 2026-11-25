import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5077 : ∀ (x1 : Finset (Fin ((13 : ℕ) + (13 : ℕ)))), (∀ (x2 x3 : Fin (13 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ)) → Fin.castAdd (13 : ℕ) x2 ∈ x1 ∨ Fin.natAdd (13 : ℕ) x3 ∈ x1) → (13 : ℕ) ≤ x1.card := by
  classical
  intro S hS
  have key : ∀ l : Fin 13, Fin.castAdd 13 l ∈ S ∨ Fin.natAdd 13 l ∈ S := fun l => hS l l (Or.inl rfl)
  let f : Fin 13 → Fin (13 + 13) := fun l => if Fin.castAdd 13 l ∈ S then Fin.castAdd 13 l else Fin.natAdd 13 l
  have hf : ∀ l, f l ∈ S := by
    intro l
    by_cases h : Fin.castAdd 13 l ∈ S
    · simp only [f, if_pos h]; exact h
    · simp only [f, if_neg h]; exact (key l).resolve_left h
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases h1 : Fin.castAdd 13 a ∈ S <;> by_cases h2 : Fin.castAdd 13 b ∈ S <;>
      simp only [f, h1, h2, if_true, if_false] at hab <;>
      have hv := congrArg Fin.val hab <;>
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv <;>
      first
        | exact Fin.ext (by omega)
        | (exfalso; omega)
  have hcard := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := S) (fun l _ => hf l) hinj.injOn
  simpa using hcard
