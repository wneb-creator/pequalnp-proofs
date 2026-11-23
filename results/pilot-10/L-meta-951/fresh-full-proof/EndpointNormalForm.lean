import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951.Endpoint

variable {α : Type*} [Preorder α] [OrderBot α] [OrderTop α]

def select (h a b : α → Bool) (x : α) : Bool :=
  if h x then a x else b x

omit [OrderBot α] in
theorem lower_eq_false_of_top (h a b : α → Bool)
    (ha : Monotone a) (hh : h ⊤ = true)
    (hf : select h a b ⊤ = false) (x : α) : a x = false := by
  have hat : a ⊤ = false := by simpa [select, hh] using hf
  have hle := ha (show x ≤ ⊤ from le_top)
  rw [hat] at hle
  cases hx : a x <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) hle

omit [OrderTop α] in
theorem upper_eq_true_of_bot (h a b : α → Bool)
    (hb : Monotone b) (hh : h ⊥ = false)
    (hf : select h a b ⊥ = true) (x : α) : b x = true := by
  have hbb : b ⊥ = true := by simpa [select, hh] using hf
  have hle := hb (show ⊥ ≤ x from bot_le)
  rw [hbb] at hle
  cases hx : b x <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) hle

omit [OrderBot α] in
theorem false_top_normal_form (h a b : α → Bool)
    (ha : Monotone a) (hh : h ⊤ = true)
    (hf : select h a b ⊤ = false) (x : α) :
    select h a b x = (!h x && b x) := by
  have hx := lower_eq_false_of_top h a b ha hh hf x
  simp [select, hx]

omit [OrderTop α] in
theorem true_bot_normal_form (h a b : α → Bool)
    (hb : Monotone b) (hh : h ⊥ = false)
    (hf : select h a b ⊥ = true) (x : α) :
    select h a b x = (!h x || a x) := by
  have hx := upper_eq_true_of_bot h a b hb hh hf x
  cases hhx : h x <;> simp [select, hx, hhx]

theorem reversed_endpoints_alias (h a b : α → Bool)
    (ha : Monotone a) (hb : Monotone b)
    (hhb : h ⊥ = false) (hht : h ⊤ = true)
    (hfb : select h a b ⊥ = true) (hft : select h a b ⊤ = false)
    (x : α) : select h a b x = !h x := by
  have hx := lower_eq_false_of_top h a b ha hht hft x
  have hy := upper_eq_true_of_bot h a b hb hhb hfb x
  cases hhx : h x <;> simp [select, hx, hy, hhx]

theorem opposite_bias_and_alias (h a b c d : α → Bool)
    (ha : Monotone a) (hd : Monotone d)
    (hhb : h ⊥ = false) (hht : h ⊤ = true)
    (hl : select h a b ⊤ = false) (hu : select h c d ⊥ = true)
    (x : α) :
    (select h a b x && select h c d x) = select h a b x := by
  rw [false_top_normal_form h a b ha hht hl x,
    true_bot_normal_form h c d hd hhb hu x]
  cases h x <;> simp

theorem opposite_bias_or_alias (h a b c d : α → Bool)
    (ha : Monotone a) (hd : Monotone d)
    (hhb : h ⊥ = false) (hht : h ⊤ = true)
    (hl : select h a b ⊤ = false) (hu : select h c d ⊥ = true)
    (x : α) :
    (select h a b x || select h c d x) = select h c d x := by
  rw [false_top_normal_form h a b ha hht hl x,
    true_bot_normal_form h c d hd hhb hu x]
  cases h x <;> simp

end PEqualNP.Outside.L_meta_951.Endpoint
