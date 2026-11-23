import Mathlib

namespace PEqualNP.Outside.L_meta_951

/-- One ordinary Boolean channel together with an antitone selector cannot
produce two incomparable nonzero output vectors above a zero baseline. -/
theorem antitone_bit_bottleneck {α : Type*} [PartialOrder α] [OrderBot α]
    (H : Bool × Bool → α) (hH : Monotone H)
    (b₀ b₁ b₂ z₀ z₁ z₂ : Bool)
    (h₀ : H (b₀, z₀) = ⊥)
    (hz₁ : z₁ ≤ z₀) (hz₂ : z₂ ≤ z₀)
    (hn₁ : H (b₁, z₁) ≠ ⊥) (hn₂ : H (b₂, z₂) ≠ ⊥) :
    H (b₁, z₁) ≤ H (b₂, z₂) ∨ H (b₂, z₂) ≤ H (b₁, z₁) := by
  have hb₁ : b₁ = true := by
    cases b₁
    · exfalso
      apply hn₁
      apply le_antisymm _ bot_le
      calc
        H (false, z₁) ≤ H (b₀, z₀) := hH ⟨by change false ≤ b₀; exact Bool.false_le _, hz₁⟩
        _ = ⊥ := h₀
    · rfl
  have hb₂ : b₂ = true := by
    cases b₂
    · exfalso
      apply hn₂
      apply le_antisymm _ bot_le
      calc
        H (false, z₂) ≤ H (b₀, z₀) := hH ⟨by change false ≤ b₀; exact Bool.false_le _, hz₂⟩
        _ = ⊥ := h₀
    · rfl
  subst b₁
  subst b₂
  rcases le_total z₁ z₂ with h | h
  · exact Or.inl (hH ⟨le_rfl, h⟩)
  · exact Or.inr (hH ⟨le_rfl, h⟩)

end PEqualNP.Outside.L_meta_951
