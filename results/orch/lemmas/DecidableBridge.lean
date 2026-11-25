import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.DecidableBridge

universe u

lemma transport {α : Type u} (P : DecidableEq α → Prop)
    (d₁ d₂ : DecidableEq α) (h : P d₁) : P d₂ := by
  have he : d₁ = d₂ := Subsingleton.elim _ _
  exact he ▸ h

end PEqualNP.Outside.L_meta_9502.DecidableBridge
