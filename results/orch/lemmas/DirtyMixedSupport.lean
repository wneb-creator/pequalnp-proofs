import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma rejectedOuter_mixedSupport {α : Type} (A B S : α → Prop) (l c d r : α)
    (hl : (A l ∨ A c) ∧ (B l ∨ B c) ∧ (S l ∨ S c))
    (hr : (A d ∨ A r) ∧ (B d ∨ B r) ∧ (S d ∨ S r))
    (outer : ¬ ((A l ∨ A r) ∧ (B l ∨ B r) ∧ (S l ∨ S r))) :
    (A c ∧ A d) ∨ (B c ∧ B d) ∨ (S c ∧ S d) := by
  have split : ∀ P : α → Prop, (P l ∨ P c) → (P d ∨ P r) →
      ¬ (P l ∨ P r) → P c ∧ P d := by
    intro P hleft hright hout
    exact ⟨hleft.resolve_left (fun h => hout (Or.inl h)),
      hright.resolve_right (fun h => hout (Or.inr h))⟩
  by_cases ha : A l ∨ A r
  · by_cases hb : B l ∨ B r
    · exact Or.inr (Or.inr (split S hl.2.2 hr.2.2 (fun hs => outer ⟨ha, hb, hs⟩)))
    · exact Or.inr (Or.inl (split B hl.2.1 hr.2.1 hb))
  · exact Or.inl (split A hl.1 hr.1 ha)

lemma mixedSupport_noCross {α : Type} (R : α → α → Prop) (A B : α → Prop)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (cross : ∀ u v, A u → B v → R u v)
    (c d : α) (hcd : R c d) (hc : A c) (hd : A d) :
    ∀ v, ¬ B v := by
  intro v hv
  exact triangle c d v hcd (cross d v hd hv) (cross c v hc hv)

lemma unionSupport_mixed {α ι : Type} (S : ι → α → Prop) (c d : α)
    (hc : ∃ i, S i c) (hd : ∃ j, S j d) :
    (∃ i, S i c ∧ S i d) ∨ (∃ i j, i ≠ j ∧ S i c ∧ S j d) := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, hj⟩ := hd
  by_cases hij : i = j
  · exact Or.inl ⟨j, hij ▸ hi, hj⟩
  · exact Or.inr ⟨i, j, hij, hi, hj⟩

end PEqualNP.Outside.L_meta_2732_aux
