import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.OneGateAfterNot

theorem and_not_bypass {α : Type} [PartialOrder α] [OrderTop α]
    (h a : α → Bool) (mono : Monotone h)
    (top : (!h ⊤ && a ⊤) = true) : ∀ x, (!h x && a x) = a x := by
  have ht : h ⊤ = false := by
    cases hh : h ⊤ <;> simp_all
  have hz (x : α) : h x = false := by
    have le := mono (show x ≤ ⊤ from le_top)
    cases hx : h x <;> simp_all
    exact (by decide : ¬ (true ≤ false)) le
  intro x
  simp [hz]

theorem or_not_bypass {α : Type} [PartialOrder α] [OrderBot α]
    (h a : α → Bool) (mono : Monotone h)
    (bot : (!h ⊥ || a ⊥) = false) : ∀ x, (!h x || a x) = a x := by
  have ht : h ⊥ = true := by
    cases hh : h ⊥ <;> simp_all
  have hz (x : α) : h x = true := by
    have le := mono (show ⊥ ≤ x from bot_le)
    cases hx : h x <;> simp_all
    exact (by decide : ¬ (true ≤ false)) le
  intro x
  simp [hz]

theorem and_not_fiber_bypass (h a : Bool → (Fin 9 → Bool) → Bool)
    (mono : ∀ b, Monotone (h b))
    (top : ∀ b, (!h b (fun _ => true) && a b (fun _ => true)) = true) :
    ∀ b x, (!h b x && a b x) = a b x := by
  intro b
  exact and_not_bypass (h b) (a b) (mono b) (top b)

theorem or_not_fiber_bypass (h a : Bool → (Fin 9 → Bool) → Bool)
    (mono : ∀ b, Monotone (h b))
    (bot : ∀ b, (!h b (fun _ => false) || a b (fun _ => false)) = false) :
    ∀ b x, (!h b x || a b x) = a b x := by
  intro b
  exact or_not_bypass (h b) (a b) (mono b) (bot b)

end PEqualNP.Outside.L_meta_1884.OneGateAfterNot
