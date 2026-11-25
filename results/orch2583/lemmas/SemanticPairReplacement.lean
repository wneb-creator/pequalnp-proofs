import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.SemanticPair

open PEqualNP.EdgeOwnership

lemma or_true {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

lemma replace_block_from_pairs (n : Nat) (E : Fin n → Fin n → Prop)
    (F H R D : (Fin n → Bool) → Bool)
    (target : ∀ x, F x = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true)
    (split : ∀ x, (H x || R x) = F x)
    (restMono : ∀ x y, (∀ i, x i = true → y i = true) → R x = true → R y = true)
    (newMono : ∀ x y, (∀ i, x i = true → y i = true) → D x = true → D y = true)
    (newBelow : ∀ x, D x = true → F x = true)
    (pairSame : ∀ u v, E u v → D (pairInput u v) = H (pairInput u v)) :
    ∀ x, (D x || R x) = F x := by
  intro x
  have equivalent : (D x || R x) = true ↔ F x = true := by
    constructor
    · intro h
      rcases or_true.mp h with hd | hr
      · exact newBelow x hd
      · rw [← split x]
        exact or_true.mpr (Or.inr hr)
    · intro h
      obtain ⟨u, v, huv, hu, hv⟩ := (target x).mp h
      have pairLe : ∀ i, pairInput u v i = true → x i = true := by
        intro i hi
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · simpa [hi] using hu
        · simpa [hi] using hv
      have pairTarget : F (pairInput u v) = true := by
        apply (target _).mpr
        exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
      have pairOld : (H (pairInput u v) || R (pairInput u v)) = true := by
        rw [split]
        exact pairTarget
      rcases or_true.mp pairOld with hh | hr
      · apply or_true.mpr
        left
        apply newMono _ x pairLe
        rw [pairSame u v huv]
        exact hh
      · exact or_true.mpr (Or.inr (restMono _ x pairLe hr))
  cases hleft : D x || R x <;> cases hright : F x <;> simp_all

end PEqualNP.Outside.L_meta_2583.SemanticPair
