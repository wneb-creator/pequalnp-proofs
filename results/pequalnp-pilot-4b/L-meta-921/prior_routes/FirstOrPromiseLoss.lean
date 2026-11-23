import Mathlib

namespace PriorRoutes.Meta921

/-- Forcing the gate a OR b to true loses at most one level of sparse-input
soundness for a conjunction target. This alone does not retain the original
promise. -/
theorem first_or_force_true_sound {α : Type} [DecidableEq α]
    (a b : α) (hab : a ≠ b) (S : Finset α)
    (F : Finset α → Bool → Prop)
    (mono : ∀ z, Monotone (fun X => F X z))
    (sound : ∀ X, X.card ≤ 5 →
      F X (decide (a ∈ X ∨ b ∈ X)) → S ⊆ X) :
    ∀ X, X.card ≤ 4 → F X true → S ⊆ X := by
  intro X hX hF
  by_contra bad
  obtain ⟨s, hsS, hsX⟩ := Finset.not_subset.mp bad
  have extend (p : α) (hp : p = a ∨ p = b) (hsp : s ≠ p) : False := by
    have hcard : (insert p X).card ≤ 5 := by
      have := Finset.card_insert_le p X
      omega
    have hbit : decide (a ∈ insert p X ∨ b ∈ insert p X) = true := by
      rcases hp with rfl | rfl <;> simp
    have hF' : F (insert p X) true := mono true (Finset.subset_insert p X) hF
    have hs := sound (insert p X) hcard (hbit ▸ hF') hsS
    exact (Finset.mem_insert.mp hs).elim hsp hsX
  by_cases hsa : s = a
  · exact extend b (Or.inr rfl) (by simpa [hsa] using hab)
  · exact extend a (Or.inl rfl) hsa

def sharpTarget : Finset (Fin 7) := {0, 2, 3, 4}
def sharpExtra : Finset (Fin 7) := {2, 3, 4, 5, 6}
def sharpF (X : Finset (Fin 7)) (z : Bool) : Bool :=
  decide (sharpTarget ⊆ X) || (z && decide (sharpExtra ⊆ X))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharp_original_correct : ∀ X : Finset (Fin 7), X.card ≤ 5 →
    sharpF X (decide ((0 : Fin 7) ∈ X ∨ (1 : Fin 7) ∈ X)) =
    decide (sharpTarget ⊆ X) := by
  decide

theorem sharp_force_true_fails : sharpExtra.card = 5 ∧
    sharpF sharpExtra true = true ∧ ¬ sharpTarget ⊆ sharpExtra := by
  decide

end PriorRoutes.Meta921
