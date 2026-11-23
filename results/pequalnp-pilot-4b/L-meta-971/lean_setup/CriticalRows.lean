import PEqualNP.Defs

namespace EdgeCriticalAudit

theorem critical_rows_complete {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (negatives : Finset (Finset α))
    (F : Finset α → Prop) (hmono : Monotone F)
    (hcover : ∀ A : Finset α,
      (¬ ∃ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A) → ∃ I ∈ negatives, A ⊆ I)
    (hpositive : ∀ e ∈ E, F {e.1, e.2})
    (hnegative : ∀ I ∈ negatives, ¬ F I) :
    ∀ A : Finset α, F A ↔ ∃ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A := by
  intro A
  constructor
  · intro hFA
    by_contra hn
    obtain ⟨I, hI, hAI⟩ := hcover A hn
    exact hnegative I hI (hmono hAI hFA)
  · rintro ⟨e, he, hu, hv⟩
    apply hmono (show ({e.1, e.2} : Finset α) ⊆ A from ?_) (hpositive e he)
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv

end EdgeCriticalAudit
