import Mathlib

namespace PriorRoutes.Meta971

/-- A smaller monotone replacement that agrees on every minimal positive
input preserves an exact monotone target, even inside an arbitrary monotone
downstream context. -/
theorem replacement_from_minimal_positives {α : Type} [DecidableEq α]
    (E : Finset (Finset α)) (H : Finset α → Prop → Prop)
    (g replacement : Finset α → Prop)
    (monoX : ∀ z, Monotone (fun X => H X z))
    (monoZ : ∀ X, Monotone (H X))
    (monoR : Monotone replacement)
    (smaller : ∀ X, replacement X → g X)
    (onE : ∀ e ∈ E, replacement e ↔ g e)
    (correct : ∀ X, H X (g X) ↔ ∃ e ∈ E, e ⊆ X) :
    ∀ X, H X (replacement X) ↔ ∃ e ∈ E, e ⊆ X := by
  intro X
  constructor
  · intro h
    exact (correct X).mp (monoZ X (smaller X) h)
  · rintro ⟨e, he, heX⟩
    have h : H e (g e) := (correct e).mpr ⟨e, he, Finset.Subset.refl _⟩
    rw [← propext (onE e he)] at h
    exact monoZ X (monoR heX) (monoX (replacement e) heX h)

/-- A monomial that vanishes on every edge-minimal positive input can be
removed from the first OR. The other operand is a free conjunction. -/
theorem trim_first_or {α : Type} [DecidableEq α]
    (E : Finset (Finset α)) (A B : Finset α)
    (H : Finset α → Prop → Prop)
    (monoX : ∀ z, Monotone (fun X => H X z))
    (monoZ : ∀ X, Monotone (H X))
    (dead : ∀ e ∈ E, ¬ A ⊆ e)
    (correct : ∀ X, H X (A ⊆ X ∨ B ⊆ X) ↔ ∃ e ∈ E, e ⊆ X) :
    ∀ X, H X (B ⊆ X) ↔ ∃ e ∈ E, e ⊆ X := by
  apply replacement_from_minimal_positives E H
    (fun X => A ⊆ X ∨ B ⊆ X) (fun X => B ⊆ X)
    monoX monoZ
  · intro X Y hXY hBX
    exact hBX.trans hXY
  · intro X h
    exact Or.inr h
  · intro e he
    simp [dead e he]
  · exact correct

end PriorRoutes.Meta971
