import Mathlib

namespace PEqualNP.Outside.L_meta_951

theorem finite_equiv_reflects_relation {α : Type*} [Finite α]
    (e : α ≃ α) (r : α → α → Prop)
    (hr : ∀ a b, r a b → r (e a) (e b))
    (a b : α) (hab : r (e a) (e b)) : r a b := by
  let R : Set (α × α) := {p | r p.1 p.2}
  let f : α × α → α × α := fun p => (e p.1, e p.2)
  have hi : Function.Injective f := by
    intro p q hpq
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst hpq)
    · exact e.injective (congrArg Prod.snd hpq)
  have hm : Set.MapsTo f R R := fun p hp => hr _ _ hp
  have hb : Set.BijOn f R R :=
    ((Set.toFinite R).injOn_iff_bijOn_of_mapsTo hm).mp
      (fun p _ q _ hpq => hi hpq)
  obtain ⟨p, hp, hpe⟩ := hb.surjOn (show (e a, e b) ∈ R from hab)
  have hp₁ : p.1 = a := e.injective (congrArg Prod.fst hpe)
  have hp₂ : p.2 = b := e.injective (congrArg Prod.snd hpe)
  change r p.1 p.2 at hp
  simpa only [hp₁, hp₂] using hp

theorem finite_monotone_equiv_symm {α : Type*} [Finite α] [Preorder α]
    (e : α ≃ α) (he : Monotone e) : Monotone e.symm := by
  intro a b hab
  apply finite_equiv_reflects_relation e (· ≤ ·) (fun _ _ h => he h)
  simpa using hab

end PEqualNP.Outside.L_meta_951
