import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

def independentLines {p l : ℕ} (E : Finset (Fin p × Fin l))
    (z : Fin p → Bool) (b : Fin l) : Bool :=
  decide (∀ a, (a, b) ∈ E → z a = false)

lemma edge_certificate {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hpos : ∀ a b, (a, b) ∈ E →
      f (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)) = true)
    (hneg : ∀ z : Fin p → Bool, f (Fin.addCases z (independentLines E z)) = false) :
    ∀ x, f x = true ↔ ∃ a b, (a, b) ∈ E ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
  intro x
  constructor
  · intro hon
    by_contra hnone
    let z : Fin p → Bool := fun a => x (Fin.castAdd l a)
    have lift : ∀ i : Fin (p + l), x i = true →
        Fin.addCases z (independentLines E z) i = true := by
      intro i
      refine Fin.addCases (m := p) (n := l) (fun a ha => ?_) (fun b hb => ?_) i
      · simpa [z] using ha
      · simp only [Fin.addCases_right, independentLines, decide_eq_true_eq]
        intro a hab
        cases hz : z a with
        | false => rfl
        | true => exact False.elim (hnone ⟨a, b, hab, hz, hb⟩)
    have bad := hmono x (Fin.addCases z (independentLines E z)) lift hon
    rw [hneg z] at bad
    contradiction
  · rintro ⟨a, b, hab, ha, hb⟩
    apply hmono _ x _ (hpos a b hab)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb

lemma edge_one_line {p l : ℕ} (E : Finset (Fin p × Fin l))
    (b : Fin l) (z : Fin p → Bool) :
    (∃ a b', (a, b') ∈ E ∧
      Fin.addCases z (fun j => decide (j = b)) (Fin.castAdd l a) = true ∧
      Fin.addCases z (fun j => decide (j = b)) (Fin.natAdd p b') = true) ↔
    ∃ a, (a, b) ∈ E ∧ z a = true := by
  simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b', hab, ha, rfl⟩
    exact ⟨a, hab, ha⟩
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, b, hab, ha, rfl⟩

end PEqualNP.Outside.L_meta_4675
