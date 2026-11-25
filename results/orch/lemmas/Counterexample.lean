import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2602_aux

lemma monotone_boundary_certificate {n : Nat} (S : Finset (Fin n))
    (f : (Fin n → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (positive : ∀ i ∈ S, f (fun j => decide (j = i)) = true)
    (negative : f (fun j => decide (j ∉ S)) = false) :
    ∀ x, f x = true ↔ ∃ i ∈ S, x i = true := by
  intro x
  constructor
  · intro hx
    by_contra h
    have hle : ∀ i, x i = true → decide (i ∉ S) = true := by
      intro i hi
      apply decide_eq_true
      intro hmem
      exact h ⟨i, hmem, hi⟩
    have ht := mono x (fun j => decide (j ∉ S)) hle hx
    rw [negative] at ht
    contradiction
  · rintro ⟨i, hi, hxi⟩
    apply mono (fun j => decide (j = i)) x
    · intro j hj
      have heq : j = i := of_decide_eq_true hj
      simpa [heq] using hxi
    · exact positive i hi

lemma distributed_factor_identity (a b c : Bool) :
    a || (b && c) = ((a || b) && (a || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma path_double_reread_identity (x y z w : Bool) :
    ((z || (x && (x && y))) && (y || w)) =
      ((x && y) || (y && z) || (z && w)) := by
  cases x <;> cases y <;> cases z <;> cases w <;> rfl

end PEqualNP.Outside.L_meta_2602_aux
