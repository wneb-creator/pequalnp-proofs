import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Restriction

lemma below_linear_or_of_zero (n : ℕ) (S : Finset (Fin n))
    (A : (Fin n → Bool) → Bool) (hA : Monotone A)
    (hz : A (fun i => decide (i ∉ S)) = false) :
    ∀ x : Fin n → Bool, A x = true → ∃ i ∈ S, x i = true := by
  intro x hx
  by_contra hn
  have hxz : x ≤ (fun i => decide (i ∉ S)) := by
    intro i
    by_cases hi : i ∈ S
    · have hxi : x i = false := by
        cases he : x i
        · rfl
        · exact False.elim (hn ⟨i, hi, he⟩)
      simp [hi, hxi]
    · simp [hi]
  have hle := hA hxz
  rw [hx, hz] at hle
  exact (by decide : ¬ ((true : Bool) ≤ false)) hle

lemma linear_or_meet_irreducible (n : ℕ) (S : Finset (Fin n))
    (A B : (Fin n → Bool) → Bool) (hA : Monotone A) (hB : Monotone B)
    (h : ∀ x, (A x && B x) = decide (∃ i ∈ S, x i = true)) :
    (∀ x, A x = decide (∃ i ∈ S, x i = true)) ∨
    (∀ x, B x = decide (∃ i ∈ S, x i = true)) := by
  let z : Fin n → Bool := fun i => decide (i ∉ S)
  have hF : decide (∃ i ∈ S, z i = true) = false := by simp [z]
  have hab : (A z && B z) = false := (h z).trans hF
  have hzero : A z = false ∨ B z = false := by
    cases ha : A z <;> cases hb : B z <;> simp_all
  have hfromA (hz : A z = false) : ∀ x, A x = decide (∃ i ∈ S, x i = true) := by
    intro x
    cases hAx : A x
    · simpa [hAx] using h x
    · have hex := below_linear_or_of_zero n S A hA hz x hAx
      simp [hex]
  have hfromB (hz : B z = false) : ∀ x, B x = decide (∃ i ∈ S, x i = true) := by
    intro x
    cases hBx : B x
    · simpa [hBx] using h x
    · have hex := below_linear_or_of_zero n S B hB hz x hBx
      simp [hex]
  exact hzero.imp hfromA hfromB

end PEqualNP.Outside.L_meta_2583_aux.Restriction
