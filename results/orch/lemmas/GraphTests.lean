import Mathlib.Data.Finset.Powerset

namespace PEqualNP.Outside.L_meta_2585

lemma graph_test_criterion {α : Type*} [Fintype α] [DecidableEq α]
    (E : α → α → Prop) [DecidableRel E] (f : (α → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (accepts : ∀ u v, E u v → f (fun i => decide (i = u ∨ i = v)) = true)
    (rejects : ∀ S : Finset α, (∀ u ∈ S, ∀ v ∈ S, ¬ E u v) →
      f (fun i => decide (i ∈ S)) = false) :
    ∀ x, f x = decide (∃ u v, E u v ∧ x u = true ∧ x v = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    by_contra h
    let S : Finset α := Finset.univ.filter fun i => x i = true
    have independent : ∀ u ∈ S, ∀ v ∈ S, ¬ E u v := by
      intro u hu v hv huv
      exact h ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
    have input : (fun i => decide (i ∈ S)) = x := by
      funext i
      simp [S]
    have hf := rejects S independent
    rw [input, hx] at hf
    cases hf
  · rintro ⟨u, v, huv, hu, hv⟩
    apply mono (fun i => decide (i = u ∨ i = v)) x ?_ (accepts u v huv)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

end PEqualNP.Outside.L_meta_2585
