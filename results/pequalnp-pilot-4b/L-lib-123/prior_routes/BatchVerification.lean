import Mathlib

namespace PriorRoutes

lemma finite_answer_batch {Index Value Challenge Response : Type}
    [Nonempty Challenge] (actual : Index → Value)
    (accept : (Index → Value) → Prop)
    (check : Index → Value → Challenge → Response → Prop)
    (complete : ∀ i u, ∃ w, check i (actual i) u w)
    (sound : ∀ i a, a ≠ actual i → ∃ u, ∀ w, ¬ check i a u w) :
    accept actual ↔
      ∀ challenges : Index → Value → Challenge,
        ∃ answers : Index → Value, ∃ responses : Index → Response,
          accept answers ∧ ∀ i, check i (answers i) (challenges i (answers i)) (responses i) := by
  classical
  constructor
  · intro ha challenges
    choose responses hresponses using fun i => complete i (challenges i (actual i))
    exact ⟨actual, responses, ha, hresponses⟩
  · intro h
    let challenges : Index → Value → Challenge := fun i a =>
      if ha : a = actual i then Classical.choice inferInstance
      else Classical.choose (sound i a ha)
    obtain ⟨answers, responses, haccept, hcheck⟩ := h challenges
    have heq : answers = actual := by
      funext i
      by_contra hi
      have hbad := Classical.choose_spec (sound i (answers i) hi)
      have hgood := hcheck i
      simp only [challenges, dif_neg hi] at hgood
      exact hbad (responses i) hgood
    simpa only [heq] using haccept

end PriorRoutes
