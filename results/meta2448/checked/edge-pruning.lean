import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.EdgePruning

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graph_true_iff (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_below (n : ℕ) (x : Fin n → Bool) (u v : Fin n)
    (hu : x u = true) (hv : x v = true) :
    ∀ w, pairInput u v w = true → x w = true := by
  intro w hw
  have he : w = u ∨ w = v := of_decide_eq_true hw
  rcases he with rfl | rfl
  · exact hu
  · exact hv

theorem exact_of_decreasing_and_edge_preserving (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f h : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) → h x = true → h y = true)
    (hcorrect : f = graphFun G ∅)
    (hdecrease : ∀ x, h x = true → f x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → h (pairInput u v) = f (pairInput u v)) :
    h = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hcorrect]
    exact hdecrease x hx
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := (graph_true_iff n G x).mp hx
    have hp : h (pairInput u v) = true := by
      rw [hedges u v huv, hcorrect]
      apply (graph_true_iff n G (pairInput u v)).mpr
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    exact hmono (pairInput u v) x (pair_below n x u v hu hv) hp

end PEqualNP.Outside.L_meta_2448_aux.EdgePruning
