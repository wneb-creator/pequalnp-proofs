import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.StarReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma star_below_product {n : ℕ} (P Q : Finset (Fin n)) (z : Fin n)
    (hz : z ∈ P) (x : Fin n → Bool)
    (hstar : (x z && decide (∃ q ∈ Q, x q = true)) = true) :
    (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)) = true := by
  rw [Bool.and_eq_true] at hstar ⊢
  exact ⟨decide_eq_true ⟨z, hz, hstar.1⟩, hstar.2⟩

lemma star_below_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Finset (Fin n)) (z : Fin n) (hQ : ∀ q ∈ Q, G.Adj z q)
    (x : Fin n → Bool)
    (hstar : (x z && decide (∃ q ∈ Q, x q = true)) = true) :
    graphFun G ∅ x = true := by
  rw [Bool.and_eq_true] at hstar
  obtain ⟨hzx, hQx⟩ := hstar
  obtain ⟨q, hq, hqx⟩ := of_decide_eq_true hQx
  have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true :=
    ⟨z, q, hQ q hq, hzx, hqx⟩
  simpa [graphFun] using he

lemma star_agrees_on_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (P Q : Finset (Fin n)) (z : Fin n) (hz : z ∈ P)
    (hcover : ∀ u v, G.Adj u v →
      ((decide (∃ p ∈ P, pairInput u v p = true) &&
        decide (∃ q ∈ Q, pairInput u v q = true)) = true) → u = z ∨ v = z)
    (u v : Fin n) (huv : G.Adj u v) :
    (pairInput u v z && decide (∃ q ∈ Q, pairInput u v q = true)) =
      (decide (∃ p ∈ P, pairInput u v p = true) &&
        decide (∃ q ∈ Q, pairInput u v q = true)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact star_below_product P Q z hz (pairInput u v)
  · intro hg
    have hc := hcover u v huv hg
    rw [Bool.and_eq_true] at hg ⊢
    refine ⟨?_, hg.2⟩
    rcases hc with rfl | rfl <;> simp [pairInput]

lemma clean_star_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (P Q : Finset (Fin n)) (z : Fin n)
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hz : z ∈ P) (hQ : ∀ q ∈ Q, G.Adj z q)
    (hcover : ∀ u v, G.Adj u v →
      gateVal n C g (pairInput u v) = true → u = z ∨ v = z) :
    (∀ x : Fin n → Bool,
      (x z && decide (∃ q ∈ Q, x q = true)) = true → gateVal n C g x = true) ∧
    (∀ x : Fin n → Bool,
      (x z && decide (∃ q ∈ Q, x q = true)) = true → graphFun G ∅ x = true) ∧
    (∀ u v, G.Adj u v →
      (pairInput u v z && decide (∃ q ∈ Q, pairInput u v q = true)) =
        gateVal n C g (pairInput u v)) := by
  refine ⟨?_, star_below_graph G Q z hQ, ?_⟩
  · intro x hx
    rw [hsem]
    exact star_below_product P Q z hz x hx
  · intro u v huv
    rw [hsem]
    apply star_agrees_on_edges G P Q z hz _ u v huv
    intro a b hab hg
    apply hcover a b hab
    simpa only [hsem] using hg

end PEqualNP.Outside.L_meta_5012.StarReplacement
