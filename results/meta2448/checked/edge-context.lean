import EdgePruning

namespace PEqualNP.Outside.L_meta_2448_aux.EdgeContext

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.EdgePruning

lemma graph_pair_true_adj (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := (graph_true_iff n G (pairInput u v)).mp h
  have ha' : a = u ∨ a = v := of_decide_eq_true ha
  have hb' : b = u ∨ b = v := of_decide_eq_true hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact (hab.ne rfl).elim
  · exact hab
  · exact hab.symm
  · exact (hab.ne rfl).elim

theorem context_rejects_singletons (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (f k : (Fin n → Bool) → Bool)
    (fm : ∀ x y, (∀ z, x z = true → y z = true) → f x = true → f y = true)
    (km : ∀ x y, (∀ z, x z = true → y z = true) → k x = true → k y = true)
    (sound : ∀ x, f x = true → k x = true → graphFun G ∅ x = true)
    (u v : Fin n) (huv : G.Adj u v)
    (hu : f (pairInput u u) = true) (hv : f (pairInput v v) = true) :
    ∀ w : Fin n, k (pairInput w w) = false := by
  intro w
  cases hc : k (pairInput w w) with
  | false => rfl
  | true =>
    have adjacent (a : Fin n) (ha : f (pairInput a a) = true) : G.Adj a w := by
      have hfa : f (pairInput a w) = true := fm _ _
        (pair_below n (pairInput a w) a a (by simp [pairInput]) (by simp [pairInput])) ha
      have hkw : k (pairInput a w) = true := km _ _
        (pair_below n (pairInput a w) w w (by simp [pairInput]) (by simp [pairInput])) hc
      exact graph_pair_true_adj n G a w (sound _ hfa hkw)
    exact (htri u v w huv (adjacent v hv) (adjacent u hu).symm).elim

end PEqualNP.Outside.L_meta_2448_aux.EdgeContext
