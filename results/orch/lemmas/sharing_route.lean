import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_1772.Sharing

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) {a p d f : Fin n} (hap : a ≠ p)
    (had : G.Adj a d) (hpd : G.Adj p d) (haf : G.Adj a f) (hpf : G.Adj p f) :
    d = f := by
  exact (Finset.card_le_one.mp (hfour a p hap)) d
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hpd⟩) f
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haf, hpf⟩)

lemma dirty_triple_collapse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hfour : NoFourCycle G) {a d e f p : Fin n}
    (had : G.Adj a d) (hae : G.Adj a e) (haf : G.Adj a f) (hfp : G.Adj f p)
    (hclean : G.Adj d e ∨ G.Adj d p ∨ G.Adj e p) :
    p = a ∨ f = d ∨ f = e := by
  by_cases hpa : p = a
  · exact Or.inl hpa
  have hap : a ≠ p := Ne.symm hpa
  rcases hclean with hde | hdp | hep
  · exact (htri d a e had.symm hae hde.symm).elim
  · exact Or.inr (Or.inl
      (common_neighbor_unique G hfour hap had hdp.symm haf hfp.symm).symm)
  · exact Or.inr (Or.inr
      (common_neighbor_unique G hfour hap hae hep.symm haf hfp.symm).symm)

lemma support_three_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d e p : Fin n)
    (h : graphFun G ∅ (fun i => decide (i = d ∨ i = e ∨ i = p)) = true) :
    G.Adj d e ∨ G.Adj d p ∨ G.Adj e p := by
  simp [graphFun] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (G.loopless.irrefl _ huv).elim
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact (G.loopless.irrefl _ huv).elim
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact (G.loopless.irrefl _ huv).elim

lemma safe_mixed_reader_collapse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hfour : NoFourCycle G) {a d e f p : Fin n}
    (had : G.Adj a d) (hae : G.Adj a e) (haf : G.Adj a f) (hfp : G.Adj f p)
    (hsafe : ∀ x : Fin n → Bool,
      ((((x a || x d) && x e) || x f) && (x a || x p)) = true →
        graphFun G ∅ x = true) :
    p = a ∨ f = d ∨ f = e := by
  apply dirty_triple_collapse G htri hfour had hae haf hfp
  apply support_three_edge G d e p
  apply hsafe
  simp

end PEqualNP.Outside.L_meta_1772.Sharing
