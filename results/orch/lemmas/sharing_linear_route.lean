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

def linearOr {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ T, x p = true)

lemma support_pair_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f p : Fin n)
    (h : graphFun G ∅ (fun i => decide (i = f ∨ i = p)) = true) : G.Adj f p := by
  have h' : graphFun G ∅ (fun i => decide (i = f ∨ i = p ∨ i = p)) = true := by
    simpa only [or_self] using h
  rcases support_three_edge G f p p h' with hfp | hfp | hpp
  · exact hfp
  · exact hfp
  · exact (G.irrefl hpp).elim

lemma safe_mixed_linear_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a d e f : Fin n) (T : Finset (Fin n))
    (hsafe : ∀ x : Fin n → Bool,
      ((((x a || x d) && x e) || x f) && linearOr T x) = true → graphFun G ∅ x = true)
    (p : Fin n) (hp : p ∈ T) : G.Adj f p := by
  apply support_pair_edge G f p
  apply hsafe
  rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
  constructor
  · simp
  · simp only [linearOr, decide_eq_true_eq]
    exact ⟨p, hp, by simp⟩

lemma safe_mixed_linear_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hfour : NoFourCycle G) {a d e f : Fin n} {T : Finset (Fin n)}
    (had : G.Adj a d) (hae : G.Adj a e) (hfd : f ≠ d) (hfe : f ≠ e) (ha : a ∈ T)
    (hsafe : ∀ x : Fin n → Bool,
      ((((x a || x d) && x e) || x f) && linearOr T x) = true → graphFun G ∅ x = true) :
    T = {a} := by
  ext p
  simp only [Finset.mem_singleton]
  constructor
  · intro hp
    have haf := (safe_mixed_linear_edge G a d e f T hsafe a ha).symm
    have hfp := safe_mixed_linear_edge G a d e f T hsafe p hp
    have hc : p = a ∨ f = d ∨ f = e := by
      apply safe_mixed_reader_collapse G htri hfour had hae haf hfp
      intro x hx
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hx
      obtain ⟨hxleft, hxright⟩ := hx
      apply hsafe x
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
      refine ⟨hxleft, ?_⟩
      simp only [linearOr, decide_eq_true_eq]
      rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hxright
      rcases hxright with hxa | hxp
      · exact ⟨a, ha, hxa⟩
      · exact ⟨p, hp, hxp⟩
    rcases hc with hpa | hfd' | hfe'
    · exact hpa
    · exact (hfd hfd').elim
    · exact (hfe hfe').elim
  · intro hpa
    simpa only [hpa] using ha

lemma collapsed_reader_identity (a d e f : Bool) :
    ((((a || d) && e) || f) && a) = (a && (e || f)) := by
  cases a <;> cases d <;> cases e <;> cases f <;> rfl

lemma safe_mixed_linear_rewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hfour : NoFourCycle G) {a d e f : Fin n} {T : Finset (Fin n)}
    (had : G.Adj a d) (hae : G.Adj a e) (hfd : f ≠ d) (hfe : f ≠ e) (ha : a ∈ T)
    (hsafe : ∀ x : Fin n → Bool,
      ((((x a || x d) && x e) || x f) && linearOr T x) = true → graphFun G ∅ x = true) :
    ∀ x : Fin n → Bool,
      ((((x a || x d) && x e) || x f) && linearOr T x) = (x a && (x e || x f)) := by
  have hT := safe_mixed_linear_singleton G htri hfour had hae hfd hfe ha hsafe
  intro x
  rw [hT]
  simpa [linearOr] using collapsed_reader_identity (x a) (x d) (x e) (x f)

end PEqualNP.Outside.L_meta_1772.Sharing
