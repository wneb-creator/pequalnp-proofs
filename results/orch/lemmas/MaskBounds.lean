import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.MaskBounds

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def masks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun w => ∀ x : Fin n → Bool,
    f x = true → x w = true → graphFun G ∅ x = true

def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Finset (Fin n) := Finset.univ.filter (G.Adj v)

lemma masks_pair_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) (p q : Fin n)
    (hpq : ¬ G.Adj p q) (hfire : f (pairInput p q) = true) :
    masks G f ⊆ nbrs G p ∪ nbrs G q := by
  intro c hc
  have hclean := (Finset.mem_filter.mp hc).2
  let x : Fin n → Bool := fun v => decide (v = p ∨ v = q ∨ v = c)
  have hle : pairInput p q ≤ x := by
    intro v
    apply Bool.le_iff_imp.mpr
    intro hv
    simp only [pairInput, decide_eq_true_eq] at hv
    simp only [x, decide_eq_true_eq]
    rcases hv with rfl | rfl <;> simp
  have hfx : f x = true := Bool.le_iff_imp.mp (hf hle) hfire
  have hgraph := hclean x hfx (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hgraph
  obtain ⟨u, v, huv, hu, hv⟩ := hgraph
  simp only [x, decide_eq_true_eq] at hu hv
  have hc' : G.Adj p c ∨ G.Adj q c := by
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact (hpq huv).elim
    · exact Or.inl huv
    · exact (hpq huv.symm).elim
    · exact (G.loopless.irrefl _ huv).elim
    · exact Or.inr huv
    · exact Or.inl huv.symm
    · exact Or.inr huv.symm
    · exact (G.loopless.irrefl _ huv).elim
  simpa [nbrs] using hc'

lemma masks_card_le_two_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) (p q : Fin n)
    (hpq : ¬ G.Adj p q) (hfire : f (pairInput p q) = true) :
    (masks G f).card ≤ (nbrs G p).card + (nbrs G q).card :=
  (Finset.card_le_card (masks_pair_subset G f hf p q hpq hfire)).trans
    (Finset.card_union_le _ _)

lemma masks_singleton_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) (z : Fin n)
    (hz : f (pairInput z z) = true) : masks G f ⊆ nbrs G z := by
  simpa only [Finset.union_self] using
    masks_pair_subset G f hf z z (G.loopless.irrefl z) hz

lemma masks_card_le_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) (z : Fin n)
    (hz : f (pairInput z z) = true) : (masks G f).card ≤ (nbrs G z).card :=
  Finset.card_le_card (masks_singleton_subset G f hf z hz)

lemma common_nbrs_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (a b : Fin n) (hab : a ≠ b) :
    (nbrs G a ∩ nbrs G b).card ≤ 1 := by
  have heq : nbrs G a ∩ nbrs G b = Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    ext w
    simp [nbrs]
  rw [heq]
  exact hG a b hab

lemma masks_two_singletons_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (z w : Fin n) (hzw : z ≠ w) (hz : f (pairInput z z) = true)
    (hw : f (pairInput w w) = true) : (masks G f).card ≤ 1 := by
  apply (Finset.card_le_card (Finset.subset_inter
    (masks_singleton_subset G f hf z hz) (masks_singleton_subset G f hf w hw))).trans
  exact common_nbrs_card G hG z w hzw

lemma masks_singleton_nonedge_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (z p q : Fin n) (hzp : z ≠ p) (hzq : z ≠ q)
    (hz : f (pairInput z z) = true) (hpq : ¬ G.Adj p q)
    (hpqf : f (pairInput p q) = true) : (masks G f).card ≤ 2 := by
  have hsub : masks G f ⊆ (nbrs G z ∩ nbrs G p) ∪ (nbrs G z ∩ nbrs G q) := by
    intro c hc
    have hz' := masks_singleton_subset G f hf z hz hc
    rcases Finset.mem_union.mp (masks_pair_subset G f hf p q hpq hpqf hc) with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz', hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz', hq⟩)
  have h1 := common_nbrs_card G hG z p hzp
  have h2 := common_nbrs_card G hG z q hzq
  have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma large_masks_pair_clean_away_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (z : Fin n) (hz : f (pairInput z z) = true) (hlarge : 3 ≤ (masks G f).card)
    (p q : Fin n) (hzp : z ≠ p) (hzq : z ≠ q) (hpqf : f (pairInput p q) = true) :
    G.Adj p q := by
  by_contra h
  have hbound := masks_singleton_nonedge_card G hG f hf z p q hzp hzq hz h hpqf
  omega

lemma wmax_eq_masks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) :
    wmax G C g = masks G (PEqualNP.EdgeOwnership.gateVal n C g) := rfl

end PEqualNP.Outside.L_meta_1477.MaskBounds
