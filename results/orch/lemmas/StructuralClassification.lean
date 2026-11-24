import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.Structural

def cleanCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Finset (Fin n) :=
  (A.filter fun a => ∀ b ∈ B, G.Adj a b) ∪
    (B.filter fun b => ∀ a ∈ A, G.Adj a b)

lemma commonNeighbors_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hB : 2 ≤ B.card) :
    (A.filter fun a => ∀ b ∈ B, G.Adj a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha c hc
  by_contra hac
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hsub : ({b, d} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ha).2 w hb, (Finset.mem_filter.mp hc).2 w hb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ha).2 w hd, (Finset.mem_filter.mp hc).2 w hd⟩
  have hcard := Finset.card_le_card hsub
  have hpair : ({b, d} : Finset (Fin n)).card = 2 := by simp [hbd]
  have hsmall := h4 a c hac
  omega

lemma cleanCenters_card_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    (cleanCenters G A B).card ≤ 2 := by
  have hleft := commonNeighbors_card_le_one G h4 A B hB
  have hright := commonNeighbors_card_le_one G h4 B A hA
  have heq : (B.filter fun b => ∀ a ∈ A, G.Adj a b) =
      B.filter fun b => ∀ a ∈ A, G.Adj b a := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun a ha => (h a ha).symm⟩
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun a ha => (h a ha).symm⟩
  unfold cleanCenters
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma opposite_centers_no_shared_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : G.Adj a b) :
    ¬ ∃ v, G.Adj a v ∧ G.Adj b v := by
  rintro ⟨v, hav, hbv⟩
  have h1 := hbip a b hab
  have h2 := hbip a v hav
  have h3 := hbip b v hbv
  cases ha : side a <;> cases hb : side b <;> cases hv : side v <;> simp_all

lemma common_mask_inputs_empty {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : G.Adj a b) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, G.Adj a v ∧ G.Adj b v) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact opposite_centers_no_shared_neighbors G side hbip a b hab ⟨v, hS v hv⟩

end PEqualNP.Outside.L_meta_1477.Structural

namespace PEqualNP.Outside.L_meta_1477.StructuralMasks

def orValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def productValue {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orValue A x && orValue B x

def CleanMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∀ x : Fin n → Bool, productValue A B x = true → x c = true →
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def EffectiveMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧
    productValue A B (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
    PEqualNP.EdgeOwnership.pairInput u v c = true

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (c d : Fin n) :
    (∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.pairInput c d u = true ∧
      PEqualNP.EdgeOwnership.pairInput c d v = true) ↔ G.Adj c d := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact huv
    · exact huv.symm
    · exact (G.loopless.irrefl _ huv).elim
  · intro h
    exact ⟨c, d, h, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma cleanMask_of_mem_left_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A) :
    CleanMask G A B c ↔ ∀ b ∈ B, G.Adj c b := by
  constructor
  · intro h b hb
    apply (graph_pair_iff G c b).mp
    apply h (PEqualNP.EdgeOwnership.pairInput c b)
    · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
        ⟨b, hb, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
    · simp [PEqualNP.EdgeOwnership.pairInput]
  · intro h x hx hxc
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hx
    obtain ⟨b, hb, hxb⟩ := hx.2
    exact ⟨c, b, h b hb, hxc, hxb⟩

lemma cleanMask_of_mem_right_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ B) :
    CleanMask G A B c ↔ ∀ a ∈ A, G.Adj a c := by
  have hs : CleanMask G A B c ↔ CleanMask G B A c := by
    simp only [CleanMask, productValue, Bool.and_comm]
  rw [hs, cleanMask_of_mem_left_iff G B A c hc]
  exact forall₂_congr fun a _ => G.adj_comm c a

lemma cleanMask_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c)
    (z : Fin n) (hz : z ∈ A ∩ B) : G.Adj c z := by
  apply (graph_pair_iff G c z).mp
  apply hc (PEqualNP.EdgeOwnership.pairInput c z)
  · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
  · simp [PEqualNP.EdgeOwnership.pairInput]

lemma effectiveMask_mem_union {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (c : Fin n)
    (hc : EffectiveMask G A B c) : c ∈ A ∪ B := by
  obtain ⟨u, v, _, hprod, hmask⟩ := hc
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  obtain ⟨a, ha, hpa⟩ := hprod.1
  obtain ⟨b, hb, hpb⟩ := hprod.2
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hpa hpb hmask
  by_contra hnot
  have hca : c ∉ A := fun h => hnot (Finset.mem_union_left _ h)
  have hcb : c ∉ B := fun h => hnot (Finset.mem_union_right _ h)
  have hab : a ≠ b := fun h => (Finset.disjoint_left.mp hdis ha) (h ▸ hb)
  rcases hmask with rfl | rfl <;>
    rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> contradiction

end PEqualNP.Outside.L_meta_1477.StructuralMasks

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
namespace PEqualNP.Outside.L_meta_1477.StructuralClassification

open PEqualNP.TopForm PEqualNP.EdgeOwnership
open Structural StructuralMasks MaskBounds

lemma productValue_monotone {n : ℕ} (A B : Finset (Fin n)) :
    Monotone (productValue A B) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx.1
  obtain ⟨b, hb, hxb⟩ := hx.2
  exact ⟨⟨a, ha, Bool.le_iff_imp.mp (hxy a) hxa⟩,
    ⟨b, hb, Bool.le_iff_imp.mp (hxy b) hxb⟩⟩

lemma cleanMask_mem_masks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c) :
    c ∈ masks G (productValue A B) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro x hx hxc
  have h := hc x hx hxc
  simpa only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] using h

lemma three_effective_masks_product_shape {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (A B W : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hW : 3 ≤ W.card)
    (hclean : ∀ c ∈ W, CleanMask G A B c)
    (heffective : ∀ c ∈ W, EffectiveMask G A B c) :
    ∃ z : Fin n, A ∩ B = {z} ∧ (A.card ≤ 2 ∨ B.card ≤ 2) := by
  have hIle : (A ∩ B).card ≤ 1 := by
    by_contra h
    have hsub : W ⊆ Finset.univ.filter (fun c => ∀ z ∈ A ∩ B, G.Adj c z) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun z hz => cleanMask_adj_overlap G A B c (hclean c hc) z hz⟩
    have hsmall := commonNeighbors_card_le_one G h4 Finset.univ (A ∩ B) (by omega)
    have hcard := Finset.card_le_card hsub
    omega
  have hIne : (A ∩ B).Nonempty := by
    by_contra h
    have hi : A ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hd : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hi
    have hsub : W ⊆ cleanCenters G A B := by
      intro c hc
      rcases Finset.mem_union.mp (effectiveMask_mem_union G A B hd c (heffective c hc)) with ha | hb
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨ha, (cleanMask_of_mem_left_iff G A B c ha).mp (hclean c hc)⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hb, (cleanMask_of_mem_right_iff G A B c hb).mp (hclean c hc)⟩)
    have hsmall := cleanCenters_card_le_two G h4 A B hA hB
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (by
    have hp := Finset.card_pos.mpr hIne
    omega : (A ∩ B).card = 1)
  have hzi : z ∈ A ∩ B := by rw [hz]; simp
  obtain ⟨hza, hzb⟩ := Finset.mem_inter.mp hzi
  have hprodmono := productValue_monotone A B
  have hWsub : W ⊆ masks G (productValue A B) :=
    fun c hc => cleanMask_mem_masks G A B c (hclean c hc)
  have hlarge : 3 ≤ (masks G (productValue A B)).card :=
    hW.trans (Finset.card_le_card hWsub)
  have hzfire : productValue A B (pairInput z z) = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨z, hza, by simp [pairInput]⟩, ⟨z, hzb, by simp [pairInput]⟩⟩
  have hcross : ∀ a ∈ A.erase z, ∀ b ∈ B.erase z, G.Adj a b := by
    intro a ha b hb
    obtain ⟨haz, ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨hbz, hb⟩ := Finset.mem_erase.mp hb
    apply large_masks_pair_clean_away_singleton G h4 (productValue A B) hprodmono z
      hzfire hlarge a b (Ne.symm haz) (Ne.symm hbz)
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨a, ha, by simp [pairInput]⟩, ⟨b, hb, by simp [pairInput]⟩⟩
  have hside : (A.erase z).card ≤ 1 ∨ (B.erase z).card ≤ 1 := by
    by_cases hb : (B.erase z).card ≤ 1
    · exact Or.inr hb
    apply Or.inl
    have heq : ((A.erase z).filter fun a => ∀ b ∈ B.erase z, G.Adj a b) = A.erase z :=
      Finset.filter_eq_self.mpr hcross
    have hc := commonNeighbors_card_le_one G h4 (A.erase z) (B.erase z) (by omega)
    simpa only [heq] using hc
  refine ⟨z, hz, ?_⟩
  have hca := Finset.card_erase_add_one hza
  have hcb := Finset.card_erase_add_one hzb
  omega

end PEqualNP.Outside.L_meta_1477.StructuralClassification
