import Mathlib
import PEqualNP.Defs

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
namespace PEqualNP.Outside.L_meta_1477.OverlapMaskGeometry
open StructuralMasks PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma overlap_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (a c : Fin n) (hac : a ≠ c)
    (ha : CleanMask G A B a) (hc : CleanMask G A B c) : (A ∩ B).card ≤ 1 := by
  apply (Finset.card_le_card (show A ∩ B ⊆ Finset.univ.filter (fun z => G.Adj a z ∧ G.Adj c z) from ?_)).trans
    (h4 a c hac)
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cleanMask_adj_overlap G A B a ha z hz,
    cleanMask_adj_overlap G A B c hc z hz⟩

lemma internal_unique_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B : Finset (Fin n)) (z a : Fin n) (hz : z ∈ A ∩ B)
    (ha : a ∈ A) (ham : CleanMask G A B a) (hB : 2 ≤ B.card)
    (c : Fin n) (hcm : CleanMask G A B c) (hc : c ∈ A ∪ B) : c=a := by
  by_cases hca : c ∈ A
  · by_contra hne
    have hs : B ⊆ Finset.univ.filter (fun z => G.Adj c z ∧ G.Adj a z) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (cleanMask_of_mem_left_iff G A B c hca).mp hcm v hv,
        (cleanMask_of_mem_left_iff G A B a ha).mp ham v hv⟩
    have hl := (Finset.card_le_card hs).trans (h4 c a hne)
    omega
  · have hcb := (Finset.mem_union.mp hc).resolve_left hca
    have hza := hbip a z (cleanMask_adj_overlap G A B a ham z hz)
    have hzc := hbip c z (cleanMask_adj_overlap G A B c hcm z hz)
    have hac := hbip a c ((cleanMask_of_mem_left_iff G A B a ha).mp ham c hcb)
    cases haC : color a <;> cases hcC : color c <;> cases hzC : color z <;> simp_all

lemma outside_pair_uses_overlap {n : ℕ} (A B : Finset (Fin n)) (z : Fin n)
    (hinter : A ∩ B = {z}) (u v c : Fin n) (hc : c=u ∨ c=v)
    (hout : c ∉ A ∪ B) (hfire : productValue A B (pairInput u v) = true) :
    pairInput u v z = true := by
  simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq] at hfire
  obtain ⟨a,ha,hav⟩ := hfire.1
  obtain ⟨b,hb,hbv⟩ := hfire.2
  simp only [pairInput,decide_eq_true_eq] at hav hbv ⊢
  have hca : a ≠ c := fun he => hout (Finset.mem_union_left _ (he ▸ ha))
  have hcb : b ≠ c := fun he => hout (Finset.mem_union_right _ (he ▸ hb))
  have hab : a=b := by
    rcases hc with rfl | rfl <;> rcases hav with rfl | rfl <;> rcases hbv with rfl | rfl <;> simp_all
  have haz : a=z := by
    have hm : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha,hab ▸ hb⟩
    simpa only [hinter,Finset.mem_singleton] using hm
  exact haz ▸ hav

lemma masked_pair_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B : Finset (Fin n)) (z a : Fin n) (hinter : A ∩ B = {z})
    (ha : a ∈ A) (ham : CleanMask G A B a) (hB : 2 ≤ B.card)
    (u v c : Fin n) (hcm : CleanMask G A B c) (hc : c=u ∨ c=v)
    (hfire : productValue A B (pairInput u v) = true) :
    a=u ∨ a=v ∨ z=u ∨ z=v := by
  by_cases hin : c ∈ A ∪ B
  · have he := internal_unique_left G h4 color hbip A B z a (by simp [hinter]) ha ham hB c hcm hin
    rcases hc with h | h
    · exact Or.inl (he ▸ h)
    · exact Or.inr (Or.inl (he ▸ h))
  · have hz := outside_pair_uses_overlap A B z hinter u v c hc hin hfire
    exact Or.inr (Or.inr (by simpa only [pairInput,decide_eq_true_eq] using hz))

end PEqualNP.Outside.L_meta_1477.OverlapMaskGeometry

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
namespace PEqualNP.Outside.L_meta_1477.OverlapMaskGeometry
open StructuralMasks PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma product_monotone {n : ℕ} (A B : Finset (Fin n)) : Monotone (productValue A B) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq] at hx ⊢
  obtain ⟨a,ha,hxa⟩ := hx.1
  obtain ⟨b,hb,hxb⟩ := hx.2
  exact ⟨⟨a,ha,Bool.le_iff_imp.mp (hxy a) hxa⟩,⟨b,hb,Bool.le_iff_imp.mp (hxy b) hxb⟩⟩

lemma clean_mem_masks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c) :
    c ∈ MaskBounds.masks G (productValue A B) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  intro x hp hx
  simpa only [PEqualNP.MetaComplexity.NestedCover.graphFun,Finset.notMem_empty,false_and,
    exists_false,decide_false,Bool.false_or,decide_eq_true_eq] using hc x hp hx

lemma three_masks_small_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (z : Fin n) (hz : z ∈ A ∩ B)
    (hlarge : 3 ≤ (MaskBounds.masks G (productValue A B)).card) :
    A.card ≤ 2 ∨ B.card ≤ 2 := by
  have hsingle : productValue A B (pairInput z z) = true := by
    simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq]
    exact ⟨⟨z,(Finset.mem_inter.mp hz).1,by simp [pairInput]⟩,
      ⟨z,(Finset.mem_inter.mp hz).2,by simp [pairInput]⟩⟩
  have hcross (u : Fin n) (hu : u ∈ A.erase z) (v : Fin n) (hv : v ∈ B.erase z) : G.Adj u v := by
    apply MaskBounds.large_masks_pair_clean_away_singleton G h4 (productValue A B)
      (product_monotone A B) z hsingle hlarge u v
      (Finset.mem_erase.mp hu).1.symm (Finset.mem_erase.mp hv).1.symm
    simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq]
    exact ⟨⟨u,(Finset.mem_erase.mp hu).2,by simp [pairInput]⟩,
      ⟨v,(Finset.mem_erase.mp hv).2,by simp [pairInput]⟩⟩
  by_contra hn
  push_neg at hn
  have heA := Finset.card_erase_add_one (Finset.mem_inter.mp hz).1
  have heB := Finset.card_erase_add_one (Finset.mem_inter.mp hz).2
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (show 1 < (A.erase z).card by omega)
  have hs : B.erase z ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcross u hu w hw,hcross v hv w hw⟩
  have hbound := (Finset.card_le_card hs).trans (h4 u v huv)
  omega

end PEqualNP.Outside.L_meta_1477.OverlapMaskGeometry
