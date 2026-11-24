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

namespace PEqualNP.Outside.L_meta_1477.MaskGrouping

open Structural StructuralMasks PEqualNP.EdgeOwnership

noncomputable def neighbors {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) : Finset (Fin n) :=
  if c ∈ A then B else A

noncomputable def starEdges {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) : Finset (Sym2 (Fin n)) :=
  (neighbors A B c).image fun v => s(c, v)

lemma mem_centers_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) :
    c ∈ cleanCenters G A B ↔ c ∈ A ∪ B ∧ CleanMask G A B c := by
  simp only [cleanCenters, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hc, h⟩ | ⟨hc, h⟩)
    · exact ⟨Or.inl hc, (cleanMask_of_mem_left_iff G A B c hc).mpr h⟩
    · exact ⟨Or.inr hc, (cleanMask_of_mem_right_iff G A B c hc).mpr h⟩
  · rintro ⟨hc | hc, h⟩
    · exact Or.inl ⟨hc, (cleanMask_of_mem_left_iff G A B c hc).mp h⟩
    · exact Or.inr ⟨hc, (cleanMask_of_mem_right_iff G A B c hc).mp h⟩

lemma center_neighbors_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    ∀ v ∈ neighbors A B c, G.Adj c v := by
  have hd := (mem_centers_iff G A B c).mp hc
  by_cases hca : c ∈ A
  · simpa only [neighbors, if_pos hca] using
      (cleanMask_of_mem_left_iff G A B c hca).mp hd.2
  · have hcb : c ∈ B := (Finset.mem_union.mp hd.1).resolve_left hca
    intro v hv
    have hva : v ∈ A := by simpa only [neighbors, if_neg hca] using hv
    exact ((cleanMask_of_mem_right_iff G A B c hcb).mp hd.2 v hva).symm

lemma neighbors_nonempty {n : ℕ} (A B : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (c : Fin n) :
    (neighbors A B c).Nonempty := by
  unfold neighbors
  split <;> assumption

lemma center_effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (c : Fin n) (hc : c ∈ cleanCenters G A B) : EffectiveMask G A B c := by
  have hcm := (mem_centers_iff G A B c).mp hc
  obtain ⟨v, hv⟩ := neighbors_nonempty A B hA hB c
  refine ⟨c, v, center_neighbors_clean G A B c hc v hv, ?_, by simp [pairInput]⟩
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
  by_cases hca : c ∈ A
  · have hvb : v ∈ B := by simpa only [neighbors, if_pos hca] using hv
    exact ⟨⟨c, hca, by simp [pairInput]⟩, ⟨v, hvb, by simp [pairInput]⟩⟩
  · have hcb : c ∈ B := (Finset.mem_union.mp hcm.1).resolve_left hca
    have hva : v ∈ A := by simpa only [neighbors, if_neg hca] using hv
    exact ⟨⟨v, hva, by simp [pairInput]⟩, ⟨c, hcb, by simp [pairInput]⟩⟩

lemma centers_exact_effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (c : Fin n) :
    c ∈ cleanCenters G A B ↔ CleanMask G A B c ∧ EffectiveMask G A B c := by
  constructor
  · intro hc
    exact ⟨((mem_centers_iff G A B c).mp hc).2, center_effective G A B hA hB c hc⟩
  · rintro ⟨hc, he⟩
    exact (mem_centers_iff G A B c).mpr ⟨effectiveMask_mem_union G A B hdis c he, hc⟩

lemma same_side_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ A) (hd : d ∈ A) (hcm : CleanMask G A B c) (hdm : CleanMask G A B d) :
    c = d := by
  have hh := commonNeighbors_card_le_one G hG A B hB
  rw [Finset.card_le_one] at hh
  exact hh c (Finset.mem_filter.mpr ⟨hc, (cleanMask_of_mem_left_iff G A B c hc).mp hcm⟩)
    d (Finset.mem_filter.mpr ⟨hd, (cleanMask_of_mem_left_iff G A B d hd).mp hdm⟩)

lemma different_centers_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) (hne : c ≠ d) :
    (c ∈ A ∧ d ∈ B) ∨ (c ∈ B ∧ d ∈ A) := by
  obtain ⟨hcAB, hcm⟩ := (mem_centers_iff G A B c).mp hc
  obtain ⟨hdAB, hdm⟩ := (mem_centers_iff G A B d).mp hd
  rcases Finset.mem_union.mp hcAB with hcA | hcB <;>
    rcases Finset.mem_union.mp hdAB with hdA | hdB
  · exact (hne (same_side_equal G hG A B hB c d hcA hdA hcm hdm)).elim
  · exact Or.inl ⟨hcA, hdB⟩
  · exact Or.inr ⟨hcB, hdA⟩
  · apply (hne (same_side_equal G hG B A hA c d hcB hdB ?_ ?_)).elim
    · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
    · simpa only [CleanMask, productValue, Bool.and_comm] using hdm

lemma centers_shared_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hdis : Disjoint A B) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) (hne : c ≠ d) :
    s(c, d) ∈ starEdges A B c ∩ starEdges A B d := by
  have finish (hcd : d ∈ neighbors A B c) (hdc : c ∈ neighbors A B d) :
      s(c, d) ∈ starEdges A B c ∩ starEdges A B d := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_image.mpr ⟨d, hcd, rfl⟩,
      Finset.mem_image.mpr ⟨c, hdc, Sym2.eq_swap⟩⟩
  rcases different_centers_cross G hG A B hA hB c d hc hd hne with ⟨hcA, hdB⟩ | ⟨hcB, hdA⟩
  · have hdA : d ∉ A := fun h => Finset.disjoint_left.mp hdis h hdB
    exact finish (by simpa only [neighbors, if_pos hcA] using hdB)
      (by simpa only [neighbors, if_neg hdA] using hcA)
  · have hcA : c ∉ A := fun h => Finset.disjoint_left.mp hdis h hcB
    exact finish (by simpa only [neighbors, if_neg hcA] using hdA)
      (by simpa only [neighbors, if_pos hdA] using hcB)

lemma centers_stars_intersect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hdis : Disjoint A B) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) :
    (starEdges A B c ∩ starEdges A B d).Nonempty := by
  by_cases hcd : c = d
  · subst d
    obtain ⟨v, hv⟩ := neighbors_nonempty A B (Finset.card_pos.mp (by omega))
      (Finset.card_pos.mp (by omega)) c
    exact ⟨s(c, v), Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩⟩
  · exact ⟨s(c, d), centers_shared_edge G hG A B hdis hA hB c d hc hd hcd⟩

end PEqualNP.Outside.L_meta_1477.MaskGrouping

namespace PEqualNP.Outside.L_meta_1477.SharedMaskCollision

open PEqualNP.TopForm Structural StructuralMasks MaskGrouping

lemma common_neighbor_bad_column {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B : Finset (Fin n)) (c d q b₀ : Fin n)
    (hb₀ : b₀ ∈ B) (hcB : ∀ b ∈ B, G.Adj c b) (hAb₀ : ∀ a ∈ A, G.Adj a b₀)
    (hmask : CleanMask G A B d) (hcd : c ≠ d) (hqc : G.Adj q c) (hqd : G.Adj q d)
    (a b : Fin n) (ha : a ∈ A) (hb : b ∈ B) (hbad : ¬ G.Adj a b) : b = q := by
  classical
  have hnotad : ¬ G.Adj a d := by
    intro had
    have h₁ := hcolor a b₀ (hAb₀ a ha)
    have h₂ := hcolor c b₀ (hcB b₀ hb₀)
    have h₃ := hcolor q c hqc
    have h₄ := hcolor q d hqd
    have h₅ := hcolor a d had
    cases ha : color a <;> cases hb : color b₀ <;> cases hc : color c <;>
      cases hq : color q <;> cases hd : color d <;> simp_all
  let x : Fin n → Bool := fun z => decide (z = a ∨ z = b ∨ z = d)
  have hprod : productValue A B x = true := by
    simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq]
    exact ⟨⟨a,ha,by simp [x]⟩,⟨b,hb,by simp [x]⟩⟩
  obtain ⟨u,v,huv,hu,hv⟩ := hmask x hprod (by simp [x])
  simp only [x,decide_eq_true_eq] at hu hv
  have hdb : G.Adj d b := by
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact (hbad huv).elim
    · exact (hnotad huv).elim
    · exact (hbad huv.symm).elim
    · exact (G.loopless.irrefl _ huv).elim
    · exact huv.symm
    · exact (hnotad huv.symm).elim
    · exact huv
    · exact (G.loopless.irrefl _ huv).elim
  by_contra hbq
  have hsub : ({b,q} : Finset (Fin n)) ⊆ Finset.univ.filter (fun z => G.Adj c z ∧ G.Adj d z) := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcB _ hb,hdb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqc.symm,hqd.symm⟩
  have hn := (Finset.card_le_card hsub).trans (h4 c d hcd)
  have hs : ({b,q} : Finset (Fin n)).card = 2 := by simp [hbq]
  omega

lemma common_neighbor_shared_mask_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B : Finset (Fin n)) (c d q b₀ : Fin n)
    (hcA : c ∈ A) (hb₀ : b₀ ∈ B)
    (hcB : ∀ b ∈ B, G.Adj c b) (hAb₀ : ∀ a ∈ A, G.Adj a b₀)
    (hmask : CleanMask G A B d) (hcd : c ≠ d) (hqc : G.Adj q c) (hqd : G.Adj q d)
    (hbad : ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b) :
    q ∈ B ∧ s(c,q) ∈ MaskGrouping.starEdges A B c := by
  obtain ⟨a,ha,b,hb,hbad⟩ := hbad
  have heq := common_neighbor_bad_column G h4 color hcolor A B c d q b₀ hb₀ hcB hAb₀
    hmask hcd hqc hqd a b ha hb hbad
  subst b
  refine ⟨hb,?_⟩
  simp only [MaskGrouping.starEdges,neighbors,if_pos hcA]
  exact Finset.mem_image.mpr ⟨q,hb,rfl⟩

end PEqualNP.Outside.L_meta_1477.SharedMaskCollision


namespace PEqualNP.Outside.L_meta_1477.SharedMaskCollision

open PEqualNP.TopForm Structural StructuralMasks MaskGrouping

lemma common_neighbor_opposite_side_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (c d q b₀ : Fin n)
    (hb₀ : b₀ ∈ B) (hcB : ∀ b ∈ B, G.Adj c b) (hAb₀ : ∀ a ∈ A, G.Adj a b₀)
    (hmask : CleanMask G A B d) (hcd : c ≠ d) (hqc : G.Adj q c) (hqd : G.Adj q d) :
    B.card ≤ 2 := by
  classical
  have hcomplete : ∀ a ∈ A, ∀ b ∈ B.erase q, G.Adj a b := by
    intro a ha b hb
    obtain ⟨hbq,hb⟩ := Finset.mem_erase.mp hb
    by_contra hbad
    exact hbq (common_neighbor_bad_column G h4 color hcolor A B c d q b₀
      hb₀ hcB hAb₀ hmask hcd hqc hqd a b ha hb hbad)
  obtain ⟨a,ha,a',ha',hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hsub : B.erase q ⊆ Finset.univ.filter (fun b => G.Adj a b ∧ G.Adj a' b) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcomplete a ha b hb,hcomplete a' ha' b hb⟩
  have hs := (Finset.card_le_card hsub).trans (h4 a a' hne)
  by_cases hq : q ∈ B
  · have he := Finset.card_erase_add_one hq
    omega
  · rw [Finset.erase_eq_of_notMem hq] at hs
    omega

end PEqualNP.Outside.L_meta_1477.SharedMaskCollision


namespace PEqualNP.Outside.L_meta_1477.SharedMaskCollision

open PEqualNP.TopForm Structural StructuralMasks MaskGrouping

lemma universal_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (a b : Fin n) (ha : ∀ v ∈ S, G.Adj a v) (hb : ∀ v ∈ S, G.Adj b v) : a = b := by
  classical
  have hsmall := commonNeighbors_card_le_one G h4 Finset.univ S hS
  exact Finset.card_le_one.mp hsmall a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
    b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)

lemma common_neighbor_cover_exchange {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c d q b₀ : Fin n) (hcA : c ∈ A) (hb₀ : b₀ ∈ B)
    (hcB : ∀ b ∈ B, G.Adj c b) (hAb₀ : ∀ a ∈ A, G.Adj a b₀)
    (hmask : CleanMask G A B d) (hcd : c ≠ d) (hqc : G.Adj q c) (hqd : G.Adj q d) :
    ∀ z ∈ cleanCenters G A B, ∀ e ∈ MaskGrouping.starEdges A B z, b₀ ∈ e ∨ q ∈ e := by
  classical
  have hBsub : ∀ b ∈ B, b = b₀ ∨ b = q := by
    intro b hb
    by_cases hbq : b = q
    · exact Or.inr hbq
    · left
      apply universal_equal G h4 A hA b b₀
      · intro a ha
        have hab : G.Adj a b := by
          by_contra hbad
          exact hbq (common_neighbor_bad_column G h4 color hcolor A B c d q b₀
            hb₀ hcB hAb₀ hmask hcd hqc hqd a b ha hb hbad)
        exact hab.symm
      · exact fun a ha => (hAb₀ a ha).symm
  intro z hz e he
  have hz' := hz
  rw [cleanCenters] at hz'
  rcases Finset.mem_union.mp hz' with hzA | hzB
  · have hzc := universal_equal G h4 B hB z c (Finset.mem_filter.mp hzA).2 hcB
    subst z
    simp only [MaskGrouping.starEdges,neighbors,if_pos hcA] at he
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    rcases hBsub v hv with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · have hzb := universal_equal G h4 A hA z b₀
      (fun a ha => ((Finset.mem_filter.mp hzB).2 a ha).symm)
      (fun a ha => (hAb₀ a ha).symm)
    subst z
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
    exact Or.inl (by simp)

end PEqualNP.Outside.L_meta_1477.SharedMaskCollision
