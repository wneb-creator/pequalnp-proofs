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

namespace PEqualNP.Outside.L_meta_1477.MaskGrouping

open Structural StructuralMasks PEqualNP.EdgeOwnership

lemma center_not_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    c ∉ neighbors A B c := by
  intro hv
  exact G.loopless.irrefl c (center_neighbors_clean G A B c hc c hv)

lemma masked_pair_in_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B)
    (u v : Fin n) (hprod : productValue A B (pairInput u v) = true)
    (hmask : pairInput u v c = true) : s(u, v) ∈ starEdges A B c := by
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  have he : ∃ w ∈ neighbors A B c, pairInput u v w = true := by
    by_cases hca : c ∈ A
    · simpa only [neighbors, if_pos hca] using hprod.2
    · simpa only [neighbors, if_neg hca] using hprod.1
  obtain ⟨w, hw, hpw⟩ := he
  have hcw : c ≠ w := fun h => center_not_neighbors G A B c hc (h ▸ hw)
  apply Finset.mem_image.mpr
  refine ⟨w, hw, ?_⟩
  simp only [pairInput, decide_eq_true_eq] at hmask hpw
  rcases hmask with rfl | rfl <;> rcases hpw with rfl | rfl
  · exact (hcw rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hcw rfl).elim

lemma star_pair_masked {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B)
    (u v : Fin n) (he : s(u, v) ∈ starEdges A B c) :
    productValue A B (pairInput u v) = true ∧ pairInput u v c = true := by
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp he
  have hcm := (mem_centers_iff G A B c).mp hc
  have hv : productValue A B (pairInput c w) = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    by_cases hca : c ∈ A
    · have hwb : w ∈ B := by simpa only [neighbors, if_pos hca] using hw
      exact ⟨⟨c, hca, by simp [pairInput]⟩, ⟨w, hwb, by simp [pairInput]⟩⟩
    · have hcb : c ∈ B := (Finset.mem_union.mp hcm.1).resolve_left hca
      have hwa : w ∈ A := by simpa only [neighbors, if_neg hca] using hw
      exact ⟨⟨w, hwa, by simp [pairInput]⟩, ⟨c, hcb, by simp [pairInput]⟩⟩
  have hpair : pairInput c w = pairInput u v := by
    funext z
    apply Bool.eq_iff_iff.mpr
    have hz := Iff.of_eq (congrArg (fun e : Sym2 (Fin n) => z ∈ e) he)
    simpa only [pairInput, decide_eq_true_eq, Sym2.mem_iff] using hz
  rw [← hpair]
  exact ⟨hv, by simp [pairInput]⟩

lemma effective_mask_pair_covered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (u v c : Fin n)
    (huv : G.Adj u v) (hprod : productValue A B (pairInput u v) = true)
    (hmask : pairInput u v c = true) (hclean : CleanMask G A B c) :
    c ∈ cleanCenters G A B ∧ s(u, v) ∈ starEdges A B c := by
  have hm : c ∈ cleanCenters G A B := (mem_centers_iff G A B c).mpr
    ⟨effectiveMask_mem_union G A B hdis c ⟨u, v, huv, hprod, hmask⟩, hclean⟩
  exact ⟨hm, masked_pair_in_star G A B c hm u v hprod hmask⟩

end PEqualNP.Outside.L_meta_1477.MaskGrouping


namespace PEqualNP.Outside.L_meta_1477.TwoCenters

open PEqualNP.TopForm

lemma cross_edge_centered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v)
    (u v : Fin n) (hu : u ∈ A) (hv : v ∈ B) (huv : G.Adj u v) :
    u = a ∨ v = b := by
  by_cases hua : u = a
  · exact Or.inl hua
  apply Or.inr
  by_contra hvb
  have hsub : {b, v} ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj u w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB _ hb, hA u hu⟩
    · have he : w = v := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB v hv, huv⟩
  have hcard : ({b, v} : Finset (Fin n)).card = 2 := by simp [Ne.symm hvb]
  have hle := (Finset.card_le_card hsub).trans (hG a u (Ne.symm hua))
  omega

lemma cross_edges_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v) :
    (A ×ˢ B).filter (fun p => G.Adj p.1 p.2) = ({a} ×ˢ B) ∪ (A ×ˢ {b}) := by
  ext p
  rcases p with ⟨u, v⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hu, hv⟩, huv⟩
    rcases cross_edge_centered G hG A B a b ha hb hA hB u v hu hv huv with rfl | rfl
    · exact Or.inl ⟨rfl, hv⟩
    · exact Or.inr ⟨hu, rfl⟩
  · rintro (⟨rfl, hv⟩ | ⟨hu, rfl⟩)
    · exact ⟨⟨ha, hv⟩, hB v hv⟩
    · exact ⟨⟨hu, hb⟩, hA u hu⟩

lemma cross_edges_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v) :
    ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card + 1 = A.card + B.card := by
  rw [cross_edges_eq G hG A B a b ha hb hA hB]
  have hi : ({a} ×ˢ B) ∩ (A ×ˢ {b}) = {(a, b)} := by
    ext p
    rcases p with ⟨u, v⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, hb⟩, ⟨ha, rfl⟩⟩
  have hc := Finset.card_union_add_card_inter ({a} ×ˢ B) (A ×ˢ {b})
  rw [hi] at hc
  simpa [Finset.card_product, Nat.add_comm] using hc

end PEqualNP.Outside.L_meta_1477.TwoCenters


namespace PEqualNP.Outside.L_meta_1477.JointCentersStar

open PEqualNP.TopForm

def crossEdges {n : ℕ} (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (A ×ˢ B).image fun p => s(p.1, p.2)

def jointEdges {n : ℕ} (A B C D : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  crossEdges (A ∩ C) (B ∩ D) ∪ crossEdges (A ∩ D) (B ∩ C)

def SideCenter {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Prop :=
  (∃ p, ∀ b ∈ B, G.Adj p b) ∨ (∃ p, ∀ a ∈ A, G.Adj a p)

lemma bipartite_five_edges_absurd {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (p q a b c : Fin n) (hpc : G.Adj p c) (hqc : G.Adj q c)
    (hpa : G.Adj p a) (hqb : G.Adj q b) (hab : G.Adj a b) : False := by
  have h₁ := hcolor p c hpc
  have h₂ := hcolor q c hqc
  have h₃ := hcolor p a hpa
  have h₄ := hcolor q b hqb
  have h₅ := hcolor a b hab
  cases hp : color p <;> cases hq : color q <;> cases ha : color a <;>
    cases hb : color b <;> cases hc : color c <;> simp_all

lemma opposite_rectangles_incompatible {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (hAB : SideCenter G A B) (hCD : SideCenter G C D)
    (u v y z : Fin n) (hu : u ∈ A ∩ C) (hv : v ∈ B ∩ D)
    (hy : y ∈ A ∩ D) (hz : z ∈ B ∩ C) (huv : G.Adj u v) (hyz : G.Adj y z) : False := by
  obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvB, hvD⟩ := Finset.mem_inter.mp hv
  obtain ⟨hyA, hyD⟩ := Finset.mem_inter.mp hy
  obtain ⟨hzB, hzC⟩ := Finset.mem_inter.mp hz
  rcases hAB with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases hCD with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact bipartite_five_edges_absurd G color hcolor p q z y v
      (hp v hvB) (hq v hvD) (hp z hzB) (hq y hyD) hyz.symm
  · exact bipartite_five_edges_absurd G color hcolor p q v u z
      (hp z hzB) (hq z hzC).symm (hp v hvB) (hq u huC).symm huv.symm
  · exact bipartite_five_edges_absurd G color hcolor p q u v y
      (hp y hyA).symm (hq y hyD) (hp u huA).symm (hq v hvD) huv
  · exact bipartite_five_edges_absurd G color hcolor p q y z u
      (hp u huA).symm (hq u huC).symm (hp y hyA).symm (hq z hzC).symm hyz

lemma rectangle_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ K : Finset (Fin n), K.card ≤ 1 ∧ ∀ e ∈ crossEdges A B, ∃ v ∈ K, v ∈ e := by
  classical
  by_cases hA : A.card ≤ 1
  · refine ⟨A, hA, ?_⟩
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨p.1, (Finset.mem_product.mp hp).1, by simp⟩
  · obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hsub : B ⊆ Finset.univ.filter (fun b => G.Adj a b ∧ G.Adj a' b) := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB a ha b hb, hAB a' ha' b hb⟩
    refine ⟨B, (Finset.card_le_card hsub).trans (h4 a a' haa), ?_⟩
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨p.2, (Finset.mem_product.mp hp).2, by simp⟩

lemma joint_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (hAB : SideCenter G A B) (hCD : SideCenter G C D)
    (hclean : ∀ e ∈ jointEdges A B C D, e ∈ G.edgeFinset) :
    ∃ K : Finset (Fin n), K.card ≤ 1 ∧
      ∀ e ∈ jointEdges A B C D, ∃ v ∈ K, v ∈ e := by
  classical
  have hfirst : ∀ u ∈ A ∩ C, ∀ v ∈ B ∩ D, G.Adj u v := by
    intro u hu v hv
    apply (G.mem_edgeSet).mp
    apply (SimpleGraph.mem_edgeFinset).mp
    apply hclean
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, rfl⟩)
  have hsecond : ∀ y ∈ A ∩ D, ∀ z ∈ B ∩ C, G.Adj y z := by
    intro y hy z hz
    apply (G.mem_edgeSet).mp
    apply (SimpleGraph.mem_edgeFinset).mp
    apply hclean
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y,z), Finset.mem_product.mpr ⟨hy,hz⟩, rfl⟩)
  have hempty : crossEdges (A ∩ C) (B ∩ D) = ∅ ∨ crossEdges (A ∩ D) (B ∩ C) = ∅ := by
    by_cases h : crossEdges (A ∩ C) (B ∩ D) = ∅
    · exact Or.inl h
    · right
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨f, hf⟩ := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      obtain ⟨hy, hz⟩ := Finset.mem_product.mp hq
      exact opposite_rectangles_incompatible G color hcolor A B C D hAB hCD
        p.1 p.2 q.1 q.2 hu hv hy hz (hfirst _ hu _ hv) (hsecond _ hy _ hz)
  rcases hempty with h | h
  · obtain ⟨K, hK, hcov⟩ := rectangle_cover_one G h4 (A ∩ D) (B ∩ C) hsecond
    refine ⟨K, hK, ?_⟩
    simpa only [jointEdges, h, Finset.empty_union] using hcov
  · obtain ⟨K, hK, hcov⟩ := rectangle_cover_one G h4 (A ∩ C) (B ∩ D) hfirst
    refine ⟨K, hK, ?_⟩
    simpa only [jointEdges, h, Finset.union_empty] using hcov

end PEqualNP.Outside.L_meta_1477.JointCentersStar

namespace PEqualNP.Outside.L_meta_1477.PrivateJointCover

open PEqualNP.TopForm Structural StructuralMasks MaskGrouping JointCentersStar

def maskEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  crossEdges (A.filter fun a => ∀ b ∈ B, G.Adj a b) B ∪
    crossEdges A (B.filter fun b => ∀ a ∈ A, G.Adj a b)

lemma cross_mem {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n)
    (hu : u ∈ A) (hv : v ∈ B) : s(u,v) ∈ crossEdges A B :=
  Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, rfl⟩

lemma mask_subset_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : maskEdges G A B ⊆ crossEdges A B := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact cross_mem A B p.1 p.2 (Finset.mem_filter.mp ha).1 hb
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact cross_mem A B p.1 p.2 ha (Finset.mem_filter.mp hb).1

lemma mask_cover_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) :
    ∀ e ∈ maskEdges G A B, ∃ c ∈ cleanCenters G A B, c ∈ e := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨p.1, Finset.mem_union_left _ (Finset.mem_product.mp hp).1, by simp⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨p.2, Finset.mem_union_right _ (Finset.mem_product.mp hp).2, by simp⟩

lemma opposite_centers_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B) (hca : a ∈ cleanCenters G A B)
    (hcb : b ∈ cleanCenters G A B) (u v : Fin n)
    (hu : u ∈ A) (hv : v ∈ B) (huv : G.Adj u v) : s(u,v) ∈ maskEdges G A B := by
  have hrow := (cleanMask_of_mem_left_iff G A B a ha).mp
    ((mem_centers_iff G A B a).mp hca).2
  have hcol := (cleanMask_of_mem_right_iff G A B b hb).mp
    ((mem_centers_iff G A B b).mp hcb).2
  rcases TwoCenters.cross_edge_centered G h4 A B a b ha hb hcol hrow u v hu hv huv with rfl | rfl
  · exact Finset.mem_union_left _ (cross_mem _ _ u v (Finset.mem_filter.mpr ⟨ha,hrow⟩) hv)
  · exact Finset.mem_union_right _ (cross_mem _ _ u v hu
      (Finset.mem_filter.mpr ⟨hb, hcol⟩))

lemma private_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (u v : Fin n) (hu : u ∈ A) (hv : v ∈ B) (huv : G.Adj u v)
    (hprivate : s(u,v) ∉ maskEdges G A B) : (cleanCenters G A B).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  rcases different_centers_cross G h4 A B hA hB a b ha hb hab with h | h
  · exact hprivate (opposite_centers_mask G h4 A B a b h.1 h.2 ha hb u v hu hv huv)
  · exact hprivate (opposite_centers_mask G h4 A B b a h.2 h.1 hb ha u v hu hv huv)

lemma private_mask_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (e : Sym2 (Fin n))
    (he : e ∈ crossEdges A B) (heg : e ∈ G.edgeFinset) (hp : e ∉ maskEdges G A B) :
    ∃ K : Finset (Fin n), K.card ≤ 1 ∧ ∀ f ∈ maskEdges G A B, ∃ v ∈ K, v ∈ f := by
  classical
  by_cases hA : A.card ≤ 1
  · refine ⟨A,hA,?_⟩
    intro f hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (mask_subset_cross G A B hf)
    exact ⟨p.1,(Finset.mem_product.mp hp).1,by simp⟩
  by_cases hB : B.card ≤ 1
  · refine ⟨B,hB,?_⟩
    intro f hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (mask_subset_cross G A B hf)
    exact ⟨p.2,(Finset.mem_product.mp hp).2,by simp⟩
  obtain ⟨p,hpAB,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp hpAB
  have huv : G.Adj p.1 p.2 := (G.mem_edgeSet).mp ((SimpleGraph.mem_edgeFinset).mp heg)
  exact ⟨cleanCenters G A B, private_centers_card G h4 A B (by omega) (by omega)
    p.1 p.2 hu hv huv hp, mask_cover_centers G A B⟩

end PEqualNP.Outside.L_meta_1477.PrivateJointCover

namespace PEqualNP.Outside.L_meta_1477.PrivateJointCover

open PEqualNP.TopForm JointCentersStar

lemma joint_subset_cross_left {n : ℕ} (A B C D : Finset (Fin n)) :
    jointEdges A B C D ⊆ crossEdges A B := by
  intro e he
  rcases Finset.mem_union.mp he with he | he <;>
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he <;>
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
  · exact cross_mem A B p.1 p.2 (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1
  · exact cross_mem A B p.1 p.2 (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1

lemma joint_subset_cross_right {n : ℕ} (A B C D : Finset (Fin n)) :
    jointEdges A B C D ⊆ crossEdges C D := by
  intro e he
  rcases Finset.mem_union.mp he with he | he <;>
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he <;>
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
  · exact cross_mem C D p.1 p.2 (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hv).2
  · simpa only [Sym2.eq_swap] using
      cross_mem C D p.2 p.1 (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hu).2

lemma mask_nonempty_sideCenter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (h : (maskEdges G A B).Nonempty) : SideCenter G A B := by
  obtain ⟨e,he⟩ := h
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨p.1, (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2⟩
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    exact Or.inr ⟨p.2, (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2⟩

lemma combine_covers {n : ℕ} (E F : Finset (Sym2 (Fin n))) (a b : ℕ)
    (hE : ∃ K : Finset (Fin n), K.card ≤ a ∧ ∀ e ∈ E, ∃ v ∈ K, v ∈ e)
    (hF : ∃ K : Finset (Fin n), K.card ≤ b ∧ ∀ e ∈ F, ∃ v ∈ K, v ∈ e) :
    ∃ K : Finset (Fin n), K.card ≤ a+b ∧ ∀ e ∈ E ∪ F, ∃ v ∈ K, v ∈ e := by
  obtain ⟨K,hK,hcovK⟩ := hE
  obtain ⟨L,hL,hcovL⟩ := hF
  refine ⟨K∪L, (Finset.card_union_le K L).trans (Nat.add_le_add hK hL), ?_⟩
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨v,hv,hve⟩ := hcovK e he
    exact ⟨v,Finset.mem_union_left _ hv,hve⟩
  · obtain ⟨v,hv,hve⟩ := hcovL e he
    exact ⟨v,Finset.mem_union_right _ hv,hve⟩

lemma joint_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hclean : ∀ e ∈ jointEdges A B C D, e ∈ G.edgeFinset) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ e ∈ jointEdges A B C D, ∃ v ∈ K, v ∈ e := by
  have h₁ : ∀ u ∈ A ∩ C, ∀ v ∈ B ∩ D, G.Adj u v := by
    intro u hu v hv
    exact (G.mem_edgeSet).mp ((SimpleGraph.mem_edgeFinset).mp
      (hclean _ (Finset.mem_union_left _ (cross_mem _ _ u v hu hv))))
  have h₂ : ∀ u ∈ A ∩ D, ∀ v ∈ B ∩ C, G.Adj u v := by
    intro u hu v hv
    exact (G.mem_edgeSet).mp ((SimpleGraph.mem_edgeFinset).mp
      (hclean _ (Finset.mem_union_right _ (cross_mem _ _ u v hu hv))))
  exact combine_covers _ _ 1 1 (rectangle_cover_one G h4 _ _ h₁)
    (rectangle_cover_one G h4 _ _ h₂)

lemma private_joint_cover_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n))
    (hclean : ∀ e ∈ jointEdges A B C D, e ∈ G.edgeFinset)
    (e : Sym2 (Fin n)) (he : e ∈ jointEdges A B C D)
    (hprivate : e ∉ maskEdges G A B ∪ maskEdges G C D) :
    ∃ K : Finset (Fin n), K.card ≤ 3 ∧
      ∀ f ∈ maskEdges G A B ∪ maskEdges G C D ∪ jointEdges A B C D,
        ∃ v ∈ K, v ∈ f := by
  classical
  have hp₁ : e ∉ maskEdges G A B := fun h => hprivate (Finset.mem_union_left _ h)
  have hp₂ : e ∉ maskEdges G C D := fun h => hprivate (Finset.mem_union_right _ h)
  have hc₁ := private_mask_cover G h4 A B e (joint_subset_cross_left A B C D he)
    (hclean e he) hp₁
  have hc₂ := private_mask_cover G h4 C D e (joint_subset_cross_right A B C D he)
    (hclean e he) hp₂
  by_cases h₁ : (maskEdges G A B).Nonempty
  · by_cases h₂ : (maskEdges G C D).Nonempty
    · have hj := joint_cover_one G h4 color hcolor A B C D
        (mask_nonempty_sideCenter G A B h₁) (mask_nonempty_sideCenter G C D h₂) hclean
      exact combine_covers _ _ 2 1 (combine_covers _ _ 1 1 hc₁ hc₂) hj
    · have hz := Finset.not_nonempty_iff_eq_empty.mp h₂
      simpa only [hz, Finset.union_empty] using
        combine_covers _ _ 1 2 hc₁ (joint_cover_two G h4 A B C D hclean)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp h₁
    simpa only [hz, Finset.empty_union] using
      combine_covers _ _ 1 2 hc₂ (joint_cover_two G h4 A B C D hclean)

end PEqualNP.Outside.L_meta_1477.PrivateJointCover


namespace PEqualNP.Outside.L_meta_1477.MaskJointForest

open PEqualNP.TopForm

lemma no_rectangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (a b c d : Fin n) (hab : a ≠ b)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : c = d := by
  by_contra hcd
  have hs : ({c,d} : Finset (Fin n)) ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac, hbc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hbd⟩
  have hcard := (Finset.card_le_card hs).trans (hG a b hab)
  simp [hcd] at hcard

lemma row_universal_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (hEn : E.Nonempty) (a : Fin n)
    (ha : ∀ b ∈ E.image Prod.snd, (a,b) ∈ E) :
    E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := by
  classical
  let F := E.filter fun e => e.1 = a
  let R := E.filter fun e => e.1 ≠ a
  have hF : F.card ≤ (E.image Prod.snd).card := by
    have hinj : Set.InjOn Prod.snd (↑F : Set (Fin n × Fin n)) := by
      intro e he f hf hef
      exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
  have hR : R.card ≤ ((E.image Prod.fst).erase a).card := by
    have hinj : Set.InjOn Prod.fst (↑R : Set (Fin n × Fin n)) := by
      intro e he f hf hef
      have heE := (Finset.mem_filter.mp he).1
      have hfE := (Finset.mem_filter.mp hf).1
      have hne : a ≠ e.1 := ((Finset.mem_filter.mp he).2).symm
      have hfirst : (a,e.2) ∈ E := ha _ (Finset.mem_image.mpr ⟨e, heE, rfl⟩)
      have hsecond : (a,f.2) ∈ E := ha _ (Finset.mem_image.mpr ⟨f, hfE, rfl⟩)
      have hsnd := no_rectangle G hG a e.1 e.2 f.2 hne
        (hE _ hfirst) (hE _ hsecond) (hE _ heE) (by simpa only [hef] using hE _ hfE)
      exact Prod.ext hef hsnd
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp he).2,
      Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩⟩
  have haE : a ∈ E.image Prod.fst := by
    obtain ⟨e, he⟩ := hEn
    exact Finset.mem_image.mpr ⟨(a,e.2), ha _ (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
  have hdis : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp he).2
  have hun : F ∪ R = E := by
    ext e
    simp only [F, R, Finset.mem_union, Finset.mem_filter]
    tauto
  have hsum : F.card + R.card = E.card := by
    rw [← Finset.card_union_of_disjoint hdis, hun]
  have herase := Finset.card_erase_add_one haE
  omega

lemma column_universal_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (hEn : E.Nonempty) (b : Fin n)
    (hb : ∀ a ∈ E.image Prod.fst, (a,b) ∈ E) :
    E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := by
  classical
  let T := E.image Prod.swap
  have hT : ∀ e ∈ T, G.Adj e.1 e.2 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (hE f hf).symm
  have hTsnd : T.image Prod.snd = E.image Prod.fst := by
    simp [T, Finset.image_image, Function.comp_def]
  have hTfst : T.image Prod.fst = E.image Prod.snd := by
    simp [T, Finset.image_image, Function.comp_def]
  have hTcard : T.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
  have hbb : ∀ a ∈ T.image Prod.snd, (b,a) ∈ T := by
    intro a ha
    rw [hTsnd] at ha
    exact Finset.mem_image.mpr ⟨(a,b), hb a ha, rfl⟩
  have hh := row_universal_bound G hG T hT (hEn.image _) b hbb
  rw [hTcard, hTfst, hTsnd] at hh
  omega

end PEqualNP.Outside.L_meta_1477.MaskJointForest

namespace PEqualNP.Outside.L_meta_1477.MaskJointForest

open PEqualNP.TopForm

lemma rectangle_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (X Y : Finset (Fin n))
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b) (hN : (X ×ˢ Y).Nonempty) :
    (X ×ˢ Y).card + 1 ≤ ((X ×ˢ Y).image Prod.fst).card + ((X ×ˢ Y).image Prod.snd).card := by
  obtain ⟨e, he⟩ := hN
  have hXe := (Finset.mem_product.mp he).1
  apply row_universal_bound G hG (X ×ˢ Y)
    (fun f hf => hXY f.1 (Finset.mem_product.mp hf).1 f.2 (Finset.mem_product.mp hf).2)
    ⟨e, he⟩ e.1
  intro b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_product.mpr ⟨hXe, (Finset.mem_product.mp hf).2⟩

lemma disjoint_union_bound {n : ℕ} (E F : Finset (Fin n × Fin n))
    (hleft : Disjoint (E.image Prod.fst) (F.image Prod.fst))
    (hright : Disjoint (E.image Prod.snd) (F.image Prod.snd))
    (hE : E.Nonempty → E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card)
    (hF : F.Nonempty → F.card + 1 ≤ (F.image Prod.fst).card + (F.image Prod.snd).card)
    (hN : (E ∪ F).Nonempty) :
    (E ∪ F).card + 1 ≤ ((E ∪ F).image Prod.fst).card + ((E ∪ F).image Prod.snd).card := by
  by_cases he : E = ∅
  · simpa only [he, Finset.empty_union] using hF (by simpa only [he, Finset.empty_union] using hN)
  by_cases hf : F = ∅
  · simpa only [hf, Finset.union_empty] using hE (by simpa only [hf, Finset.union_empty] using hN)
  have hdis : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hleft (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      (Finset.mem_image.mpr ⟨e, hf, rfl⟩)
  rw [Finset.card_union_of_disjoint hdis, Finset.image_union, Finset.image_union,
    Finset.card_union_of_disjoint hleft, Finset.card_union_of_disjoint hright]
  have hhE := hE (Finset.nonempty_iff_ne_empty.mpr he)
  have hhF := hF (Finset.nonempty_iff_ne_empty.mpr hf)
  omega

lemma two_rectangles_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (X Y Z W : Finset (Fin n))
    (hXZ : Disjoint X Z) (hYW : Disjoint Y W)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b)
    (hZW : ∀ a ∈ Z, ∀ b ∈ W, G.Adj a b)
    (hN : ((X ×ˢ Y) ∪ (Z ×ˢ W)).Nonempty) :
    ((X ×ˢ Y) ∪ (Z ×ˢ W)).card + 1 ≤
      (((X ×ˢ Y) ∪ (Z ×ˢ W)).image Prod.fst).card +
        (((X ×ˢ Y) ∪ (Z ×ˢ W)).image Prod.snd).card := by
  apply disjoint_union_bound (X ×ˢ Y) (Z ×ˢ W) ?_ ?_
    (rectangle_bound G hG X Y hXY) (rectangle_bound G hG Z W hZW) hN
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f, hf, hef⟩ := Finset.mem_image.mp hb
    exact Finset.disjoint_left.mp hXZ (Finset.mem_product.mp he).1
      (hef ▸ (Finset.mem_product.mp hf).1)
  · apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨f, hf, hef⟩ := Finset.mem_image.mp hc
    exact Finset.disjoint_left.mp hYW (Finset.mem_product.mp he).2
      (hef ▸ (Finset.mem_product.mp hf).2)

def maskJointEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (A ×ˢ B).filter fun e =>
    (∀ b ∈ B, G.Adj e.1 b) ∨ (∀ a ∈ A, G.Adj e.2 a) ∨
      ((e.1 ∈ C ∨ e.2 ∈ C) ∧ (e.1 ∈ D ∨ e.2 ∈ D))

lemma maskJointEdges_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n)) (hCD : Disjoint C D)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b)
    (hN : (maskJointEdges G A B C D).Nonempty) :
    (maskJointEdges G A B C D).card + 1 ≤
      ((maskJointEdges G A B C D).image Prod.fst).card +
        ((maskJointEdges G A B C D).image Prod.snd).card := by
  classical
  let E := maskJointEdges G A B C D
  have hE : ∀ e ∈ E, G.Adj e.1 e.2 := by
    intro e he
    obtain ⟨heAB, heJ⟩ := Finset.mem_filter.mp he
    obtain ⟨heA, heB⟩ := Finset.mem_product.mp heAB
    rcases heJ with hrow | hcol | ⟨hC, hD⟩
    · exact hrow _ heB
    · exact (hcol _ heA).symm
    · exact hjoint _ heA _ heB hC hD
  by_cases hrow : ∃ a ∈ A, ∀ b ∈ B, G.Adj a b
  · obtain ⟨a, ha, hab⟩ := hrow
    apply row_universal_bound G hG E hE hN a
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    have heB := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, heB⟩, Or.inl hab⟩
  by_cases hcol : ∃ b ∈ B, ∀ a ∈ A, G.Adj b a
  · obtain ⟨b, hb, hba⟩ := hcol
    apply column_universal_bound G hG E hE hN b
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have heA := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heA, hb⟩, Or.inr (Or.inl hba)⟩
  have heq : E = ((A ∩ C) ×ˢ (B ∩ D)) ∪ ((A ∩ D) ×ˢ (B ∩ C)) := by
    ext e
    simp only [E, maskJointEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨⟨ha, hb⟩, hr | hc | ⟨hC, hD⟩⟩
      · exact (hrow ⟨e.1, ha, hr⟩).elim
      · exact (hcol ⟨e.2, hb, hc⟩).elim
      · rcases hC with hc | hc <;> rcases hD with hd | hd
        · exact (Finset.disjoint_left.mp hCD hc hd).elim
        · exact Or.inl ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩
        · exact Or.inr ⟨⟨ha, hd⟩, ⟨hb, hc⟩⟩
        · exact (Finset.disjoint_left.mp hCD hc hd).elim
    · rintro (⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩ | ⟨⟨ha, hd⟩, ⟨hb, hc⟩⟩)
      · exact ⟨⟨ha, hb⟩, Or.inr (Or.inr ⟨Or.inl hc, Or.inr hd⟩)⟩
      · exact ⟨⟨ha, hb⟩, Or.inr (Or.inr ⟨Or.inr hc, Or.inl hd⟩)⟩
  change E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card
  rw [heq]
  apply two_rectangles_bound G hG (A ∩ C) (B ∩ D) (A ∩ D) (B ∩ C)
  · exact Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp hCD (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  · exact Finset.disjoint_left.mpr fun b hb hc =>
      Finset.disjoint_left.mp hCD (Finset.mem_inter.mp hc).2 (Finset.mem_inter.mp hb).2
  · intro a ha b hb
    exact hjoint a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
      (Or.inl (Finset.mem_inter.mp ha).2) (Or.inr (Finset.mem_inter.mp hb).2)
  · intro a ha b hb
    exact hjoint a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
      (Or.inr (Finset.mem_inter.mp hb).2) (Or.inl (Finset.mem_inter.mp ha).2)
  · simpa only [← heq] using hN

end PEqualNP.Outside.L_meta_1477.MaskJointForest

namespace PEqualNP.Outside.L_meta_1477.MaskJointForest

open PEqualNP.TopForm

def undirected {n : ℕ} (E : Finset (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  E.image fun e => s(e.1,e.2)

def active {n : ℕ} (U : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  U.biUnion Sym2.toFinset

lemma active_undirected {n : ℕ} (E : Finset (Fin n × Fin n)) :
    active (undirected E) = E.image Prod.fst ∪ E.image Prod.snd := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_biUnion.mpr ⟨s(p.1,p.2), Finset.mem_image.mpr ⟨p, hp, rfl⟩,
        by simp only [Sym2.mem_toFinset, Sym2.mem_iff, true_or]⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_biUnion.mpr ⟨s(p.1,p.2), Finset.mem_image.mpr ⟨p, hp, rfl⟩,
        by simp only [Sym2.mem_toFinset, Sym2.mem_iff, or_true]⟩

lemma separated_images {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ A ×ˢ B) :
    Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hw
  exact Finset.disjoint_left.mp hAB (Finset.mem_product.mp (hE hp)).1
    (hqp ▸ (Finset.mem_product.mp (hE hq)).2)

lemma undirected_card {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (E : Finset (Fin n × Fin n)) (hE : E ⊆ A ×ˢ B) :
    (undirected E).card = E.card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  rcases Sym2.eq_iff.mp heq with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact Prod.ext hfirst hsecond
  · exact (Finset.disjoint_left.mp hAB (Finset.mem_product.mp (hE hp)).1
      (hfirst.symm ▸ (Finset.mem_product.mp (hE hq)).2)).elim

lemma undirected_maskJoint_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b)
    (hN : (undirected (maskJointEdges G A B C D)).Nonempty) :
    (undirected (maskJointEdges G A B C D)).card + 1 ≤
      (active (undirected (maskJointEdges G A B C D))).card := by
  have hsub : maskJointEdges G A B C D ⊆ A ×ˢ B := Finset.filter_subset _ _
  have hEn : (maskJointEdges G A B C D).Nonempty := by
    obtain ⟨e, he⟩ := hN
    obtain ⟨p, hp, _⟩ := Finset.mem_image.mp he
    exact ⟨p, hp⟩
  rw [undirected_card A B hAB _ hsub, active_undirected,
    Finset.card_union_of_disjoint (separated_images A B hAB _ hsub)]
  exact maskJointEdges_bound G hG A B C D hCD hjoint hEn

end PEqualNP.Outside.L_meta_1477.MaskJointForest




namespace PEqualNP.Outside.L_meta_1477.MaskJointSemantics

open PEqualNP.EdgeOwnership StructuralMasks MaskJointForest

lemma pair_symm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext z
  simp only [pairInput, or_comm]

lemma or_pair_members {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    orValue A (pairInput u v) = true ↔ u ∈ A ∨ v ∈ A := by
  simp only [orValue, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, ha, he⟩
    rcases he with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma product_pair_members {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n) :
    productValue A B (pairInput u v) = true ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) := by
  simp only [productValue, Bool.and_eq_true, or_pair_members]

lemma disjoint_product_pair {n : ℕ} (A B : Finset (Fin n))
    (hAB : Disjoint A B) (u v : Fin n) :
    productValue A B (pairInput u v) = true ↔ (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B) := by
  rw [product_pair_members]
  constructor
  · rintro ⟨hu | hv, huB | hvB⟩
    · exact (Finset.disjoint_left.mp hAB hu huB).elim
    · exact Or.inl ⟨hu, hvB⟩
    · exact Or.inr ⟨hv, huB⟩
    · exact (Finset.disjoint_left.mp hAB hv hvB).elim
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨Or.inl hu, Or.inr hv⟩
    · exact ⟨Or.inr hv, Or.inl hu⟩

lemma undirected_mem {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) :
    s(u,v) ∈ undirected E ↔ (u,v) ∈ E ∨ (v,u) ∈ E := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    rcases Sym2.eq_iff.mp he with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · exact Or.inl (by simpa only [← he1, ← he2] using hp)
    · exact Or.inr (by simpa only [← he1, ← he2] using hp)
  · rintro (h | h)
    · exact Finset.mem_image.mpr ⟨(u,v), h, rfl⟩
    · exact Finset.mem_image.mpr ⟨(v,u), h, Sym2.eq_swap⟩

lemma oriented_mem_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (a b : Fin n) (ha : a ∈ A) (hb : b ∈ B) :
    (a,b) ∈ maskJointEdges G A B C D ↔
      (∃ c : Fin n, CleanMask G A B c ∧ pairInput a b c = true) ∨
        productValue C D (pairInput a b) = true := by
  simp only [maskJointEdges, Finset.mem_filter, Finset.mem_product,
    ha, hb, true_and, product_pair_members]
  constructor
  · rintro (hr | hc | hj)
    · exact Or.inl ⟨a, (cleanMask_of_mem_left_iff G A B a ha).mpr hr, by simp [pairInput]⟩
    · exact Or.inl ⟨b, (cleanMask_of_mem_right_iff G A B b hb).mpr
        (fun v hv => (hc v hv).symm), by simp [pairInput]⟩
    · exact Or.inr hj
  · rintro (⟨c, hc, hp⟩ | hj)
    · simp only [pairInput, decide_eq_true_eq] at hp
      rcases hp with rfl | rfl
      · exact Or.inl ((cleanMask_of_mem_left_iff G A B _ ha).mp hc)
      · exact Or.inr (Or.inl (fun v hv =>
          ((cleanMask_of_mem_right_iff G A B _ hb).mp hc v hv).symm))
    · exact Or.inr (Or.inr hj)

lemma undirected_mem_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B) (u v : Fin n) :
    s(u,v) ∈ undirected (maskJointEdges G A B C D) ↔
      productValue A B (pairInput u v) = true ∧
        ((∃ c : Fin n, CleanMask G A B c ∧ pairInput u v c = true) ∨
          productValue C D (pairInput u v) = true) := by
  rw [undirected_mem, disjoint_product_pair A B hAB]
  constructor
  · rintro (h | h)
    · obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h).1
      exact ⟨Or.inl ⟨ha,hb⟩, (oriented_mem_semantics G A B C D u v ha hb).mp h⟩
    · obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h).1
      refine ⟨Or.inr ⟨ha,hb⟩, ?_⟩
      simpa only [pair_symm v u] using (oriented_mem_semantics G A B C D v u ha hb).mp h
  · rintro ⟨hab | hba, hj⟩
    · exact Or.inl ((oriented_mem_semantics G A B C D u v hab.1 hab.2).mpr hj)
    · apply Or.inr
      apply (oriented_mem_semantics G A B C D v u hba.1 hba.2).mpr
      simpa only [pair_symm v u] using hj

end PEqualNP.Outside.L_meta_1477.MaskJointSemantics

namespace PEqualNP.Outside.L_meta_1477.PrivateJointCover

open PEqualNP.TopForm PEqualNP.EdgeOwnership StructuralMasks JointCentersStar MaskJointForest

lemma mask_eq_undirected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) :
    maskEdges G A B = undirected (maskJointEdges G A B ∅ ∅) := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      obtain ⟨ha,hr⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hb⟩, Or.inl hr⟩, rfl⟩
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hb,hc⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha,hb⟩, Or.inr (Or.inl (fun a ha => (hc a ha).symm))⟩, rfl⟩
  · intro he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hp,h⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    rcases h with hr | hc | hj
    · exact Finset.mem_union_left _ (cross_mem _ _ p.1 p.2 (Finset.mem_filter.mpr ⟨ha,hr⟩) hb)
    · exact Finset.mem_union_right _ (cross_mem _ _ p.1 p.2 ha
        (Finset.mem_filter.mpr ⟨hb,fun a ha => (hc a ha).symm⟩))
    · simp at hj

lemma mask_pair_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hAB : Disjoint A B) (u v : Fin n) :
    s(u,v) ∈ maskEdges G A B ↔ productValue A B (pairInput u v) = true ∧
      ∃ c, CleanMask G A B c ∧ pairInput u v c = true := by
  rw [mask_eq_undirected, MaskJointSemantics.undirected_mem_semantics G A B ∅ ∅ hAB]
  simp [productValue,orValue]

lemma cross_pair_members {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n) :
    s(u,v) ∈ crossEdges A B ↔ (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B) := by
  change s(u,v) ∈ undirected (A ×ˢ B) ↔ _
  rw [MaskJointSemantics.undirected_mem]
  simp only [Finset.mem_product]

lemma joint_pair_semantics {n : ℕ} (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D) (u v : Fin n) :
    s(u,v) ∈ jointEdges A B C D ↔
      productValue A B (pairInput u v) = true ∧ productValue C D (pairInput u v) = true := by
  rw [MaskJointSemantics.disjoint_product_pair A B hAB,
    MaskJointSemantics.disjoint_product_pair C D hCD]
  simp only [jointEdges, Finset.mem_union, cross_pair_members, Finset.mem_inter]
  tauto

lemma joint_clean_of_products {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hclean : ∀ x, productValue A B x = true → productValue C D x = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    ∀ e ∈ jointEdges A B C D, e ∈ G.edgeFinset := by
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro he
    have hp := (joint_pair_semantics A B C D hAB hCD u v).mp he
    have hg := hclean (pairInput u v) hp.1 hp.2
    have huv : G.Adj u v := (graph_pair_iff G u v).mp (by
      simpa only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq] using hg)
    exact (SimpleGraph.mem_edgeFinset).mpr ((G.mem_edgeSet).mpr huv)

lemma private_semantic_cover_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hclean : ∀ x, productValue A B x = true → productValue C D x = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (u v : Fin n) (hg : productValue A B (pairInput u v) = true)
    (hh : productValue C D (pairInput u v) = true)
    (hn₁ : ¬∃ c, CleanMask G A B c ∧ pairInput u v c = true)
    (hn₂ : ¬∃ c, CleanMask G C D c ∧ pairInput u v c = true) :
    ∃ K : Finset (Fin n), K.card ≤ 3 ∧
      ∀ a b, (productValue A B (pairInput a b) = true ∧
          ((∃ c, CleanMask G A B c ∧ pairInput a b c = true) ∨
            productValue C D (pairInput a b) = true)) ∨
        (productValue C D (pairInput a b) = true ∧
          ∃ c, CleanMask G C D c ∧ pairInput a b c = true) → a ∈ K ∨ b ∈ K := by
  have he := (joint_pair_semantics A B C D hAB hCD u v).mpr ⟨hg,hh⟩
  have hp : s(u,v) ∉ maskEdges G A B ∪ maskEdges G C D := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hn₁ ((mask_pair_semantics G A B hAB u v).mp he).2
    · exact hn₂ ((mask_pair_semantics G C D hCD u v).mp he).2
  obtain ⟨K,hK,hcov⟩ := private_joint_cover_three G h4 color hcolor A B C D
    (joint_clean_of_products G A B C D hAB hCD hclean) s(u,v) he hp
  refine ⟨K,hK,?_⟩
  intro a b hab
  have he : s(a,b) ∈ maskEdges G A B ∪ maskEdges G C D ∪ jointEdges A B C D := by
    rcases hab with ⟨hg,hm | hh⟩ | ⟨hh,hm⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mask_pair_semantics G A B hAB a b).mpr ⟨hg,hm⟩))
    · exact Finset.mem_union_right _ ((joint_pair_semantics A B C D hAB hCD a b).mpr ⟨hg,hh⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mask_pair_semantics G C D hCD a b).mpr ⟨hh,hm⟩))
  obtain ⟨w,hw,hwe⟩ := hcov _ he
  rcases Sym2.mem_iff.mp hwe with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

end PEqualNP.Outside.L_meta_1477.PrivateJointCover

namespace PEqualNP.Outside.L_meta_1477.PrivateJointCover

open StructuralMasks PEqualNP.EdgeOwnership

lemma private_product_sides_large {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : Disjoint A B) (u v : Fin n)
    (hadj : G.Adj u v) (hprod : productValue A B (pairInput u v) = true)
    (hn : ¬ ∃ c, CleanMask G A B c ∧ pairInput u v c = true) :
    2 ≤ A.card ∧ 2 ≤ B.card := by
  have oriented (u v : Fin n) (hu : u ∈ A) (hv : v ∈ B) (hadj : G.Adj u v)
      (hn : ¬ ∃ c, CleanMask G A B c ∧ pairInput u v c = true) :
      2 ≤ A.card ∧ 2 ≤ B.card := by
    constructor
    · by_contra hc
      have hcard : A.card ≤ 1 := by omega
      rw [Finset.card_le_one] at hcard
      apply hn
      refine ⟨v,(cleanMask_of_mem_right_iff G A B v hv).mpr ?_,by simp [pairInput]⟩
      intro a ha
      have he := hcard a ha u hu
      simpa only [he] using hadj
    · by_contra hc
      have hcard : B.card ≤ 1 := by omega
      rw [Finset.card_le_one] at hcard
      apply hn
      refine ⟨u,(cleanMask_of_mem_left_iff G A B u hu).mpr ?_,by simp [pairInput]⟩
      intro b hb
      have he := hcard b hb v hv
      simpa only [he] using hadj
  rcases (MaskJointSemantics.disjoint_product_pair A B hAB u v).mp hprod with h | h
  · exact oriented u v h.1 h.2 hadj hn
  · apply oriented v u h.1 h.2 hadj.symm
    simpa only [MaskJointSemantics.pair_symm v u] using hn

end PEqualNP.Outside.L_meta_1477.PrivateJointCover
