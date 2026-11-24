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


namespace PEqualNP.Outside.L_meta_1477.JointCentersStar

open StructuralMasks

lemma same_orientation_clean_mask {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (u v p q : Fin n)
    (huA : u ∈ A) (huC : u ∈ C) (hvB : v ∈ B) (hvD : v ∈ D)
    (hp : ∀ b ∈ B, G.Adj p b) (hq : ∀ d ∈ D, G.Adj q d)
    (hclean : ∀ x : Fin n → Bool, productValue A B x = true → productValue C D x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    CleanMask G A B u ∨ CleanMask G C D u := by
  classical
  by_contra hn
  obtain ⟨hAB, hCD⟩ := not_or.mp hn
  have hbadB : ¬ ∀ b ∈ B, G.Adj u b := fun h =>
    hAB ((cleanMask_of_mem_left_iff G A B u huA).mpr h)
  have hbadD : ¬ ∀ d ∈ D, G.Adj u d := fun h =>
    hCD ((cleanMask_of_mem_left_iff G C D u huC).mpr h)
  push_neg at hbadB hbadD
  obtain ⟨b, hb, hub⟩ := hbadB
  obtain ⟨d, hd, hud⟩ := hbadD
  have hbd : ¬ G.Adj b d := fun h => bipartite_five_edges_absurd G color hcolor
    p q b d v (hp v hvB) (hq v hvD) (hp b hb) (hq d hd) h
  let x : Fin n → Bool := fun z => decide (z = u ∨ z = b ∨ z = d)
  have hxu : x u = true := by simp [x]
  have hxb : x b = true := by simp [x]
  have hxd : x d = true := by simp [x]
  have hvAB : productValue A B x = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨u, huA, hxu⟩, ⟨b, hb, hxb⟩⟩
  have hvCD : productValue C D x = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨u, huC, hxu⟩, ⟨d, hd, hxd⟩⟩
  obtain ⟨a, b', hab, ha, hb'⟩ := hclean x hvAB hvCD
  simp only [x, decide_eq_true_eq] at ha hb'
  rcases ha with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
  · exact G.irrefl hab
  · exact hub hab
  · exact hud hab
  · exact hub hab.symm
  · exact G.irrefl hab
  · exact hbd hab
  · exact hud hab.symm
  · exact hbd hab.symm
  · exact G.irrefl hab

lemma opposite_orientation_of_private_pair {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (u v p q : Fin n)
    (hu : u ∈ A ∩ C) (hv : v ∈ B ∩ D)
    (hp : (p ∈ A ∧ ∀ b ∈ B, G.Adj p b) ∨ (p ∈ B ∧ ∀ a ∈ A, G.Adj a p))
    (hq : (q ∈ C ∧ ∀ d ∈ D, G.Adj q d) ∨ (q ∈ D ∧ ∀ c ∈ C, G.Adj c q))
    (hclean : ∀ x : Fin n → Bool, productValue A B x = true → productValue C D x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    (hup : ¬ CleanMask G A B u) (huq : ¬ CleanMask G C D u)
    (hvp : ¬ CleanMask G A B v) (hvq : ¬ CleanMask G C D v) :
    (p ∈ A ∧ q ∈ D) ∨ (p ∈ B ∧ q ∈ C) := by
  have huA := (Finset.mem_inter.mp hu).1
  have huC := (Finset.mem_inter.mp hu).2
  have hvB := (Finset.mem_inter.mp hv).1
  have hvD := (Finset.mem_inter.mp hv).2
  rcases hp with ⟨hpA, hp⟩ | ⟨hpB, hp⟩ <;> rcases hq with ⟨hqC, hq⟩ | ⟨hqD, hq⟩
  · exact (same_orientation_clean_mask G color hcolor A B C D u v p q
      huA huC hvB hvD hp hq hclean).elim (fun h => (hup h).elim) (fun h => (huq h).elim)
  · exact Or.inl ⟨hpA, hqD⟩
  · exact Or.inr ⟨hpB, hqC⟩
  · have hclean' : ∀ x : Fin n → Bool, productValue B A x = true → productValue D C x = true →
        ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      intro x h1 h2
      apply hclean x
      · simpa only [productValue, Bool.and_comm] using h1
      · simpa only [productValue, Bool.and_comm] using h2
    have h := same_orientation_clean_mask G color hcolor B A D C v u p q
      hvB hvD huA huC (fun a ha => (hp a ha).symm) (fun c hc => (hq c hc).symm) hclean'
    rcases h with h | h
    · apply False.elim
      apply hvp
      simpa only [CleanMask, productValue, Bool.and_comm] using h
    · apply False.elim
      apply hvq
      simpa only [CleanMask, productValue, Bool.and_comm] using h

end PEqualNP.Outside.L_meta_1477.JointCentersStar
