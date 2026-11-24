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

namespace PEqualNP.Outside.L_meta_1477.ProductJointCover

open PEqualNP.TopForm PEqualNP.EdgeOwnership Structural StructuralMasks MaskGrouping JointCentersStar

lemma pair_cross {n : ℕ} (A B : Finset (Fin n)) (hdis : Disjoint A B) (u v : Fin n)
    (hf : productValue A B (pairInput u v) = true) :
    (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B) := by
  simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq] at hf
  obtain ⟨a,ha,hav⟩ := hf.1
  obtain ⟨b,hb,hbv⟩ := hf.2
  simp only [pairInput,decide_eq_true_eq] at hav hbv
  rcases hav with rfl | rfl <;> rcases hbv with rfl | rfl
  · exact ((Finset.disjoint_left.mp hdis ha) hb).elim
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · exact ((Finset.disjoint_left.mp hdis ha) hb).elim

lemma pair_true_of_cross {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n)
    (hp : (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B)) :
    productValue A B (pairInput u v) = true := by
  simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq]
  rcases hp with h | h
  · exact ⟨⟨u,h.1,by simp [pairInput]⟩,⟨v,h.2,by simp [pairInput]⟩⟩
  · exact ⟨⟨v,h.1,by simp [pairInput]⟩,⟨u,h.2,by simp [pairInput]⟩⟩

lemma pair_mem_joint {n : ℕ} (A B C D : Finset (Fin n)) (u v : Fin n)
    (hAB : (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B))
    (hCD : (u ∈ C ∧ v ∈ D) ∨ (v ∈ C ∧ u ∈ D)) :
    s(u,v) ∈ jointEdges A B C D := by
  have first (x y : Fin n) (hxA : x ∈ A) (hxC : x ∈ C) (hyB : y ∈ B) (hyD : y ∈ D) :
      s(x,y) ∈ jointEdges A B C D := Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨hxA,hxC⟩,Finset.mem_inter.mpr ⟨hyB,hyD⟩⟩,rfl⟩)
  have second (x y : Fin n) (hxA : x ∈ A) (hxD : x ∈ D) (hyB : y ∈ B) (hyC : y ∈ C) :
      s(x,y) ∈ jointEdges A B C D := Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨hxA,hxD⟩,Finset.mem_inter.mpr ⟨hyB,hyC⟩⟩,rfl⟩)
  rcases hAB with hAB | hAB <;> rcases hCD with hCD | hCD
  · exact first u v hAB.1 hCD.1 hAB.2 hCD.2
  · exact second u v hAB.1 hCD.2 hAB.2 hCD.1
  · have he : s(v,u) = s(u,v) := Sym2.eq_swap
    exact he ▸ second v u hAB.1 hCD.2 hAB.2 hCD.1
  · have he : s(v,u) = s(u,v) := Sym2.eq_swap
    exact he ▸ first v u hAB.1 hCD.1 hAB.2 hCD.2

lemma product_joint_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Bool)
    (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hcAB : (cleanCenters G A B).Nonempty) (hcCD : (cleanCenters G C D).Nonempty)
    (hclean : ∀ u v : Fin n, productValue A B (pairInput u v) = true →
      productValue C D (pairInput u v) = true → G.Adj u v) :
    ∃ J : Finset (Fin n), J.card ≤ 1 ∧ ∀ u v : Fin n,
      productValue A B (pairInput u v) = true → productValue C D (pairInput u v) = true →
        ∃ c ∈ J, c ∈ s(u,v) := by
  have side_center (X Y : Finset (Fin n)) (hc : (cleanCenters G X Y).Nonempty) : SideCenter G X Y := by
    obtain ⟨c,hc⟩ := hc
    simp only [cleanCenters,Finset.mem_union,Finset.mem_filter] at hc
    rcases hc with ⟨_,hc⟩ | ⟨_,hc⟩
    · exact Or.inl ⟨c,hc⟩
    · exact Or.inr ⟨c,hc⟩
  have hgraph : ∀ e ∈ jointEdges A B C D, e ∈ G.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
      obtain ⟨huA,huC⟩ := Finset.mem_inter.mp hu
      obtain ⟨hvB,hvD⟩ := Finset.mem_inter.mp hv
      exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr
        (hclean p.1 p.2 (pair_true_of_cross A B _ _ (Or.inl ⟨huA,hvB⟩))
          (pair_true_of_cross C D _ _ (Or.inl ⟨huC,hvD⟩))))
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
      obtain ⟨huA,huD⟩ := Finset.mem_inter.mp hu
      obtain ⟨hvB,hvC⟩ := Finset.mem_inter.mp hv
      exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr
        (hclean p.1 p.2 (pair_true_of_cross A B _ _ (Or.inl ⟨huA,hvB⟩))
          (pair_true_of_cross C D _ _ (Or.inr ⟨hvC,huD⟩))))
  obtain ⟨J,hJ,hcov⟩ := joint_cover_one G h4 color hcolor A B C D
    (side_center A B hcAB) (side_center C D hcCD) hgraph
  refine ⟨J,hJ,?_⟩
  intro u v hfAB hfCD
  exact hcov _ (pair_mem_joint A B C D u v (pair_cross A B hAB u v hfAB) (pair_cross C D hCD u v hfCD))

end PEqualNP.Outside.L_meta_1477.ProductJointCover

namespace PEqualNP.Outside.L_meta_1477.TwoCentersValidPair

open PEqualNP.TopForm PEqualNP.EdgeOwnership Structural StructuralMasks MaskGrouping

lemma two_centers_cover_valid_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (htwo : (cleanCenters G A B).card = 2)
    (u v : Fin n) (hp : productValue A B (pairInput u v) = true) (huv : G.Adj u v) :
    u ∈ cleanCenters G A B ∨ v ∈ cleanCenters G A B := by
  classical
  obtain ⟨p,hpC,q,hqC,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (cleanCenters G A B).card)
  have hsides : ∃ p ∈ cleanCenters G A B, ∃ q ∈ cleanCenters G A B, p ∈ A ∧ q ∈ B := by
    rcases different_centers_cross G h4 A B hA hB p q hpC hqC hpq with h | h
    · exact ⟨p,hpC,q,hqC,h⟩
    · exact ⟨q,hqC,p,hpC,h.2,h.1⟩
  obtain ⟨p,hpC,q,hqC,hpA,hqB⟩ := hsides
  have hpclean := (mem_centers_iff G A B p).mp hpC |>.2
  have hqclean := (mem_centers_iff G A B q).mp hqC |>.2
  have hpall := (cleanMask_of_mem_left_iff G A B p hpA).mp hpclean
  have hqall := (cleanMask_of_mem_right_iff G A B q hqB).mp hqclean
  have cover (x y : Fin n) (hx : x ∈ A) (hy : y ∈ B) (hxy : G.Adj x y) :
      x ∈ cleanCenters G A B ∨ y ∈ cleanCenters G A B := by
    by_contra hn
    have hn := not_or.mp hn
    have hxp : x ≠ p := by intro h; subst x; exact hn.1 hpC
    have hqy : q ≠ y := by intro h; subst y; exact hn.2 hqC
    have hsub : ({q,y} : Finset (Fin n)) ⊆ Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj p z) := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqall x hx,hpall _ hqB⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy,hpall _ hy⟩
    have hc := (Finset.card_le_card hsub).trans (h4 x p hxp)
    have hs : ({q,y} : Finset (Fin n)).card = 2 := by simp [hqy]
    omega
  rcases ProductJointCover.pair_cross A B hdis u v hp with h | h
  · exact cover u v h.1 h.2 huv
  · exact (cover v u h.1 h.2 huv.symm).symm

end PEqualNP.Outside.L_meta_1477.TwoCentersValidPair
