import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.JointCellAccounting

def crossEdges {α : Type*} [DecidableEq α] (X Y : Finset α) : Finset (Sym2 α) :=
  (X ×ˢ Y).image (fun p => s(p.1, p.2))

lemma crossEdges_card {α : Type*} [DecidableEq α] (X Y : Finset α)
    (hXY : Disjoint X Y) : (crossEdges X Y).card = X.card * Y.card := by
  rw [crossEdges, Finset.card_image_iff.mpr]
  · exact Finset.card_product X Y
  · intro p hp q hq he
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · have hpX := (Finset.mem_product.mp hp).1
      have hqY := (Finset.mem_product.mp hq).2
      exact (Finset.disjoint_left.mp hXY hpX (h.1 ▸ hqY)).elim

lemma crossEdges_disjoint {α : Type*} [DecidableEq α] (X Y Z W : Finset α)
    (hXZ : Disjoint X Z) (hXW : Disjoint X W) :
    Disjoint (crossEdges X Y) (crossEdges Z W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hf
  have hpX := (Finset.mem_product.mp hp).1
  obtain ⟨hqZ, hqW⟩ := Finset.mem_product.mp hq
  rcases Sym2.eq_iff.mp heq with h | h
  · exact Finset.disjoint_left.mp hXZ hpX (h.1 ▸ hqZ)
  · exact Finset.disjoint_left.mp hXW hpX (h.2 ▸ hqW)

lemma positive_pair_budget (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a + b ≤ a * b + 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [Nat.succ_mul, Nat.mul_succ]
  omega

lemma pair_cell_budget (a b : ℕ)
    (ha : a = 0 → b ≤ 1) (hb : b = 0 → a ≤ 1) :
    a + b + min 1 (a * b) ≤ a * b + min 1 a + min 1 b := by
  by_cases ha0 : a = 0
  · have hh := ha ha0
    simp only [ha0, zero_add, zero_mul, min_zero, add_zero]
    omega
  by_cases hb0 : b = 0
  · have hh := hb hb0
    simp only [hb0, add_zero, mul_zero, min_zero, zero_add]
    omega
  have hab := positive_pair_budget a b (by omega) (by omega)
  have hp : 1 ≤ a * b := Nat.mul_pos (by omega) (by omega)
  simp only [min_eq_left (show 1 ≤ a by omega), min_eq_left (show 1 ≤ b by omega),
    min_eq_left hp]
  omega

lemma four_cell_budget (a b c d : ℕ)
    (ha : a = 0 → d ≤ 1) (hd : d = 0 → a ≤ 1)
    (hb : b = 0 → c ≤ 1) (hc : c = 0 → b ≤ 1)
    (hne : 0 < a * d + b * c) :
    a + b + c + d + 1 ≤ a * d + b * c +
      (min 1 a + min 1 b + min 1 c + min 1 d) := by
  have h₁ := pair_cell_budget a d ha hd
  have h₂ := pair_cell_budget b c hb hc
  have hp : 1 ≤ min 1 (a * d) + min 1 (b * c) := by
    omega
  omega

lemma shared_cells_refund {α : Type*} [DecidableEq α]
    (X Y Z W : Finset α) (J : Finset (Sym2 α))
    (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hJ₁ : crossEdges X W ⊆ J) (hJ₂ : crossEdges Y Z ⊆ J)
    (hX : X = ∅ → W.card ≤ 1) (hW : W = ∅ → X.card ≤ 1)
    (hY : Y = ∅ → Z.card ≤ 1) (hZ : Z = ∅ → Y.card ≤ 1)
    (hne : (crossEdges X W ∪ crossEdges Y Z).Nonempty) :
    X.card + Y.card + Z.card + W.card + 1 ≤ J.card +
      (min 1 X.card + min 1 Y.card + min 1 Z.card + min 1 W.card) := by
  have hdis := crossEdges_disjoint X W Y Z hXY hXZ
  have hcard : (crossEdges X W ∪ crossEdges Y Z).card =
      X.card * W.card + Y.card * Z.card := by
    rw [Finset.card_union_of_disjoint hdis, crossEdges_card X W hXW,
      crossEdges_card Y Z hYZ]
  have hprod := Finset.card_le_card (Finset.union_subset hJ₁ hJ₂)
  rw [hcard] at hprod
  have hpos := Finset.card_pos.mpr hne
  rw [hcard] at hpos
  have hsum := four_cell_budget X.card Y.card Z.card W.card
    (fun h => hX (Finset.card_eq_zero.mp h)) (fun h => hW (Finset.card_eq_zero.mp h))
    (fun h => hY (Finset.card_eq_zero.mp h)) (fun h => hZ (Finset.card_eq_zero.mp h)) hpos
  omega

lemma union_budget {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E₁ E₂ : Finset α) (V₁ V₂ N : Finset β) (r : ℕ)
    (h₁ : E₁.card + 1 ≤ V₁.card) (h₂ : E₂.card + 1 ≤ V₂.card)
    (hsub : V₁ ∪ V₂ ⊆ N)
    (hrefund : (V₁ ∩ V₂).card + 1 ≤ (E₁ ∩ E₂).card + r) :
    (E₁ ∪ E₂).card + 3 ≤ N.card + r := by
  have he := Finset.card_union_add_card_inter E₁ E₂
  have hv := Finset.card_union_add_card_inter V₁ V₂
  have hn := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1477.JointCellAccounting

namespace PEqualNP.Outside.L_meta_1477.JointCellAccounting

lemma crossEdges_mono {α : Type*} [DecidableEq α] {X Y X' Y' : Finset α}
    (hX : X ⊆ X') (hY : Y ⊆ Y') : crossEdges X Y ⊆ crossEdges X' Y' := by
  apply Finset.image_subset_image
  exact Finset.product_subset_product hX hY

lemma crossEdges_active {α : Type*} [DecidableEq α]
    (V X Y : Finset α) (J : Finset (Sym2 α)) (hJ : crossEdges X Y ⊆ J)
    (hincident : ∀ u v, s(u, v) ∈ J → u ∈ V ∧ v ∈ V) :
    crossEdges (V ∩ X) (V ∩ Y) = crossEdges X Y := by
  apply Finset.Subset.antisymm (crossEdges_mono Finset.inter_subset_right Finset.inter_subset_right)
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hpX, hpY⟩ := Finset.mem_product.mp hp
  have hv := hincident p.1 p.2 (hJ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr
    ⟨Finset.mem_inter.mpr ⟨hv.1, hpX⟩, Finset.mem_inter.mpr ⟨hv.2, hpY⟩⟩, rfl⟩

lemma active_opposite_empty {α : Type*} [DecidableEq α]
    (V X Y : Finset α) (J : Finset (Sym2 α)) (hJ : crossEdges X Y ⊆ J)
    (hincident : ∀ u v, s(u, v) ∈ J → u ∈ V ∧ v ∈ V)
    (hsmall : Y = ∅ → (V ∩ X).card ≤ 1) (hempty : V ∩ Y = ∅) :
    (V ∩ X).card ≤ 1 := by
  by_cases hY : Y = ∅
  · exact hsmall hY
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hY
  have he : V ∩ X = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxX := (Finset.mem_inter.mp hx).2
    have hpair : s(x, y) ∈ J := hJ (Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨hxX, hy⟩, rfl⟩)
    have hyV := (hincident x y hpair).2
    have hyI : y ∈ V ∩ Y := Finset.mem_inter.mpr ⟨hyV, hy⟩
    rw [hempty] at hyI
    exact Finset.notMem_empty y hyI
  simp [he]

lemma crossEdges_comm {α : Type*} [DecidableEq α] (X Y : Finset α) :
    crossEdges X Y = crossEdges Y X := by
  ext e
  simp only [crossEdges, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨(y, x), ⟨hy, hx⟩, Sym2.eq_swap⟩
  · rintro ⟨⟨y, x⟩, ⟨hy, hx⟩, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, Sym2.eq_swap⟩

lemma four_disjoint_card {α : Type*} [DecidableEq α] (X Y Z W : Finset α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W)
    (hYZ : Disjoint Y Z) (hYW : Disjoint Y W) (hZW : Disjoint Z W) :
    (X ∪ Y ∪ Z ∪ W).card = X.card + Y.card + Z.card + W.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hXW, hYW⟩, hZW⟩)]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩)]
  rw [Finset.card_union_of_disjoint hXY]

lemma cell_partition_refund {α : Type*} [DecidableEq α]
    (V X Y Z W : Finset α) (J : Finset (Sym2 α))
    (hpart : V ⊆ X ∪ Y ∪ Z ∪ W)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W)
    (hYZ : Disjoint Y Z) (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hJ₁ : crossEdges X W ⊆ J) (hJ₂ : crossEdges Y Z ⊆ J)
    (hincident : ∀ u v, s(u, v) ∈ J → u ∈ V ∧ v ∈ V)
    (hX : X = ∅ → (V ∩ W).card ≤ 1) (hW : W = ∅ → (V ∩ X).card ≤ 1)
    (hY : Y = ∅ → (V ∩ Z).card ≤ 1) (hZ : Z = ∅ → (V ∩ Y).card ≤ 1)
    (hne : (crossEdges X W ∪ crossEdges Y Z).Nonempty) :
    V.card + 1 ≤ J.card +
      (min 1 X.card + min 1 Y.card + min 1 Z.card + min 1 W.card) := by
  have hdis {S T : Finset α} (h : Disjoint S T) : Disjoint (V ∩ S) (V ∩ T) :=
    h.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsame : V = V ∩ X ∪ V ∩ Y ∪ V ∩ Z ∪ V ∩ W := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv
      have hvpart := hpart hv
      simp only [Finset.mem_union] at hvpart
      tauto
    · tauto
  have hcard : V.card = (V ∩ X).card + (V ∩ Y).card + (V ∩ Z).card + (V ∩ W).card := by
    conv_lhs => rw [hsame]
    exact four_disjoint_card _ _ _ _ (hdis hXY) (hdis hXZ) (hdis hXW)
      (hdis hYZ) (hdis hYW) (hdis hZW)
  have hJ₁' : crossEdges W X ⊆ J := by simpa only [crossEdges_comm W X] using hJ₁
  have hJ₂' : crossEdges Z Y ⊆ J := by simpa only [crossEdges_comm Z Y] using hJ₂
  have hsum := shared_cells_refund (V ∩ X) (V ∩ Y) (V ∩ Z) (V ∩ W) J
    (hdis hXW) (hdis hYZ) (hdis hXY) (hdis hXZ)
    ((crossEdges_mono Finset.inter_subset_right Finset.inter_subset_right).trans hJ₁)
    ((crossEdges_mono Finset.inter_subset_right Finset.inter_subset_right).trans hJ₂)
    (active_opposite_empty V W X J hJ₁' hincident hX)
    (active_opposite_empty V X W J hJ₁ hincident hW)
    (active_opposite_empty V Z Y J hJ₂' hincident hY)
    (active_opposite_empty V Y Z J hJ₂ hincident hZ)
    (by simpa only [crossEdges_active V X W J hJ₁ hincident,
      crossEdges_active V Y Z J hJ₂ hincident] using hne)
  rw [← hcard] at hsum
  have hcx := Finset.card_le_card (show V ∩ X ⊆ X from Finset.inter_subset_right)
  have hcy := Finset.card_le_card (show V ∩ Y ⊆ Y from Finset.inter_subset_right)
  have hcz := Finset.card_le_card (show V ∩ Z ⊆ Z from Finset.inter_subset_right)
  have hcw := Finset.card_le_card (show V ∩ W ⊆ W from Finset.inter_subset_right)
  omega

end PEqualNP.Outside.L_meta_1477.JointCellAccounting


namespace PEqualNP.Outside.L_meta_1477.UnpairedCell

open PEqualNP.TopForm

def Universal {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ w ∈ S, G.Adj v w

open Classical in
lemma common_active_cell_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hB : B.Nonempty) (hD : D.Nonempty) (hBD : Disjoint B D) :
    ((A ∩ C).filter (fun v =>
      (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
      (Universal G D v ∨ ∃ d ∈ D, Universal G C d))).card ≤ 1 := by
  classical
  let X := (A ∩ C).filter (fun v =>
    (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
    (Universal G D v ∨ ∃ d ∈ D, Universal G C d))
  change X.card ≤ 1
  have left_center : ∃ b ∈ B, ∀ v ∈ X, G.Adj b v := by
    by_cases hb : ∃ b ∈ B, Universal G A b
    · obtain ⟨b, hbB, hbA⟩ := hb
      exact ⟨b, hbB, fun v hv => hbA v (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).1⟩
    · obtain ⟨b, hbB⟩ := hB
      refine ⟨b, hbB, ?_⟩
      intro v hv
      exact (((Finset.mem_filter.mp hv).2.1.resolve_right hb) b hbB).symm
  have right_center : ∃ d ∈ D, ∀ v ∈ X, G.Adj d v := by
    by_cases hd : ∃ d ∈ D, Universal G C d
    · obtain ⟨d, hdD, hdC⟩ := hd
      exact ⟨d, hdD, fun v hv => hdC v (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).2⟩
    · obtain ⟨d, hdD⟩ := hD
      refine ⟨d, hdD, ?_⟩
      intro v hv
      exact (((Finset.mem_filter.mp hv).2.2.resolve_right hd) d hdD).symm
  obtain ⟨b, hbB, hbX⟩ := left_center
  obtain ⟨d, hdD, hdX⟩ := right_center
  have hbd : b ≠ d := by
    intro he
    exact Finset.disjoint_left.mp hBD hbB (he.symm ▸ hdD)
  have hsub : X ⊆ Finset.univ.filter (fun v => G.Adj b v ∧ G.Adj d v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbX v hv, hdX v hv⟩
  exact (Finset.card_le_card hsub).trans (hG b d hbd)

end PEqualNP.Outside.L_meta_1477.UnpairedCell


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

namespace PEqualNP.Outside.L_meta_1477.JointUnion

open PEqualNP.TopForm MaskJointForest JointCellAccounting UnpairedCell

def pairEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  undirected (maskJointEdges G A B C D)

def jointEdges {n : ℕ} (A B C D : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  crossEdges (A ∩ C) (B ∩ D) ∪ crossEdges (A ∩ D) (B ∩ C)

lemma mem_undirected {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) :
    s(u, v) ∈ undirected E ↔ (u, v) ∈ E ∨ (v, u) ∈ E := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp h
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hab
    · exact Or.inr hab
  · rintro (h | h)
    · exact Finset.mem_image.mpr ⟨(u, v), h, rfl⟩
    · exact Finset.mem_image.mpr ⟨(v, u), h, Sym2.eq_swap⟩

lemma mem_active {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) :
    v ∈ active E ↔ ∃ w, s(v, w) ∈ E := by
  constructor
  · intro h
    obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hv)
    exact ⟨w, he⟩
  · rintro ⟨w, hw⟩
    exact Finset.mem_biUnion.mpr ⟨s(v, w), hw, by simp⟩

lemma mem_crossEdges {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n) :
    s(u, v) ∈ crossEdges A B ↔ (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B) := by
  change s(u, v) ∈ undirected (A ×ˢ B) ↔ _
  rw [mem_undirected]
  simp only [Finset.mem_product]

lemma pairEdges_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : pairEdges G A B C D ⊆ crossEdges A B := by
  exact Finset.image_subset_image (Finset.filter_subset _ _)

lemma active_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : active (pairEdges G A B C D) ⊆ A ∪ B := by
  intro v hv
  obtain ⟨w, hw⟩ := (mem_active _ _).mp hv
  rcases (mem_crossEdges A B v w).mp (pairEdges_support G A B C D hw) with h | h
  · exact Finset.mem_union_left _ h.1
  · exact Finset.mem_union_right _ h.2

lemma joint_subset_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : jointEdges A B C D ⊆ pairEdges G A B C D := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨haA, haC⟩, ⟨hbB, hbD⟩⟩ :=
      And.intro (Finset.mem_inter.mp (Finset.mem_product.mp hab).1)
        (Finset.mem_inter.mp (Finset.mem_product.mp hab).2)
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haA, hbB⟩, Or.inr (Or.inr ⟨Or.inl haC, Or.inr hbD⟩)⟩, rfl⟩
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨haA, haD⟩, ⟨hbB, hbC⟩⟩ :=
      And.intro (Finset.mem_inter.mp (Finset.mem_product.mp hab).1)
        (Finset.mem_inter.mp (Finset.mem_product.mp hab).2)
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haA, hbB⟩, Or.inr (Or.inr ⟨Or.inr hbC, Or.inl haD⟩)⟩, rfl⟩

lemma joint_comm {n : ℕ} (A B C D : Finset (Fin n)) :
    jointEdges A B C D = jointEdges C D A B := by
  simp only [jointEdges, Finset.inter_comm]
  rw [crossEdges_comm (A ∩ D) (B ∩ C)]

lemma crossEdges_inter {n : ℕ} (A B C D : Finset (Fin n)) :
    crossEdges A B ∩ crossEdges C D = jointEdges A B C D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [jointEdges, Finset.mem_inter, Finset.mem_union, mem_crossEdges]
    tauto

lemma pairEdges_inter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) :
    pairEdges G A B C D ∩ pairEdges G C D A B = jointEdges A B C D := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [← crossEdges_inter]
    exact Finset.mem_inter.mpr
      ⟨pairEdges_support G A B C D (Finset.mem_inter.mp he).1,
        pairEdges_support G C D A B (Finset.mem_inter.mp he).2⟩
  · intro e he
    exact Finset.mem_inter.mpr ⟨joint_subset_left G A B C D he,
      joint_subset_left G C D A B (joint_comm A B C D ▸ he)⟩

lemma active_unpaired {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hBD : B ∩ D = ∅) (v : Fin n) (hvA : v ∈ A) (hvC : v ∈ C)
    (hv : v ∈ active (pairEdges G A B C D)) :
    Universal G B v ∨ ∃ b ∈ B, Universal G A b := by
  obtain ⟨w, hw⟩ := (mem_active _ _).mp hv
  rcases (mem_undirected _ v w).mp hw with hw | hw
  · obtain ⟨hvw, hmask | hmask | ⟨hC, hD⟩⟩ := Finset.mem_filter.mp hw
    · exact Or.inl hmask
    · exact Or.inr ⟨w, (Finset.mem_product.mp hvw).2, hmask⟩
    · rcases hD with hvD | hwD
      · exact (Finset.disjoint_left.mp hCD hvC hvD).elim
      · have hwBD : w ∈ B ∩ D := Finset.mem_inter.mpr
          ⟨(Finset.mem_product.mp hvw).2, hwD⟩
        rw [hBD] at hwBD
        exact (Finset.notMem_empty w hwBD).elim
  · have hvB := (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).2
    exact (Finset.disjoint_left.mp hAB hvA hvB).elim

lemma common_active_unpaired {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D) (hB : B.Nonempty) (hD : D.Nonempty)
    (hBD : B ∩ D = ∅) :
    ((active (pairEdges G A B C D) ∩ active (pairEdges G C D A B)) ∩ (A ∩ C)).card ≤ 1 := by
  classical
  have hsmall := common_active_cell_small G hG A B C D hB hD
    (Finset.disjoint_iff_inter_eq_empty.mpr hBD)
  apply (Finset.card_le_card ?_).trans hsmall
  intro v hv
  obtain ⟨⟨hv₁, hv₂⟩, ⟨hvA, hvC⟩⟩ :=
    And.intro (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1)
      (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hvA, hvC⟩,
    active_unpaired G A B C D hAB hCD hBD v hvA hvC hv₁,
    active_unpaired G C D A B hCD hAB (by simpa only [Finset.inter_comm] using hBD) v hvC hvA hv₂⟩

end PEqualNP.Outside.L_meta_1477.JointUnion

namespace PEqualNP.Outside.L_meta_1477.JointUnion

open PEqualNP.TopForm MaskJointForest JointCellAccounting UnpairedCell

lemma pairEdges_swap_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : pairEdges G B A C D = pairEdges G A B C D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [pairEdges, mem_undirected, maskJointEdges, Finset.mem_filter, Finset.mem_product]
    tauto

lemma pairEdges_swap_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : pairEdges G A B D C = pairEdges G A B C D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [pairEdges, mem_undirected, maskJointEdges, Finset.mem_filter, Finset.mem_product]
    tauto

lemma active_inter_refund {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (hD : D.Nonempty)
    (hJ : (jointEdges A B C D).Nonempty) :
    (active (pairEdges G A B C D) ∩ active (pairEdges G C D A B)).card + 1 ≤
      (jointEdges A B C D).card +
        (min 1 (A ∩ C).card + min 1 (A ∩ D).card + min 1 (B ∩ C).card + min 1 (B ∩ D).card) := by
  classical
  let V := active (pairEdges G A B C D) ∩ active (pairEdges G C D A B)
  have hdis {S T X Y : Finset (Fin n)} (h : Disjoint S T) : Disjoint (S ∩ X) (T ∩ Y) :=
    h.mono Finset.inter_subset_left Finset.inter_subset_left
  have hdis' {S T X Y : Finset (Fin n)} (h : Disjoint S T) : Disjoint (X ∩ S) (Y ∩ T) :=
    h.mono Finset.inter_subset_right Finset.inter_subset_right
  apply cell_partition_refund V (A ∩ C) (A ∩ D) (B ∩ C) (B ∩ D) (jointEdges A B C D)
  · intro v hv
    have hv₁ := active_support G A B C D (Finset.mem_inter.mp hv).1
    have hv₂ := active_support G C D A B (Finset.mem_inter.mp hv).2
    simp only [Finset.mem_union, Finset.mem_inter] at hv₁ hv₂ ⊢
    tauto
  · exact hdis' hCD
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis' hCD
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right
  · intro u v huv
    have hu₁ := joint_subset_left G A B C D huv
    have hu₂ := joint_subset_left G C D A B (joint_comm A B C D ▸ huv)
    have hv₁ : s(v, u) ∈ pairEdges G A B C D := by simpa only [Sym2.eq_swap] using hu₁
    have hv₂ : s(v, u) ∈ pairEdges G C D A B := by simpa only [Sym2.eq_swap] using hu₂
    exact ⟨Finset.mem_inter.mpr ⟨(mem_active _ _).mpr ⟨v, hu₁⟩, (mem_active _ _).mpr ⟨v, hu₂⟩⟩,
      Finset.mem_inter.mpr ⟨(mem_active _ _).mpr ⟨u, hv₁⟩, (mem_active _ _).mpr ⟨u, hv₂⟩⟩⟩
  · intro hAC
    have h := common_active_unpaired G hG B A D C hAB.symm hCD.symm hA hC hAC
    simpa only [V, pairEdges_swap_left G A B D C, pairEdges_swap_right G A B C D,
      pairEdges_swap_left G C D B A, pairEdges_swap_right G C D A B] using h
  · exact common_active_unpaired G hG A B C D hAB hCD hB hD
  · intro hAD
    have h := common_active_unpaired G hG B A C D hAB.symm hCD hA hD hAD
    simpa only [V, pairEdges_swap_left G A B C D, pairEdges_swap_right G C D A B] using h
  · intro hBC
    have h := common_active_unpaired G hG A B D C hAB hCD.symm hB hC hBC
    simpa only [V, pairEdges_swap_right G A B C D, pairEdges_swap_left G C D A B] using h
  · exact hJ

lemma union_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (hD : D.Nonempty)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b)
    (hJ : (jointEdges A B C D).Nonempty) :
    (pairEdges G A B C D ∪ pairEdges G C D A B).card + 3 ≤
      (A ∪ B ∪ C ∪ D).card +
        (min 1 (A ∩ C).card + min 1 (A ∩ D).card + min 1 (B ∩ C).card + min 1 (B ∩ D).card) := by
  have hN₁ : (pairEdges G A B C D).Nonempty := hJ.mono (joint_subset_left G A B C D)
  have hN₂ : (pairEdges G C D A B).Nonempty := by
    rw [joint_comm A B C D] at hJ
    exact hJ.mono (joint_subset_left G C D A B)
  have h₁ := undirected_maskJoint_bound G hG A B C D hAB hCD hjoint hN₁
  have hjoint' : ∀ c ∈ C, ∀ d ∈ D,
      (c ∈ A ∨ d ∈ A) → (c ∈ B ∨ d ∈ B) → G.Adj c d := by
    intro c hc d hd hca hcb
    rcases hca with hcA | hdA <;> rcases hcb with hcB | hdB
    · exact (Finset.disjoint_left.mp hAB hcA hcB).elim
    · exact hjoint c hcA d hdB (Or.inl hc) (Or.inr hd)
    · exact (hjoint d hdA c hcB (Or.inr hc) (Or.inl hd)).symm
    · exact (Finset.disjoint_left.mp hAB hdA hdB).elim
  have h₂ := undirected_maskJoint_bound G hG C D A B hCD hAB hjoint' hN₂
  have hrefund := active_inter_refund G hG A B C D hAB hCD hA hB hC hD hJ
  rw [← pairEdges_inter G A B C D] at hrefund
  apply union_budget _ _ _ _ (A ∪ B ∪ C ∪ D) _ h₁ h₂ ?_ hrefund
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have h := active_support G A B C D hv
    simp only [Finset.mem_union] at h ⊢
    tauto
  · have h := active_support G C D A B hv
    simp only [Finset.mem_union] at h ⊢
    tauto

end PEqualNP.Outside.L_meta_1477.JointUnion

namespace PEqualNP.Outside.L_meta_1477.JointCellAccounting

lemma shared_cells_refund_weak {α : Type*} [DecidableEq α]
    (X Y Z W : Finset α) (J : Finset (Sym2 α))
    (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hJ₁ : crossEdges X W ⊆ J) (hJ₂ : crossEdges Y Z ⊆ J)
    (hX : X = ∅ → W.card ≤ 1) (hW : W = ∅ → X.card ≤ 1)
    (hY : Y = ∅ → Z.card ≤ 1) (hZ : Z = ∅ → Y.card ≤ 1)
    :
    X.card + Y.card + Z.card + W.card ≤ J.card +
      (min 1 X.card + min 1 Y.card + min 1 Z.card + min 1 W.card) := by
  have hdis := crossEdges_disjoint X W Y Z hXY hXZ
  have hcard : (crossEdges X W ∪ crossEdges Y Z).card =
      X.card * W.card + Y.card * Z.card := by
    rw [Finset.card_union_of_disjoint hdis, crossEdges_card X W hXW,
      crossEdges_card Y Z hYZ]
  have hprod := Finset.card_le_card (Finset.union_subset hJ₁ hJ₂)
  rw [hcard] at hprod
  have h₁ := pair_cell_budget X.card W.card
    (fun h => hX (Finset.card_eq_zero.mp h)) (fun h => hW (Finset.card_eq_zero.mp h))
  have h₂ := pair_cell_budget Y.card Z.card
    (fun h => hY (Finset.card_eq_zero.mp h)) (fun h => hZ (Finset.card_eq_zero.mp h))
  omega

lemma cell_partition_refund_weak {α : Type*} [DecidableEq α]
    (V X Y Z W : Finset α) (J : Finset (Sym2 α))
    (hpart : V ⊆ X ∪ Y ∪ Z ∪ W)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W)
    (hYZ : Disjoint Y Z) (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hJ₁ : crossEdges X W ⊆ J) (hJ₂ : crossEdges Y Z ⊆ J)
    (hincident : ∀ u v, s(u, v) ∈ J → u ∈ V ∧ v ∈ V)
    (hX : X = ∅ → (V ∩ W).card ≤ 1) (hW : W = ∅ → (V ∩ X).card ≤ 1)
    (hY : Y = ∅ → (V ∩ Z).card ≤ 1) (hZ : Z = ∅ → (V ∩ Y).card ≤ 1)
    :
    V.card ≤ J.card +
      (min 1 X.card + min 1 Y.card + min 1 Z.card + min 1 W.card) := by
  have hdis {S T : Finset α} (h : Disjoint S T) : Disjoint (V ∩ S) (V ∩ T) :=
    h.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsame : V = V ∩ X ∪ V ∩ Y ∪ V ∩ Z ∪ V ∩ W := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv
      have hvpart := hpart hv
      simp only [Finset.mem_union] at hvpart
      tauto
    · tauto
  have hcard : V.card = (V ∩ X).card + (V ∩ Y).card + (V ∩ Z).card + (V ∩ W).card := by
    conv_lhs => rw [hsame]
    exact four_disjoint_card _ _ _ _ (hdis hXY) (hdis hXZ) (hdis hXW)
      (hdis hYZ) (hdis hYW) (hdis hZW)
  have hJ₁' : crossEdges W X ⊆ J := by simpa only [crossEdges_comm W X] using hJ₁
  have hJ₂' : crossEdges Z Y ⊆ J := by simpa only [crossEdges_comm Z Y] using hJ₂
  have hsum := shared_cells_refund_weak (V ∩ X) (V ∩ Y) (V ∩ Z) (V ∩ W) J
    (hdis hXW) (hdis hYZ) (hdis hXY) (hdis hXZ)
    ((crossEdges_mono Finset.inter_subset_right Finset.inter_subset_right).trans hJ₁)
    ((crossEdges_mono Finset.inter_subset_right Finset.inter_subset_right).trans hJ₂)
    (active_opposite_empty V W X J hJ₁' hincident hX)
    (active_opposite_empty V X W J hJ₁ hincident hW)
    (active_opposite_empty V Z Y J hJ₂' hincident hY)
    (active_opposite_empty V Y Z J hJ₂ hincident hZ)
  rw [← hcard] at hsum
  have hcx := Finset.card_le_card (show V ∩ X ⊆ X from Finset.inter_subset_right)
  have hcy := Finset.card_le_card (show V ∩ Y ⊆ Y from Finset.inter_subset_right)
  have hcz := Finset.card_le_card (show V ∩ Z ⊆ Z from Finset.inter_subset_right)
  have hcw := Finset.card_le_card (show V ∩ W ⊆ W from Finset.inter_subset_right)
  omega

end PEqualNP.Outside.L_meta_1477.JointCellAccounting

namespace PEqualNP.Outside.L_meta_1477.JointUnion

open PEqualNP.TopForm MaskJointForest JointCellAccounting UnpairedCell

lemma active_inter_refund_weak {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (hD : D.Nonempty)
    :
    (active (pairEdges G A B C D) ∩ active (pairEdges G C D A B)).card ≤
      (jointEdges A B C D).card +
        (min 1 (A ∩ C).card + min 1 (A ∩ D).card + min 1 (B ∩ C).card + min 1 (B ∩ D).card) := by
  classical
  let V := active (pairEdges G A B C D) ∩ active (pairEdges G C D A B)
  have hdis {S T X Y : Finset (Fin n)} (h : Disjoint S T) : Disjoint (S ∩ X) (T ∩ Y) :=
    h.mono Finset.inter_subset_left Finset.inter_subset_left
  have hdis' {S T X Y : Finset (Fin n)} (h : Disjoint S T) : Disjoint (X ∩ S) (Y ∩ T) :=
    h.mono Finset.inter_subset_right Finset.inter_subset_right
  apply cell_partition_refund_weak V (A ∩ C) (A ∩ D) (B ∩ C) (B ∩ D) (jointEdges A B C D)
  · intro v hv
    have hv₁ := active_support G A B C D (Finset.mem_inter.mp hv).1
    have hv₂ := active_support G C D A B (Finset.mem_inter.mp hv).2
    simp only [Finset.mem_union, Finset.mem_inter] at hv₁ hv₂ ⊢
    tauto
  · exact hdis' hCD
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis hAB
  · exact hdis' hCD
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right
  · intro u v huv
    have hu₁ := joint_subset_left G A B C D huv
    have hu₂ := joint_subset_left G C D A B (joint_comm A B C D ▸ huv)
    have hv₁ : s(v, u) ∈ pairEdges G A B C D := by simpa only [Sym2.eq_swap] using hu₁
    have hv₂ : s(v, u) ∈ pairEdges G C D A B := by simpa only [Sym2.eq_swap] using hu₂
    exact ⟨Finset.mem_inter.mpr ⟨(mem_active _ _).mpr ⟨v, hu₁⟩, (mem_active _ _).mpr ⟨v, hu₂⟩⟩,
      Finset.mem_inter.mpr ⟨(mem_active _ _).mpr ⟨u, hv₁⟩, (mem_active _ _).mpr ⟨u, hv₂⟩⟩⟩
  · intro hAC
    have h := common_active_unpaired G hG B A D C hAB.symm hCD.symm hA hC hAC
    simpa only [V, pairEdges_swap_left G A B D C, pairEdges_swap_right G A B C D,
      pairEdges_swap_left G C D B A, pairEdges_swap_right G C D A B] using h
  · exact common_active_unpaired G hG A B C D hAB hCD hB hD
  · intro hAD
    have h := common_active_unpaired G hG B A C D hAB.symm hCD hA hD hAD
    simpa only [V, pairEdges_swap_left G A B C D, pairEdges_swap_right G C D A B] using h
  · intro hBC
    have h := common_active_unpaired G hG A B D C hAB hCD.symm hB hC hBC
    simpa only [V, pairEdges_swap_right G A B C D, pairEdges_swap_left G C D A B] using h

end PEqualNP.Outside.L_meta_1477.JointUnion

namespace PEqualNP.Outside.L_meta_1477.JointUnion

open PEqualNP.TopForm MaskJointForest JointCellAccounting UnpairedCell

def cellCount {n : ℕ} (A B C D : Finset (Fin n)) : ℕ :=
  min 1 (A ∩ C).card + min 1 (A ∩ D).card + min 1 (B ∩ C).card + min 1 (B ∩ D).card

lemma overlap_count_pos {n : ℕ} (A B C D : Finset (Fin n))
    (h : ¬ Disjoint (A ∪ B) (C ∪ D)) : 1 ≤ cellCount A B C D := by
  obtain ⟨v, hv₁, hv₂⟩ := Finset.not_disjoint_iff.mp h
  rcases Finset.mem_union.mp hv₁ with ha | hb <;> rcases Finset.mem_union.mp hv₂ with hc | hd
  · have hpos := Finset.card_pos.mpr (show (A ∩ C).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨ha, hc⟩⟩)
    unfold cellCount
    omega
  · have hpos := Finset.card_pos.mpr (show (A ∩ D).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨ha, hd⟩⟩)
    unfold cellCount
    omega
  · have hpos := Finset.card_pos.mpr (show (B ∩ C).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hb, hc⟩⟩)
    unfold cellCount
    omega
  · have hpos := Finset.card_pos.mpr (show (B ∩ D).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hb, hd⟩⟩)
    unfold cellCount
    omega

lemma nonempty_extra {α : Type*} [DecidableEq α] (P Q : Finset α) (r : ℕ)
    (hP : P.Nonempty) (hr : ¬ Disjoint P Q → 1 ≤ r) :
    Q.card + 1 ≤ (P ∪ Q).card + r := by
  by_cases hdis : Disjoint P Q
  · rw [Finset.card_union_of_disjoint hdis]
    have hpos := Finset.card_pos.mpr hP
    omega
  · have hpos := hr hdis
    have hcard := Finset.card_le_card (show Q ⊆ P ∪ Q from Finset.subset_union_right)
    omega

lemma union_budget_weak {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E₁ E₂ : Finset α) (V₁ V₂ N : Finset β) (r : ℕ)
    (h₁ : E₁.card + 1 ≤ V₁.card) (h₂ : E₂.card + 1 ≤ V₂.card)
    (hsub : V₁ ∪ V₂ ⊆ N)
    (hrefund : (V₁ ∩ V₂).card ≤ (E₁ ∩ E₂).card + r) :
    (E₁ ∪ E₂).card + 2 ≤ N.card + r := by
  have he := Finset.card_union_add_card_inter E₁ E₂
  have hv := Finset.card_union_add_card_inter V₁ V₂
  have hn := Finset.card_le_card hsub
  omega

lemma union_edge_bound_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) (hD : D.Nonempty)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b) :
    (pairEdges G A B C D ∪ pairEdges G C D A B).card + 2 ≤
      (A ∪ B ∪ C ∪ D).card + cellCount A B C D := by
  have hNmin : 2 ≤ (A ∪ B ∪ C ∪ D).card := by
    have ha := Finset.card_pos.mpr hA
    have hb := Finset.card_pos.mpr hB
    have hsum := Finset.card_union_of_disjoint hAB
    have hsub : A ∪ B ⊆ A ∪ B ∪ C ∪ D := by
      intro v hv
      simp only [Finset.mem_union] at hv ⊢
      tauto
    have hc := Finset.card_le_card hsub
    omega
  have hjoint' : ∀ c ∈ C, ∀ d ∈ D,
      (c ∈ A ∨ d ∈ A) → (c ∈ B ∨ d ∈ B) → G.Adj c d := by
    intro c hc d hd hca hcb
    rcases hca with hcA | hdA <;> rcases hcb with hcB | hdB
    · exact (Finset.disjoint_left.mp hAB hcA hcB).elim
    · exact hjoint c hcA d hdB (Or.inl hc) (Or.inr hd)
    · exact (hjoint d hdA c hcB (Or.inr hc) (Or.inl hd)).symm
    · exact (Finset.disjoint_left.mp hAB hdA hdB).elim
  have hNsub : active (pairEdges G A B C D) ∪ active (pairEdges G C D A B) ⊆ A ∪ B ∪ C ∪ D := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have h := active_support G A B C D hv
      simp only [Finset.mem_union] at h ⊢
      tauto
    · have h := active_support G C D A B hv
      simp only [Finset.mem_union] at h ⊢
      tauto
  by_cases he₁ : pairEdges G A B C D = ∅
  · by_cases he₂ : pairEdges G C D A B = ∅
    · have hAN : A ⊆ A ∪ B ∪ C ∪ D := by
        intro a ha
        simp only [Finset.mem_union]
        tauto
      have hc := Finset.card_le_card hAN
      simp only [he₁, he₂, Finset.union_empty, Finset.card_empty]
      omega
    · have h₂ := undirected_maskJoint_bound G hG C D A B hCD hAB hjoint'
        (Finset.nonempty_iff_ne_empty.mpr he₂)
      have hv := Finset.card_le_card (active_support G C D A B)
      have hP : (A ∪ B).Nonempty := hA.mono
        Finset.subset_union_left
      have hextra := nonempty_extra (A ∪ B) (C ∪ D) (cellCount A B C D) hP
        (overlap_count_pos A B C D)
      have hn : (C ∪ D).card + 1 ≤ (A ∪ B ∪ C ∪ D).card + cellCount A B C D := by
        simpa only [Finset.union_assoc] using hextra
      change (pairEdges G C D A B).card + 1 ≤ (active (pairEdges G C D A B)).card at h₂
      simp only [he₁, Finset.empty_union]
      omega
  · by_cases he₂ : pairEdges G C D A B = ∅
    · have h₁ := undirected_maskJoint_bound G hG A B C D hAB hCD hjoint
        (Finset.nonempty_iff_ne_empty.mpr he₁)
      have hv := Finset.card_le_card (active_support G A B C D)
      have hP : (C ∪ D).Nonempty := hC.mono
        Finset.subset_union_left
      have hextra := nonempty_extra (C ∪ D) (A ∪ B) (cellCount A B C D) hP
        (fun h => overlap_count_pos A B C D (fun h' => h h'.symm))
      have hn : (A ∪ B).card + 1 ≤ (A ∪ B ∪ C ∪ D).card + cellCount A B C D := by
        simpa only [Finset.union_comm (C ∪ D) (A ∪ B), Finset.union_assoc] using hextra
      change (pairEdges G A B C D).card + 1 ≤ (active (pairEdges G A B C D)).card at h₁
      simp only [he₂, Finset.union_empty]
      omega
    · have h₁ := undirected_maskJoint_bound G hG A B C D hAB hCD hjoint
        (Finset.nonempty_iff_ne_empty.mpr he₁)
      have h₂ := undirected_maskJoint_bound G hG C D A B hCD hAB hjoint'
        (Finset.nonempty_iff_ne_empty.mpr he₂)
      have hrefund := active_inter_refund_weak G hG A B C D hAB hCD hA hB hC hD
      rw [← pairEdges_inter G A B C D] at hrefund
      exact union_budget_weak _ _ _ _ _ _ h₁ h₂ hNsub hrefund

end PEqualNP.Outside.L_meta_1477.JointUnion
