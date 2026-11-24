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
