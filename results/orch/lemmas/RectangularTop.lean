import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.RectangularTop

open PEqualNP.TopForm

lemma intersection_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (z a : Fin n) (haz : a ≠ z) (J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (ha : ∀ b ∈ J ∩ B, G.Adj a b) :
    (J ∩ B).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (hG a z haz)
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha b hb,
    hz b (Finset.mem_inter.mp hb).2⟩

lemma rectangle_star_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (z : Fin n) (I J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (hrect : ∀ a ∈ I, ∀ b ∈ J ∩ B, G.Adj a b) :
    I ⊆ {z} ∨ ∃ b : Fin n, J ∩ B ⊆ {b} := by
  classical
  by_cases hI : I ⊆ {z}
  · exact Or.inl hI
  · right
    obtain ⟨a, ha, haz⟩ := Finset.not_subset.mp hI
    have hcard := intersection_card_le_one G hG z a
      (by simpa only [Finset.mem_singleton] using haz) J B hz (hrect a ha)
    by_cases hne : (J ∩ B).Nonempty
    · obtain ⟨b, hb⟩ := hne
      refine ⟨b, ?_⟩
      intro c hc
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard) c hc b hb)
    · exact ⟨z, by simpa only [Finset.not_nonempty_iff_eq_empty.mp hne]
        using (Finset.empty_subset ({z} : Finset (Fin n)))⟩

lemma rectangle_off_center_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (hdeg : ∀ a : Fin n, (Finset.univ.filter (G.Adj a)).card ≤ 3)
    (z : Fin n) (I J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (hrect : ∀ a ∈ I, ∀ b ∈ J ∩ B, G.Adj a b) :
    ((I.erase z) ×ˢ (J ∩ B)).card ≤ 2 := by
  classical
  rcases rectangle_star_dichotomy G hG z I J B hz hrect with hI | ⟨b, hb⟩
  · have he : I.erase z = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have hmem := Finset.mem_erase.mp ha
      exact hmem.1 (Finset.mem_singleton.mp (hI hmem.2))
    simp [he]
  · by_cases hne : (J ∩ B).Nonempty
    · obtain ⟨c, hc⟩ := hne
      have hcb : c = b := Finset.mem_singleton.mp (hb hc)
      subst c
      have he : J ∩ B = {b} := Finset.Subset.antisymm hb (by simpa using hc)
      have hs : insert z (I.erase z) ⊆ Finset.univ.filter (G.Adj b) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hz b (Finset.mem_inter.mp hc).2).symm⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (hrect a (Finset.mem_erase.mp ha).2 b hc).symm⟩
      have hbound := (Finset.card_le_card hs).trans (hdeg b)
      have hcount : (I.erase z).card + 1 ≤ 3 := by
        rwa [Finset.card_insert_of_notMem (Finset.notMem_erase z I)] at hbound
      rw [he, Finset.card_product]
      simp only [Finset.card_singleton, Nat.mul_one]
      omega
    · have he : J ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [he]

lemma rectangle_edge_set_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (hdeg : ∀ a : Fin n, (Finset.univ.filter (G.Adj a)).card ≤ 3)
    (z : Fin n) (I J B : Finset (Fin n))
    (hz : ∀ b ∈ B, G.Adj z b)
    (hrect : ∀ a ∈ I, ∀ b ∈ J ∩ B, G.Adj a b)
    (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, ∃ a ∈ I, ∃ b ∈ J ∩ B, e = s(a, b) ∧ a ≠ z) :
    U.card ≤ 2 := by
  classical
  have hs : U ⊆ ((I.erase z) ×ˢ (J ∩ B)).image (fun p => s(p.1, p.2)) := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl, haz⟩ := hU e he
    exact Finset.mem_image.mpr ⟨(a, b),
      Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨haz, ha⟩, hb⟩, rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans
    (rectangle_off_center_card G hG hdeg z I J B hz hrect))

lemma colored_rectangle_edge_set_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G)
    (hdeg : ∀ a : Fin n, (Finset.univ.filter (G.Adj a)).card ≤ 3)
    (color : Fin n → Bool) (hcolor : ∀ a b, G.Adj a b → color a ≠ color b)
    (z : Fin n) (hzcolor : color z = false) (I J B : Finset (Fin n))
    (hI : ∀ a ∈ I, color a = false)
    (hz : ∀ b ∈ B, G.Adj z b)
    (hrect : ∀ a ∈ I, ∀ b ∈ J ∩ B, G.Adj a b)
    (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, ∃ a ∈ I, ∃ b ∈ J, e = s(a, b) ∧ (a ∈ B ∨ b ∈ B))
    (havoid : ∀ e ∈ U, z ∉ e) : U.card ≤ 2 := by
  apply rectangle_edge_set_card G hG hdeg z I J B hz hrect U
  intro e he
  obtain ⟨a, ha, b, hb, heq, hB⟩ := hU e he
  have hbB : b ∈ B := by
    rcases hB with haB | hbB
    · exact False.elim ((hcolor z a (hz a haB)) (hzcolor.trans (hI a ha).symm))
    · exact hbB
  refine ⟨a, ha, b, Finset.mem_inter.mpr ⟨hb, hbB⟩, heq, ?_⟩
  intro haz
  apply havoid e he
  rw [heq, haz]
  simp

end PEqualNP.Outside.L_meta_9811.RectangularTop
