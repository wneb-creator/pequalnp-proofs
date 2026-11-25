import Mathlib

namespace PEqualNP.Outside.L_meta_1770_aux.Moore

lemma order_ge_ten {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hmin : ∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v)
    (hne : ∃ u v : Fin n, G.Adj u v) : 10 ≤ n := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  let N : Fin n → Finset (Fin n) := fun v => G.neighborFinset v
  let S : Fin n → Finset (Fin n) := fun v => (N v).erase a
  let D : Finset (Fin n) := (N a).biUnion S
  have hN : ∀ u v, v ∈ N u ↔ G.Adj u v := by
    intro u v
    simp [N]
  have hcN : ∀ v, (N v).card = G.degree v := fun _ => rfl
  have hpos : 0 < (N a).card := Finset.card_pos.mpr ⟨b, (hN a b).mpr hab⟩
  have ha3 : 3 ≤ (N a).card := by
    rcases hmin a with h | h
    · rw [← hcN a] at h
      omega
    · simpa only [hcN] using h
  have hS2 : ∀ v ∈ N a, 2 ≤ (S v).card := by
    intro v hv
    have hav : a ∈ N v := (hN v a).mpr ((hN a v).mp hv).symm
    have hvpos := Finset.card_pos.mpr ⟨a, hav⟩
    have hv3 : 3 ≤ (N v).card := by
      rcases hmin v with h | h
      · rw [← hcN v] at h
        omega
      · simpa only [hcN] using h
    have herase := Finset.card_erase_of_mem hav
    change 2 ≤ ((N v).erase a).card
    omega
  have hdisj : (N a : Set (Fin n)).PairwiseDisjoint S := by
    intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro z hzv hzw
    have hzv' := Finset.mem_erase.mp hzv
    have hzw' := Finset.mem_erase.mp hzw
    exact hfour a v z w (Ne.symm hzv'.1) hvw
      ⟨(hN a v).mp hv, (hN v z).mp hzv'.2,
       ((hN w z).mp hzw'.2).symm, ((hN a w).mp hw).symm⟩
  have hDcard : D.card = ∑ v ∈ N a, (S v).card := Finset.card_biUnion hdisj
  have hD2 : 2 * (N a).card ≤ D.card := by
    rw [hDcard]
    calc 2 * (N a).card = ∑ v ∈ N a, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ N a, (S v).card := Finset.sum_le_sum hS2
  have hND : Disjoint (N a) D := by
    apply Finset.disjoint_left.mpr
    intro z hz hzd
    obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp hzd
    exact htri a v z ((hN a v).mp hv)
      ((hN v z).mp (Finset.mem_erase.mp hzv).2) ((hN a z).mp hz).symm
  have ha : a ∉ N a ∪ D := by
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · simpa only [hN] using (G.irrefl : ¬ G.Adj a a)
    · intro h
      obtain ⟨v, _, hav⟩ := Finset.mem_biUnion.mp h
      exact Finset.notMem_erase a (N v) hav
  have hc : (insert a (N a ∪ D)).card ≤ n := by
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  rw [Finset.card_insert_of_notMem ha, Finset.card_union_of_disjoint hND] at hc
  omega

end PEqualNP.Outside.L_meta_1770_aux.Moore
