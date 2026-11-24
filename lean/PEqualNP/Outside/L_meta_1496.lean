import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1496

open PEqualNP.CircuitLowerBounds in
theorem cone_count (n : ℕ) (g : ℕ → Gate) (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → k ∈ I) :
    stops.card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set U : Finset ℕ := insert (n + r) (E.biUnion (fun k => (g k).inputs.toFinset)) with hU
  have hEI : E ⊆ I := by
    intro k hk
    rw [hE, Finset.mem_filter] at hk
    exact hI k hk.1 hk.2.1 hk.2.2
  have hUcard : U.card ≤ 1 + 2 * E.card := by
    have h1 : (E.biUnion (fun k => (g k).inputs.toFinset)).card ≤ E.card * 2 := by
      refine Finset.card_biUnion_le_card_mul _ _ _ ?_
      intro k hk
      rw [hE, Finset.mem_filter] at hk
      exact le_trans (List.toFinset_card_le _) (hlen k hk.2.1 hk.2.2)
    have h2 : U.card ≤ (E.biUnion (fun k => (g k).inputs.toFinset)).card + 1 :=
      Finset.card_insert_le _ _
    omega
  have hRU : ∀ k, k ∈ R → n + k ∈ U := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨b, ?_, List.mem_toFinset.2 hb3⟩)
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := E.image (fun k => n + k) with hS2
  have hS2card : S2.card = E.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint stops S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hE, Finset.mem_filter] at hk
    rcases (hstops _).1 hw with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.2.1 h3
      · exact h3 hk.2.2
  have hsub : stops ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases (hstops _).1 hw with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k, ?_, List.mem_toFinset.2 hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rwa [Nat.add_sub_cancel' h1] at this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hE, Finset.mem_filter] at hk
      exact hRU k hk.1
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hEI
  omega

open PEqualNP.CircuitLowerBounds in
theorem len_le (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) (k : ℕ) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length ≤ 2 := by
  by_cases hk : k < C.gates.length
  · have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    exact le_of_eq (h.2.2 _ hmem)
  · unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_default _ _ (not_lt.1 hk)]
    simp

end PEqualNP.Outside.L_meta_1496

theorem PEqualNP.Outside.L_meta_1496 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
  ∀ (Z : Finset ℕ) (r : ℕ), r < C.gates.length →
  ∀ (R : Finset ℕ), (∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      n + k' ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) r k) →
  ∀ (stops : Finset ℕ), (∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or))) →
  ∀ I : Finset ℕ, (∀ k, k ∈ R → k ∉ Z →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or → k ∈ I) →
    stops.card ≤ I.card + 1 := by
  intro n C h Z r _ R hR stops hs I hI
  exact PEqualNP.Outside.L_meta_1496.cone_count n _ Z
    (fun k _ _ => PEqualNP.Outside.L_meta_1496.len_le n C h k) r R hR stops hs I hI
