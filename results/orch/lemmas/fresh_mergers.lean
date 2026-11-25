import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Mergers

lemma frontier_bound {V : Type} [DecidableEq V] (supp : ℕ → Finset V) (merges : Finset ℕ)
    (hstep : ∀ w, 1 < (supp w).card →
      (∃ a < w, supp w ⊆ supp a) ∨
      (w ∈ merges ∧ ∃ a < w, ∃ b < w, supp w ⊆ supp a ∪ supp b)) :
    ∀ (k : ℕ) (F : Finset ℕ), F ⊆ Finset.range k →
      (F.biUnion supp).card ≤ F.card + (merges ∩ Finset.range k).card := by
  intro k
  induction k with
  | zero =>
    intro F hF
    have hz : F = ∅ := by simpa using hF
    simp [hz]
  | succ k ih =>
    intro F hF
    have hrest : F.erase k ⊆ Finset.range k := by
      intro i hi
      have hne := (Finset.mem_erase.mp hi).1
      have hlt := Finset.mem_range.mp (hF (Finset.mem_of_mem_erase hi))
      exact Finset.mem_range.mpr (by omega)
    have hmon : (merges ∩ Finset.range k).card ≤ (merges ∩ Finset.range (k + 1)).card :=
      Finset.card_le_card (by
        intro i hi
        obtain ⟨him, hir⟩ := Finset.mem_inter.mp hi
        exact Finset.mem_inter.mpr ⟨him, Finset.mem_range.mpr ((Finset.mem_range.mp hir).trans (Nat.lt_succ_self k))⟩)
    by_cases hk : k ∈ F
    · have hnum := Finset.card_erase_add_one hk
      have hun : F.biUnion supp = supp k ∪ (F.erase k).biUnion supp := by
        conv_lhs => rw [← Finset.insert_erase hk, Finset.biUnion_insert]
      by_cases hs : (supp k).card ≤ 1
      · rw [hun]
        have hcard := Finset.card_union_le (supp k) ((F.erase k).biUnion supp)
        have hf := ih (F.erase k) hrest
        omega
      · rcases hstep k (by omega) with ⟨a, ha, hka⟩ | ⟨hm, a, ha, b, hb, hkab⟩
        · have hnext : insert a (F.erase k) ⊆ Finset.range k :=
            Finset.insert_subset (Finset.mem_range.mpr ha) hrest
          have hinc : F.biUnion supp ⊆ (insert a (F.erase k)).biUnion supp := by
            rw [hun, Finset.biUnion_insert]
            exact Finset.union_subset_union hka (by rfl)
          have hcard := Finset.card_le_card hinc
          have hcount := Finset.card_insert_le a (F.erase k)
          have hf := ih _ hnext
          omega
        · have hnext : insert a (insert b (F.erase k)) ⊆ Finset.range k :=
            Finset.insert_subset (Finset.mem_range.mpr ha)
              (Finset.insert_subset (Finset.mem_range.mpr hb) hrest)
          have hinc : F.biUnion supp ⊆ (insert a (insert b (F.erase k))).biUnion supp := by
            rw [hun, Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
            exact Finset.union_subset_union hkab (by rfl)
          have hcard := Finset.card_le_card hinc
          have hcounta := Finset.card_insert_le a (insert b (F.erase k))
          have hcountb := Finset.card_insert_le b (F.erase k)
          have hf := ih _ hnext
          have hin : merges ∩ Finset.range (k + 1) = insert k (merges ∩ Finset.range k) := by
            ext i
            by_cases heq : i = k
            · subst i
              simp [hm]
            · have hi : i < k + 1 ↔ i < k := by omega
              simp [heq, hi]
          have hnumM : (merges ∩ Finset.range (k + 1)).card =
              (merges ∩ Finset.range k).card + 1 := by simp [hin]
          omega
    · have hprev : F ⊆ Finset.range k := by simpa [Finset.erase_eq_of_notMem hk] using hrest
      exact (ih F hprev).trans (by omega)

lemma wire_merger_bound {V : Type} [DecidableEq V] (supp : ℕ → Finset V) (merges : Finset ℕ)
    (hstep : ∀ w, 1 < (supp w).card →
      (∃ a < w, supp w ⊆ supp a) ∨
      (w ∈ merges ∧ ∃ a < w, ∃ b < w, supp w ⊆ supp a ∪ supp b)) (out : ℕ) :
    (supp out).card ≤ merges.card + 1 := by
  have h := frontier_bound supp merges hstep (out + 1) {out} (by simp)
  have hle : (merges ∩ Finset.range (out + 1)).card ≤ merges.card :=
    Finset.card_le_card Finset.inter_subset_left
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at h
  omega

end PEqualNP.Outside.L_meta_2583.Mergers
