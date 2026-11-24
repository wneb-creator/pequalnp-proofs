import Mathlib

namespace PEqualNP.Outside.L_meta_1477.PrivateConeBudget

lemma binary_support_card_le {α : Type*} [DecidableEq α]
    (n : ℕ) (S : ℕ → Finset α) (left right : ℕ → ℕ)
    (hinput : ∀ r < n, (S r).card ≤ 1) :
    ∀ N (M R : Finset ℕ),
      (∀ k ∈ M, k < N) →
      (∀ k ∈ M, left k < n + k ∧ right k < n + k ∧
        S (n + k) ⊆ S (left k) ∪ S (right k)) →
      (∀ k ∈ M, ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∈ M) →
      (∀ r ∈ R, r < n + N ∧ (r < n ∨ r - n ∈ M)) →
      (R.biUnion S).card ≤ M.card + R.card := by
  intro N
  induction N with
  | zero =>
    intro M R hM hnode hclosed hroots
    calc
      (R.biUnion S).card ≤ ∑ r ∈ R, (S r).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ R, 1 := Finset.sum_le_sum (fun r hr => hinput r (by have := (hroots r hr).1; omega))
      _ ≤ M.card + R.card := by simp
  | succ k ih =>
    intro M R hM hnode hclosed hroots
    let M' := M.erase k
    have hMb : ∀ i ∈ M', i < k := by
      intro i hi
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
      have hb := hM i hm
      omega
    have hn : ∀ i ∈ M', left i < n + i ∧ right i < n + i ∧
        S (n + i) ⊆ S (left i) ∪ S (right i) := by
      intro i hi
      exact hnode i (Finset.mem_of_mem_erase hi)
    have hbelow (r : ℕ) (hr : r < n + k) (hm : r < n ∨ r - n ∈ M) :
        r < n ∨ r - n ∈ M' := by
      rcases hm with h | h
      · exact Or.inl h
      · by_cases hi : r < n
        · exact Or.inl hi
        · exact Or.inr (Finset.mem_erase.mpr ⟨by omega, h⟩)
    have hcl : ∀ i ∈ M', ∀ r, r = left i ∨ r = right i → r < n ∨ r - n ∈ M' := by
      intro i hi r hr
      have hib := hMb i hi
      have hno := hn i hi
      apply hbelow r
      · rcases hr with rfl | rfl <;> omega
      · exact hclosed i (Finset.mem_of_mem_erase hi) r hr
    by_cases htop : n + k ∈ R
    · have hkm : k ∈ M := by
        rcases (hroots (n + k) htop).2 with h | h
        · omega
        · simpa using h
      let R' := R.erase (n + k) ∪ {left k, right k}
      have hrb : ∀ r ∈ R', r < n + k ∧ (r < n ∨ r - n ∈ M') := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · obtain ⟨hne, hr⟩ := Finset.mem_erase.mp hr
          have hb := (hroots r hr).1
          have hl : r < n + k := by omega
          exact ⟨hl, hbelow r hl (hroots r hr).2⟩
        · have he : r = left k ∨ r = right k := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
          have hkno := hnode k hkm
          have hl : r < n + k := by rcases he with rfl | rfl <;> omega
          exact ⟨hl, hbelow r hl (hclosed k hkm r he)⟩
      have hsub : R.biUnion S ⊆ R'.biUnion S := by
        intro a ha
        obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
        by_cases he : r = n + k
        · subst r
          have hx := (hnode k hkm).2.2 har
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_biUnion.mpr ⟨left k, Finset.mem_union_right _ (by simp), hx⟩
          · exact Finset.mem_biUnion.mpr ⟨right k, Finset.mem_union_right _ (by simp), hx⟩
        · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hr⟩), har⟩
      have hcount := (Finset.card_le_card hsub).trans (ih M' R' hMb hn hcl hrb)
      have hMcard : M'.card + 1 = M.card := Finset.card_erase_add_one hkm
      have hRcard : (R.erase (n + k)).card + 1 = R.card := Finset.card_erase_add_one htop
      have hUnion := Finset.card_union_le (R.erase (n + k)) ({left k, right k} : Finset ℕ)
      have hPair : ({left k, right k} : Finset ℕ).card ≤ 2 := by
        exact (Finset.card_insert_le _ _).trans (by simp)
      change R'.card ≤ (R.erase (n + k)).card + _ at hUnion
      omega
    · have hrb : ∀ r ∈ R, r < n + k ∧ (r < n ∨ r - n ∈ M') := by
        intro r hr
        have hne : r ≠ n + k := fun h => htop (h ▸ hr)
        have hb := (hroots r hr).1
        have hl : r < n + k := by omega
        exact ⟨hl, hbelow r hl (hroots r hr).2⟩
      have hcount := ih M' R hMb hn hcl hrb
      have hmcard : M'.card ≤ M.card := Finset.card_le_card (Finset.erase_subset _ _)
      omega

end PEqualNP.Outside.L_meta_1477.PrivateConeBudget
