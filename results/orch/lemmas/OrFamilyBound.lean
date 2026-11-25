import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace PEqualNP.Outside.L_meta_2602_aux.OrFamilyBound

lemma unary_union_bound {α : Type} [DecidableEq α] (U : Finset ℕ) (f : ℕ → Finset α) (l r : ℕ → ℕ)
    (N0 : ℕ) (hleaf : ∀ j < N0, j ∉ U → (f j).card ≤ 1 ∨ ∃ p < j, f j ⊆ f p)
    (hU : ∀ j ∈ U, l j < j ∧ r j < j ∧ f j = f (l j) ∪ f (r j)) :
    ∀ N ≤ N0, ∀ V : Finset ℕ, V ⊆ Finset.range N →
      (V.biUnion f).card ≤ V.card + (U.filter (fun j => j < N)).card := by
  intro N
  induction N with
  | zero =>
    intro _ V hV
    have : V = ∅ := by simpa using hV
    subst this
    simp
  | succ N ih =>
    intro hN V hV
    have hmono : (U.filter (fun j => j < N)).card ≤ (U.filter (fun j => j < N + 1)).card :=
      Finset.card_le_card (fun j hj => by
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩)
    by_cases hNV : N ∈ V
    · have hV' : V.erase N ⊆ Finset.range N := by
        intro j hj
        have h1 := Finset.mem_erase.1 hj
        have h2 := Finset.mem_range.1 (hV h1.2)
        exact Finset.mem_range.2 (by omega)
      have hcard : (V.erase N).card + 1 = V.card := Finset.card_erase_add_one hNV
      have hsplit : V.biUnion f = f N ∪ (V.erase N).biUnion f := by
        conv_lhs => rw [← Finset.insert_erase hNV]
        rw [Finset.biUnion_insert]
      by_cases hNU : N ∈ U
      · obtain ⟨hl, hr, hf⟩ := hU N hNU
        have hV2 : insert (l N) (insert (r N) (V.erase N)) ⊆ Finset.range N := by
          intro j hj
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact Finset.mem_range.2 hl
          · rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hr
            · exact hV' hj
        have h1 := ih (by omega) _ hV2
        have hsub : V.biUnion f ⊆ (insert (l N) (insert (r N) (V.erase N))).biUnion f := by
          rw [hsplit, hf, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
        have h2 := Finset.card_le_card hsub
        have h3 : (insert (l N) (insert (r N) (V.erase N))).card ≤ (V.erase N).card + 2 :=
          (Finset.card_insert_le _ _).trans (by
            have := Finset.card_insert_le (r N) (V.erase N)
            omega)
        have h4 : (U.filter (fun j => j < N + 1)).card = (U.filter (fun j => j < N)).card + 1 := by
          have : U.filter (fun j => j < N + 1) = insert N (U.filter (fun j => j < N)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hj, hlt⟩
              by_cases e : j = N
              · exact Or.inl e
              · exact Or.inr ⟨hj, by omega⟩
            · rintro (rfl | ⟨hj, hlt⟩)
              · exact ⟨hNU, by omega⟩
              · exact ⟨hj, by omega⟩
          rw [this, Finset.card_insert_of_notMem (by simp)]
        omega
      · rcases hleaf N (by omega) hNU with hleaf | ⟨p, hp, hsub⟩
        · have h1 := ih (by omega) _ hV'
          have h3 : (V.biUnion f).card ≤ (f N).card + ((V.erase N).biUnion f).card := by
            rw [hsplit]
            exact Finset.card_union_le _ _
          omega
        · have hV2 : insert p (V.erase N) ⊆ Finset.range N := by
            intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hp
            · exact hV' hj
          have h1 := ih (by omega) _ hV2
          have hsubV : V.biUnion f ⊆ (insert p (V.erase N)).biUnion f := by
            rw [hsplit, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hsub
          have h2 := Finset.card_le_card hsubV
          have h3 := Finset.card_insert_le p (V.erase N)
          omega
    · have hV' : V ⊆ Finset.range N := by
        intro j hj
        have h2 := Finset.mem_range.1 (hV hj)
        have : j ≠ N := fun e => hNV (e ▸ hj)
        exact Finset.mem_range.2 (by omega)
      have h1 := ih (by omega) V hV'
      omega


end PEqualNP.Outside.L_meta_2602_aux.OrFamilyBound
