import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896

lemma conjunction_closure_preserves {α : Type} {n m : ℕ}
    (w : Fin n → α → Prop) (p : Fin m → α) (S : Finset (Fin n)) :
    let f := fun x => ∀ i ∈ S, w i x
    let c := fun x => ∀ i, (∀ j, f (p j) → w i (p j)) → w i x
    (∀ x, c x → f x) ∧ ∀ j, c (p j) ↔ f (p j) := by
  dsimp only
  constructor
  · intro x hc i hi
    exact hc i (fun j hj => hj i hi)
  · intro j
    constructor
    · intro hc i hi
      exact hc i (fun k hk => hk i hi)
    · intro hf i hi
      exact hi j hf

lemma cover_replace_union {α : Type} [DecidableEq α]
    (X : Finset α) (F C : Finset (Finset α)) (U A B : Finset α)
    (hA : A ∈ F) (hB : B ∈ F) (hU : U ⊆ A ∪ B)
    (hCF : C ⊆ insert U F)
    (hC : ∀ x ∈ X, ∃ V ∈ C, x ∈ V) :
    ∃ D : Finset (Finset α), D ⊆ F ∧
      (∀ x ∈ X, ∃ V ∈ D, x ∈ V) ∧ D.card ≤ C.card + 1 := by
  classical
  by_cases hUC : U ∈ C
  · let D := insert A (insert B (C.erase U))
    refine ⟨D, ?_, ?_, ?_⟩
    · intro V hV
      simp only [D, Finset.mem_insert] at hV
      rcases hV with rfl | rfl | hV
      · exact hA
      · exact hB
      · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hV
        rcases Finset.mem_insert.mp (hCF hmem) with heq | hF
        · exact (hne heq).elim
        · exact hF
    · intro x hx
      obtain ⟨V, hV, hxV⟩ := hC x hx
      by_cases hVU : V = U
      · subst V
        rcases Finset.mem_union.mp (hU hxV) with hxA | hxB
        · exact ⟨A, by simp [D], hxA⟩
        · exact ⟨B, by simp [D], hxB⟩
      · exact ⟨V, by simp [D, hVU, hV], hxV⟩
    · have hc := Finset.card_erase_add_one hUC
      calc
        D.card ≤ (insert B (C.erase U)).card + 1 := Finset.card_insert_le _ _
        _ ≤ (C.erase U).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = C.card + 1 := by rw [hc]
  · refine ⟨C, ?_, hC, Nat.le_succ _⟩
    intro V hV
    rcases Finset.mem_insert.mp (hCF hV) with hVU | hF
    · exact (hUC (hVU ▸ hV)).elim
    · exact hF

end PEqualNP.Outside.L_meta_1896
