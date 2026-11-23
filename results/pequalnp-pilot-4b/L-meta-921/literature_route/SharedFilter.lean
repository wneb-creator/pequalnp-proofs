import Mathlib

namespace SharedFilter

variable {α : Type*} [DecidableEq α]

private theorem cannot_cover (S T A P : Finset α)
    (hST : (S ∩ T).card ≤ 1) (hT : T.card = 4)
    (hA : A ⊆ S) (hP : P.card ≤ 2) : ¬ T ⊆ A ∪ P := by
  intro h
  have hsub : T ⊆ (A ∩ T) ∪ P := by
    intro p hp
    rcases Finset.mem_union.mp (h hp) with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hp⟩)
    · exact Finset.mem_union_right _ hb
  have hcap : (A ∩ T).card ≤ 1 :=
    (Finset.card_le_card (by
      intro p hp
      exact Finset.mem_inter.mpr ⟨hA (Finset.mem_inter.mp hp).1,
        (Finset.mem_inter.mp hp).2⟩ : A ∩ T ⊆ S ∩ T)).trans hST
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (A ∩ T) P)
  omega

/-- A shared detector followed by a two-point filter for T has no certificate
of size at most three contained in another line S. -/
theorem no_small_certificate (S T A P : Finset α) (g : Finset α → Prop)
    (hST : (S ∩ T).card ≤ 1) (hT : T.card = 4)
    (hA : A ⊆ S) (hAc : A.card ≤ 3) (hPc : P.card ≤ 2)
    (hmono : Monotone g)
    (hcorrect : ∀ U : Finset α, U.card ≤ 5 → P ⊆ U → g U → T ⊆ U) :
    ¬ g A := by
  intro ha
  have hu : (A ∪ P).card ≤ 5 := (Finset.card_union_le A P).trans (by omega)
  have hg : g (A ∪ P) := hmono Finset.subset_union_left ha
  exact cannot_cover S T A P hST hT hA hPc
    (hcorrect (A ∪ P) hu Finset.subset_union_right hg)

/-- If a full four-point line activates the shared detector, the other
output's two-point filter must be disjoint from it. Otherwise a forbidden
input has at most five points. -/
theorem filter_disjoint (S T P : Finset α) (g : Finset α → Prop)
    (hST : (S ∩ T).card ≤ 1) (hS : S.card = 4) (hT : T.card = 4)
    (hPc : P.card ≤ 2) (hmono : Monotone g) (hgs : g S)
    (hcorrect : ∀ U : Finset α, U.card ≤ 5 → P ⊆ U → g U → T ⊆ U) :
    Disjoint S P := by
  by_contra hd
  have hpos : 0 < (S ∩ P).card := Finset.card_pos.mpr
    (Finset.not_disjoint_iff_nonempty_inter.mp hd)
  have hsum := Finset.card_union_add_card_inter S P
  have hu : (S ∪ P).card ≤ 5 := by omega
  have hg : g (S ∪ P) := hmono Finset.subset_union_left hgs
  exact cannot_cover S T S P hST hT (by rfl) hPc
    (hcorrect (S ∪ P) hu Finset.subset_union_right hg)

/-- Two private filter points per line, plus an intersection point, force
at least `2*m+1` distinct inputs in the common detector. -/
theorem private_pairs_union {m : ℕ} (hm : 2 ≤ m)
    (S P : Fin m → Finset α)
    (hP : ∀ i, (P i).card = 2) (hsub : ∀ i, P i ⊆ S i)
    (hprivate : ∀ i j, i ≠ j → Disjoint (S i) (P j))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).Nonempty) :
    2 * m + 1 ≤ (Finset.univ.biUnion S).card := by
  classical
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  obtain ⟨a, ha⟩ := hinter i j hij
  have hai := (Finset.mem_inter.mp ha).1
  have haj := (Finset.mem_inter.mp ha).2
  let U := Finset.univ.biUnion P
  have hpw : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro u _ v _ huv
    exact (hprivate u v huv).mono_left (hsub u)
  have hU : U.card = 2 * m := by
    dsimp [U]
    rw [Finset.card_biUnion hpw]
    simp [hP, Nat.mul_comm]
  have hnot : a ∉ U := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
    by_cases hki : k = i
    · subst k
      exact Finset.disjoint_left.mp (hprivate j i hij.symm) haj hk
    · exact Finset.disjoint_left.mp (hprivate i k (Ne.symm hki)) hai hk
  have hcover : insert a U ⊆ Finset.univ.biUnion S := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hu
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hai⟩
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hu
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hsub k hk⟩
  have hcard := Finset.card_le_card hcover
  rw [Finset.card_insert_of_notMem hnot, hU] at hcard
  exact hcard

end SharedFilter
