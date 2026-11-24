import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.MultiOutputFrontier

lemma binary_frontier {α : Type*} [DecidableEq α] (n : ℕ)
    (S : ℕ → Finset α) (left right : ℕ → ℕ)
    (hinput : ∀ w < n, (S w).card ≤ 1) :
    ∀ N (M W : Finset ℕ),
      (∀ w ∈ W, w < n+N) →
      (∀ k < N, 1 < (S (n+k)).card →
        left k < n+k ∧ right k < n+k ∧ S (n+k) ⊆ S (left k) ∪ S (right k)) →
      (∀ k < N, 1 < (S (n+k)).card →
        (S (left k)).Nonempty → (S (right k)).Nonempty → left k ≠ right k → k ∈ M) →
      (W.biUnion S).card ≤ M.card + W.card := by
  intro N
  induction N with
  | zero =>
    intro M W hW _ _
    calc
      (W.biUnion S).card ≤ ∑ w ∈ W, (S w).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ W, 1 := Finset.sum_le_sum (fun w hw => hinput w (by have := hW w hw; omega))
      _ ≤ M.card + W.card := by simp
  | succ k ih =>
    intro M W hW hnode hbranch
    let M' := M.erase k
    have hnode' : ∀ j < k, 1 < (S (n+j)).card →
        left j < n+j ∧ right j < n+j ∧ S (n+j) ⊆ S (left j) ∪ S (right j) :=
      fun j hj => hnode j (by omega)
    have hbranch' : ∀ j < k, 1 < (S (n+j)).card →
        (S (left j)).Nonempty → (S (right j)).Nonempty → left j ≠ right j → j ∈ M' := by
      intro j hj hc hl hr hne
      exact Finset.mem_erase.mpr ⟨by omega,hbranch j (by omega) hc hl hr hne⟩
    have hMsmall : M'.card ≤ M.card := Finset.card_le_card (Finset.erase_subset k M)
    by_cases htop : n+k ∈ W
    swap
    · apply (ih M' W (by
        intro w hw
        have hb := hW w hw
        have hn : w ≠ n+k := fun he => htop (he ▸ hw)
        omega) hnode' hbranch').trans
      omega
    have hWsmall : ∀ w ∈ W.erase (n+k), w < n+k := by
      intro w hw
      obtain ⟨hne,hw⟩ := Finset.mem_erase.mp hw
      have hb := hW w hw
      omega
    have hWcard : (W.erase (n+k)).card + 1 = W.card := Finset.card_erase_add_one htop
    by_cases hsmall : (S (n+k)).card ≤ 1
    · have hcount := ih M' (W.erase (n+k)) hWsmall hnode' hbranch'
      have hsub : W.biUnion S ⊆ (W.erase (n+k)).biUnion S ∪ S (n+k) := by
        intro a ha
        obtain ⟨w,hw,haw⟩ := Finset.mem_biUnion.mp ha
        by_cases he : w = n+k
        · exact Finset.mem_union_right _ (he ▸ haw)
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨w,Finset.mem_erase.mpr ⟨he,hw⟩,haw⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    have hbig : 1 < (S (n+k)).card := by omega
    obtain ⟨hl,hr,hsplit⟩ := hnode k (by omega) hbig
    let children := ({left k,right k} : Finset ℕ).filter fun w => (S w).Nonempty
    let W' := W.erase (n+k) ∪ children
    have hchildren : ∀ w ∈ children, w < n+k := by
      intro w hw
      have he : w=left k ∨ w=right k := by
        simpa only [Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hw).1
      rcases he with rfl | rfl <;> assumption
    have hW' : ∀ w ∈ W', w < n+k := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hWsmall w hw
      · exact hchildren w hw
    have hsub : W.biUnion S ⊆ W'.biUnion S := by
      intro a ha
      obtain ⟨w,hw,haw⟩ := Finset.mem_biUnion.mp ha
      by_cases he : w=n+k
      · have hp := hsplit (he ▸ haw)
        rcases Finset.mem_union.mp hp with hp | hp
        · exact Finset.mem_biUnion.mpr ⟨left k,Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨by simp,⟨a,hp⟩⟩),hp⟩
        · exact Finset.mem_biUnion.mpr ⟨right k,Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨by simp,⟨a,hp⟩⟩),hp⟩
      · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨he,hw⟩),haw⟩
    have hc := (Finset.card_le_card hsub).trans (ih M' W' hW' hnode' hbranch')
    have hWbound : W'.card ≤ (W.erase (n+k)).card + children.card := Finset.card_union_le _ _
    have hchildrenBound : children.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans (by simp))
    by_cases hsmallChild : children.card ≤ 1
    · omega
    · have hkM : k ∈ M := by
        obtain ⟨w,hw,z,hz,hwz⟩ := Finset.one_lt_card.mp (by omega : 1 < children.card)
        obtain ⟨hw,hwn⟩ := Finset.mem_filter.mp hw
        obtain ⟨hz,hzn⟩ := Finset.mem_filter.mp hz
        have hw' : w=left k ∨ w=right k := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw
        have hz' : z=left k ∨ z=right k := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
        rcases hw' with rfl | rfl <;> rcases hz' with rfl | rfl
        · exact (hwz rfl).elim
        · exact hbranch k (by omega) hbig hwn hzn hwz
        · exact hbranch k (by omega) hbig hzn hwn hwz.symm
        · exact (hwz rfl).elim
      have hMcard : M'.card + 1 = M.card := Finset.card_erase_add_one hkM
      omega

end PEqualNP.Outside.L_meta_1477.MultiOutputFrontier
