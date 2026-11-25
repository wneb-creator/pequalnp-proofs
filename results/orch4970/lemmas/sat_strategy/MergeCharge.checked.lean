import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.MergeCharge

def mergeLabel {α : Type*} (f : α → Nat) (a b : Nat) : α → Nat :=
  fun x => if f x = b then a else f x

def Monochromatic {α : Type*} (f : α → Nat) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, f x = f y

theorem merge_preserves {α : Type*} (f : α → Nat) (a b : Nat) (S : Finset α)
    (h : Monochromatic f S) : Monochromatic (mergeLabel f a b) S := by
  intro x hx y hy
  simp only [mergeLabel, h x hx y hy]

theorem merge_union {α : Type*} [DecidableEq α] (f : α → Nat) (A B : Finset α)
    (x y : α) (hx : x ∈ A) (hy : y ∈ B)
    (hA : Monochromatic f A) (hB : Monochromatic f B) :
    Monochromatic (mergeLabel f (f x) (f y)) (A ∪ B) := by
  have hval : ∀ z ∈ A ∪ B, mergeLabel f (f x) (f y) z = f x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [mergeLabel, hA z hz x hx]
      split_ifs <;> rfl
    · simp [mergeLabel, hB z hz y hy]
  intro u hu v hv
  exact (hval u hu).trans (hval v hv).symm

theorem merge_card {α : Type*} [DecidableEq α] (f : α → Nat)
    (S : Finset α) (a b : Nat) :
    (S.image f).card ≤ (S.image (mergeLabel f a b)).card + 1 := by
  have hs : S.image f ⊆ insert b (S.image (mergeLabel f a b)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    by_cases he : f x = b
    · simp [he]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [mergeLabel, he]⟩
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

def mergeList {α : Type*} : List (Nat × Nat) → (α → Nat) → (α → Nat)
  | [], f => f
  | (a,b) :: es, f => mergeList es (mergeLabel f a b)

theorem mergeList_card {α : Type*} [DecidableEq α] (es : List (Nat × Nat))
    (f : α → Nat) (S : Finset α) :
    (S.image f).card ≤ (S.image (mergeList es f)).card + es.length := by
  induction es generalizing f with
  | nil => simp [mergeList]
  | cons e es ih =>
    have h1 := merge_card f S e.1 e.2
    have h2 := ih (mergeLabel f e.1 e.2)
    simp only [mergeList, List.length_cons]
    omega

theorem connected_cost {n : Nat} (S : Finset (Fin n)) (es : List (Nat × Nat))
    (h : Monochromatic (mergeList es Fin.val) S) : S.card ≤ es.length + 1 := by
  by_cases hn : S.Nonempty
  · obtain ⟨x, hx⟩ := hn
    have hs : S.image (mergeList es Fin.val) ⊆ {mergeList es Fin.val x} := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_singleton.mpr (h y hy x hx)
    have hcard : (S.image (mergeList es Fin.val)).card ≤ 1 := by
      simpa using Finset.card_le_card hs
    have hb := mergeList_card es Fin.val S
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hb
    omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

end PEqualNP.Outside.L_meta_4970_aux.MergeCharge
