import CountVectorCore

namespace PEqualNP.Outside.L_meta_2373.CountVector

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma count_insert (tag : α → β) (A : Finset α) (a : α) (fresh : a ∉ A) (j : β) :
    count tag (insert a A) j = (if tag a = j then 1 else 0) + count tag A j := by
  have dis : Disjoint ({a} : Finset α) A := by simpa using fresh
  have eq : insert a A = {a} ∪ A := by ext r; simp
  rw [eq, count_union tag {a} A dis, count_singleton]

lemma exists_subcounts (tag : α → β) (A : Finset α) (wanted : β → Nat)
    (bound : ∀ j, wanted j ≤ count tag A j) :
    ∃ B, B ⊆ A ∧ ∀ j, count tag B j = wanted j := by
  induction A using Finset.induction_on generalizing wanted with
  | empty =>
    refine ⟨∅, by simp, ?_⟩
    intro j
    have h := bound j
    have zero : wanted j = 0 := by simpa [count] using h
    simpa [count] using zero.symm
  | @insert a A fresh ih =>
    by_cases positive : 0 < wanted (tag a)
    · let rest := fun j => wanted j - if tag a = j then 1 else 0
      have restBound : ∀ j, rest j ≤ count tag A j := by
        intro j
        have h := bound j
        rw [count_insert tag A a fresh] at h
        dsimp [rest]
        by_cases eq : tag a = j
        · simp only [eq, ite_eq_left] at h ⊢
          omega
        · simpa [eq] using h
      obtain ⟨B, subB, countB⟩ := ih rest restBound
      refine ⟨insert a B, Finset.insert_subset_insert a subB, ?_⟩
      have freshB : a ∉ B := fun h => fresh (subB h)
      intro j
      rw [count_insert tag B a freshB, countB]
      dsimp [rest]
      by_cases eq : tag a = j
      · have pos : 0 < wanted j := by simpa [eq] using positive
        simp only [eq, ite_eq_left]
        omega
      · simp [eq]
    · have zero : wanted (tag a) = 0 := Nat.eq_zero_of_not_pos positive
      have reduced : ∀ j, wanted j ≤ count tag A j := by
        intro j
        have h := bound j
        rw [count_insert tag A a fresh] at h
        by_cases eq : tag a = j
        · have z : wanted j = 0 := by simpa [eq] using zero
          omega
        · simpa [eq] using h
      obtain ⟨B, subB, countB⟩ := ih wanted reduced
      exact ⟨B, subB.trans (Finset.subset_insert _ _), countB⟩

lemma count_split (tag : α → β) (A : Finset α) (left right : β → Nat)
    (sum : ∀ j, count tag A j = left j + right j) :
    ∃ L R, Disjoint L R ∧ L ∪ R = A ∧
      (∀ j, count tag L j = left j) ∧ ∀ j, count tag R j = right j := by
  have bound : ∀ j, left j ≤ count tag A j := by intro j; rw [sum]; omega
  obtain ⟨L, sub, counts⟩ := exists_subcounts tag A left bound
  refine ⟨L, A \ L, ?_, ?_, counts, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro r hr hs
    exact (Finset.mem_sdiff.mp hs).2 hr
  · ext r
    constructor
    · intro h
      rcases Finset.mem_union.mp h with hl | hr
      · exact sub hl
      · exact (Finset.mem_sdiff.mp hr).1
    · intro ha
      by_cases hl : r ∈ L
      · exact Finset.mem_union_left _ hl
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha, hl⟩)
  · intro j
    rw [count_sdiff tag A L sub, counts, sum]
    omega

lemma unit_support [Fintype β] (tag : α → β) (A : Finset α) (k : β)
    (unit : ∀ j, count tag A j = if k = j then 1 else 0) :
    ∃ r, A = {r} ∧ tag r = k := by
  have card : A.card = 1 := by
    rw [← count_sum tag A]
    simp_rw [unit]
    simp
  obtain ⟨r, eq⟩ := Finset.card_eq_one.mp card
  refine ⟨r, eq, ?_⟩
  have h := unit k
  rw [eq, count_singleton] at h
  by_contra ne
  simp [ne] at h

end PEqualNP.Outside.L_meta_2373.CountVector
