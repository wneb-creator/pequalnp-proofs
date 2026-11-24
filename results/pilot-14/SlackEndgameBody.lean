namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck LiteralBinary
lemma one_duplicate {n : Nat} {a : Sig} {v : List Sig}
    (ha : a ∈ v) (ht : test (n+1) (a :: v) = true) : testOne (n+1) v = true := by
  simp only [testOne, Bool.or_eq_true]
  exact Or.inl (Or.inl (Or.inr (List.any_eq_true.mpr ⟨a, ha, ht⟩)))

lemma lower_twelve
    (checked : ∀ a ∈ literals, ∀ b ∈ literals, ∀ d,
      test 3 (phase (bin d a b) :: inputs) = false)
    (checkedOne : ∀ a ∈ literals, ∀ b ∈ literals, ∀ d,
      testOne 4 (phase (bin d a b) :: inputs) = false)
    {k t S} (h : Live k t S) :
    (∀ a ∈ S, a ∈ literals) → t+12 ≤ k := by
  induction h with
  | stop =>
    intro hs
    exact False.elim (target_not_literal (hs target (by simp)))
  | @unary k t U a ha hf tail ih =>
    intro hs
    have hh := ih (fun z hz => by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact neg_literal (hs a (Finset.mem_insert_self _ _))
      · exact hs z (Finset.mem_insert_of_mem hz))
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro hs
    by_contra hn
    have hu : ∀ z ∈ U, z ∈ literals :=
      fun z hz => hs z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    have ha' := hs a (Finset.mem_insert_self _ _)
    have hb' := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hb11 := lower_eleven checked (Live.binary ha hb hab hf tail) hs
    have hk : k = t+10 := by omega
    have hsize := LiveCheck.live_size tail
    have fresh : bin d a b ∉ U :=
      fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    rw [Finset.card_insert_of_notMem fresh] at hsize
    have huc : U.card ≤ 10 := by omega
    obtain ⟨extra, he, hm, hp⟩ := retained_extension ha' hb' hab hu tail huc
    have hc : U.card = extra.length + 9 := by
      have hl := hp.length_eq
      simpa only [List.length_map, Finset.length_toList, List.length_append,
        inputs, List.length_map, List.length_finRange] using hl
    have falseResult := checkedOne a ha' b hb' d
    cases extra with
    | nil =>
      simp only [List.nil_append] at hp
      have ht : (insert (bin d a b) U).card + t = k := by
        rw [Finset.card_insert_of_notMem fresh]
        simp only [List.length_nil, Nat.zero_add] at hc
        omega
      have hq : (phase (bin d a b) :: inputs).Perm
          ((insert (bin d a b) U).toList.map phase) :=
        (hp.symm.cons _).trans ((Finset.toList_insert fresh).map phase).symm
      have ht' := one_test tail ht 4 _ hq
      rw [falseResult] at ht'
      cases ht'
    | cons x xs =>
      cases xs with
      | cons y ys => simp only [List.length_cons] at he; omega
      | nil =>
        have hx : x ∈ inputs := hm (by simp)
        simp only [List.cons_append, List.nil_append] at hp
        have ht : (insert (bin d a b) U).card + t = k+1 := by
          rw [Finset.card_insert_of_notMem fresh]
          simp only [List.length_cons, List.length_nil] at hc
          omega
        have hq : (x :: phase (bin d a b) :: inputs).Perm
            ((insert (bin d a b) U).toList.map phase) :=
          ((List.Perm.swap _ _ _).trans (hp.symm.cons _)).trans
            ((Finset.toList_insert fresh).map phase).symm
        have ht' := tight_test tail ht 4 _ hq
        have hh := one_duplicate (List.mem_cons_of_mem _ hx) ht'
        rw [falseResult] at hh
        cases hh
end PEqualNP.Outside.L_meta_670_aux.TightFormula
