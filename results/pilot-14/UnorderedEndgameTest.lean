import UnorderedEmbeddingTest
import RetainedExtensionTest
import FirstOrbitTest
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedEndgame
open LiveCheck LiteralBinary TightFormula
lemma one_duplicate {n : Nat} {a : Sig} {v : List Sig}
    (ha : a ∈ v) (ht : UnorderedFormula.test (n+1) (a :: v) = true) :
    UnorderedFormula.testOne (n+1) v = true := by
  simp only [UnorderedFormula.testOne, Bool.or_eq_true]
  exact Or.inl (Or.inl (Or.inr (List.any_eq_true.mpr ⟨a, ha, ht⟩)))
lemma first_cut_impossible {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha' : a ∈ literals) (hb' : b ∈ literals) (hab : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (tail : Live k t (insert (bin d a b) U))
    (fresh : bin d a b ∉ U) (hk : k ≤ t+10)
    (checkedOne : UnorderedFormula.testOne 4 (phase (bin d a b) :: inputs) = false) : False := by
  have hsize := LiveCheck.live_size tail
  rw [Finset.card_insert_of_notMem fresh] at hsize
  have huc : U.card ≤ 10 := by omega
  obtain ⟨extra, he, hm, hp⟩ := retained_extension ha' hb' hab hu tail huc
  have hc : U.card = extra.length + 9 := by
    have hl := hp.length_eq
    simpa only [List.length_map, Finset.length_toList, List.length_append,
      inputs, List.length_map, List.length_finRange] using hl
  have falseResult := checkedOne
  cases extra with
  | nil =>
    simp only [List.nil_append] at hp
    have hq : (phase (bin d a b) :: inputs).Perm
        ((insert (bin d a b) U).toList.map phase) :=
      (hp.symm.cons _).trans ((Finset.toList_insert fresh).map phase).symm
    have ht' : UnorderedFormula.testOne 4 (phase (bin d a b) :: inputs) = true := by
      by_cases heq : k = t+10
      · apply UnorderedFormula.one_test tail _ 4 _ hq
        rw [Finset.card_insert_of_notMem fresh]
        simp only [List.length_nil, Nat.zero_add] at hc
        omega
      · apply UnorderedFormula.test_implies_one
        apply UnorderedFormula.tight_test tail _ 4 _ hq
        rw [Finset.card_insert_of_notMem fresh]
        simp only [List.length_nil, Nat.zero_add] at hc
        omega
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
      have ht' := UnorderedFormula.tight_test tail ht 4 _ hq
      have hh := one_duplicate (List.mem_cons_of_mem _ hx) ht'
      rw [falseResult] at hh
      cases hh

lemma lower_twelve_by_cuts
    (cuts : ∀ (k t : Nat) (U : Finset Sig) (a b : Sig) (d : Bool),
      a ∈ literals → b ∈ literals → a ≠ b → (∀ z ∈ U, z ∈ literals) →
      Live k t (insert (bin d a b) U) → bin d a b ∉ U → k ≤ t+10 → False)
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
    exact cuts k t U a b d ha' hb' hab hu tail
      (fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))) (by omega)
lemma lower_twelve_representatives
    (checkedReps : ∀ p ∈ LiveCheck.pairReps,
      ∀ z ∈ ops (phase (raw.getD p.1.val zero)) (phase (raw.getD p.2.val zero)),
        UnorderedFormula.testOne 4 (z :: inputs) = false)
    {k t S} (h : Live k t S) (hs : ∀ a ∈ S, a ∈ literals) : t+12 ≤ k := by
  apply lower_twelve_by_cuts _ h hs
  intro k t U a b d ha hb hab hu tail fresh hk
  obtain ⟨a', b', U', ha', hb', hab', hp, hu', hc, hf', ht'⟩ :=
    FirstOrbit.first_cut ha hb hab hu fresh tail
  have hm := op_mem d a' b'
  rw [literal_phase_index ha', literal_phase_index hb'] at hm
  exact first_cut_impossible ha' hb' hab' hu' ht' hf' hk
    (checkedReps (index a', index b') hp _ hm)

lemma high_nots
    (checkedReps : ∀ p ∈ LiveCheck.pairReps,
      ∀ z ∈ ops (phase (raw.getD p.1.val zero)) (phase (raw.getD p.2.val zero)),
        UnorderedFormula.testOne 4 (z :: inputs) = false)
    {t : Nat} (ht : 4 ≤ t) : Impossible 15 t raw := by
  intro k hk h
  have hb := lower_twelve_representatives checkedReps h
    (fun a ha => List.mem_append_left _ (List.mem_toFinset.mp ha))
  omega

end PEqualNP.Outside.L_meta_670_aux.UnorderedEndgame
