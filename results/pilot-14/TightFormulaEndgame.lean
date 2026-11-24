namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck
open LiteralBinary

def inputs : List Sig := (List.finRange 9).map fun i => phase (raw.getD i.val zero)
lemma inputs_eq : inputs = raw.map phase := by decide +kernel
lemma inputs_nodup : inputs.Nodup := by decide +kernel
lemma literal_phase_index {a : Sig} (ha : a ∈ literals) :
    phase a = phase (raw.getD (index a).val zero) := by
  have h : literals.all (fun a => phase a == phase (raw.getD (index a).val zero)) = true := by decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp h a ha)
lemma every_class {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hne : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (h : Live k t (insert (bin d a b) U)) :
    ∀ i : Fin 9, ∃ z ∈ U, index z = i := by
  intro i
  by_contra hn
  have absent : ∀ z ∈ U, index z ≠ i := by
    intro z hz hi
    exact hn ⟨z, hz, hi⟩
  apply binary_missing i ha hb hne d
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨z,hz,hs⟩ := LiveCheck.live_sep h j hj
  have hx := LiveCheck.sep_weaken t z j hj hs
  rcases Finset.mem_insert.mp hz with rfl | hz
  · simp only [BitVec.getLsbD_or,hx,Bool.true_or,top,
      BitVec.getLsbD_allOnes,hj,decide_true]
  · have hm := congrArg (fun x : B => x.getLsbD j)
      (outside_mask i (hu z hz) (absent z hz))
    simp only [BitVec.getLsbD_or,hx,Bool.true_or] at hm
    simp only [BitVec.getLsbD_or,← hm,Bool.or_true,top,
      BitVec.getLsbD_allOnes,hj,decide_true]

lemma retained_perm {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hne : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (h : Live k t (insert (bin d a b) U))
    (hc : U.card = 9) : (U.toList.map phase).Perm inputs := by
  have sub : inputs ⊆ U.toList.map phase := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    obtain ⟨a, ha, hi⟩ := every_class ha hb hne hu h i
    exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, by rw [literal_phase_index (hu a ha), hi]⟩
  have hp := inputs_nodup.subperm sub
  have hl : inputs.length = (U.toList.map phase).length := by simp [inputs, hc]
  obtain ⟨w, pw, hw⟩ := hp
  have he : w = U.toList.map phase := hw.eq_of_length (by rw [pw.length_eq]; exact hl)
  exact he ▸ pw

set_option maxRecDepth 20000 in
lemma lower_eleven
    (checked : ∀ a ∈ literals, ∀ b ∈ literals, ∀ d,
      test 3 (phase (bin d a b) :: inputs) = false)
    {k t S} (h : Live k t S) :
    (∀ a ∈ S, a ∈ literals) → t+11 ≤ k := by
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
    have hc := retained_count ha' hb' hab hu tail
    have hsize := LiveCheck.live_size tail
    have fresh : bin d a b ∉ U :=
      fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    rw [Finset.card_insert_of_notMem fresh] at hsize
    have hu9 : U.card = 9 := by omega
    have ht : (insert (bin d a b) U).card + t = k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    have hp : (phase (bin d a b) :: inputs).Perm
        ((insert (bin d a b) U).toList.map phase) := by
      exact ((retained_perm ha' hb' hab hu tail hu9).symm.cons _).trans
        ((Finset.toList_insert fresh).map phase).symm
    have hh := tight_test tail ht 3 _ hp
    rw [checked a ha' b hb' d] at hh
    cases hh
end PEqualNP.Outside.L_meta_670_aux.TightFormula
