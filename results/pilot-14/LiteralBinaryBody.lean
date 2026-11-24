namespace PEqualNP.Outside.L_meta_670_aux.LiteralBinary

open LiveCheck

def literals : List Sig := raw ++ raw.map neg

def index (a : Sig) : Fin 9 := Fin.ofNat 9 (literals.idxOf a)

def missing (i : Fin 9) : B := unionSep true
  (((List.finRange 9).filter fun j => j != i).map fun j => raw.getD j.val zero)

def obstruction (i : Fin 9) : Bool :=
  (literals.all fun a => index a == i || (sep true a ||| missing i) == missing i) &&
  (literals.all fun a => literals.all fun b => a == b ||
    ((sep true (bin false a b) ||| missing i) != top &&
     (sep true (bin true a b) ||| missing i) != top))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check0 : obstruction 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check1 : obstruction 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check2 : obstruction 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check3 : obstruction 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check4 : obstruction 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check5 : obstruction 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check6 : obstruction 6 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check7 : obstruction 7 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check8 : obstruction 8 = true := by decide +kernel

lemma obstruction_checked (i : Fin 9) : obstruction i = true := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8

lemma outside_mask (i : Fin 9) {a : Sig} (ha : a ∈ literals) (hi : index a ≠ i) :
    sep true a ||| missing i = missing i := by
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (obstruction_checked i)).1 a ha
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  exact h.resolve_left hi

lemma binary_missing (i : Fin 9) {a b : Sig}
    (ha : a ∈ literals) (hb : b ∈ literals) (hne : a ≠ b) (d : Bool) :
    sep true (bin d a b) ||| missing i ≠ top := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (obstruction_checked i)).2 a ha) b hb
  simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at h
  have hh := h.resolve_left hne
  cases d
  · exact hh.1
  · exact hh.2

lemma neg_literal {a : Sig} (ha : a ∈ literals) : neg a ∈ literals := by
  rcases List.mem_append.mp ha with ha | ha
  · exact List.mem_append_right _ (List.mem_map_of_mem ha)
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    have hn : neg (neg b) = b := by simp only [neg,BitVec.not_not]
    rw [hn]
    exact List.mem_append_left _ hb

lemma target_not_literal : target ∉ literals := by decide +kernel

lemma retained_count {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hne : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (h : Live k t (insert (bin d a b) U)) :
    9 ≤ U.card := by
  have every : ∀ i : Fin 9, ∃ z ∈ U, index z = i := by
    intro i
    by_contra hn
    have absent : ∀ z ∈ U, index z ≠ i := by
      intro z hz hi
      exact hn ⟨z,hz,hi⟩
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
  have he : U.image index = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Finset.mem_image.mpr (every i)
  have hc := Finset.card_image_le (f := index) (s := U)
  rw [he] at hc
  simpa using hc

lemma lower {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    (∀ a ∈ S, a ∈ literals) → t+10 ≤ k := by
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
    have hu : ∀ z ∈ U, z ∈ literals :=
      fun z hz => hs z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    have hc := retained_count (hs a (Finset.mem_insert_self _ _))
      (hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) hab hu tail
    have hsize := LiveCheck.live_size tail
    have fresh : bin d a b ∉ U :=
      fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    rw [Finset.card_insert_of_notMem fresh] at hsize
    omega

lemma high_nots {t : Nat} (ht : 6 ≤ t) : Impossible 15 t raw := by
  intro k hk h
  have hb := lower h (fun a ha => List.mem_append_left _ (List.mem_toFinset.mp ha))
  omega

end PEqualNP.Outside.L_meta_670_aux.LiteralBinary
