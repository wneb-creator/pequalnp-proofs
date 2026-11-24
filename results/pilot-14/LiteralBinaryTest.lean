import DynamicFastBase
namespace PEqualNP.Outside.L_meta_670_aux.LiveCheck
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 414
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 414 ≤ i)] at h

lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 414
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 414 ≤ i)] at h

lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 414 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 414)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

end PEqualNP.Outside.L_meta_670_aux.LiveCheck

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
