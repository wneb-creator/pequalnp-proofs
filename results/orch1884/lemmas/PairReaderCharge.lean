import ElimManyCount

namespace PEqualNP.Outside.L_meta_1884.PairReaderCharge

open PEqualNP.CircuitLowerBounds ElimManyCount

lemma count_one {α : Type} (p : α → Bool) (l : List α) (a : α)
    (ha : a ∈ l) (hpa : p a = true) : 1 ≤ l.countP p := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [List.countP_cons, hpa, ↓reduceIte]
      omega
    · have h := ih ha
      cases hp : p c <;>
        simp only [List.countP_cons, hp, Bool.false_eq_true, ↓reduceIte] <;> omega

lemma count_two {α : Type} (p : α → Bool) (l : List α) (a b : α)
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ l.countP p := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hca : c = a
    · subst c
      have hbl : b ∈ l := by
        rcases List.mem_cons.mp hb with h | h
        · exact False.elim (hab h.symm)
        · exact h
      have hc := count_one p l b hbl hpb
      simp only [List.countP_cons, hpa, ↓reduceIte]
      omega
    · by_cases hcb : c = b
      · subst c
        have hal : a ∈ l := by
          rcases List.mem_cons.mp ha with h | h
          · exact False.elim (hab h)
          · exact h
        have hc := count_one p l a hal hpa
        simp only [List.countP_cons, hpb, ↓reduceIte]
        omega
      · have hal : a ∈ l := by simpa [Ne.symm hca] using ha
        have hbl : b ∈ l := by simpa [Ne.symm hcb] using hb
        have hc := ih hal hbl
        cases hp : p c <;>
          simp only [List.countP_cons, hp, Bool.false_eq_true, ↓reduceIte] <;> omega

lemma count_split {α : Type} (p q : α → Bool) (l : List α)
    (hle : ∀ a ∈ l, p a = true → q a = true) :
    l.countP q = l.countP p + l.countP (fun a => q a && !p a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hi := ih (fun b hb => hle b (List.mem_cons_of_mem _ hb))
    have h := hle a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.countP_cons, hp, hq, Bool.not_false, Bool.not_true,
        Bool.true_and, Bool.false_and, ↓reduceIte] <;> simp_all <;> omega

theorem pair_charge (K : Finset Nat) (q : Nat) (pre post : List Gate) (a b : Gate)
    (hbase : 2 ≤ pre.countP (reads K) + post.countP (reads K))
    (ha : a ∈ post) (hb : b ∈ post) (hab : a ≠ b)
    (ha0 : reads K a = false) (hb0 : reads K b = false)
    (ha1 : reads (insert q K) a = true) (hb1 : reads (insert q K) b = true) :
    4 ≤ pre.countP (reads K) + post.countP (reads (insert q K)) := by
  have hle : ∀ g ∈ post, reads K g = true → reads (insert q K) g = true := by
    intro g _ hg
    obtain ⟨i, hi, hiK⟩ := List.any_eq_true.mp hg
    apply List.any_eq_true.mpr
    refine ⟨i,hi,?_⟩
    simp only [decide_eq_true_eq]
    exact Finset.mem_insert_of_mem (of_decide_eq_true hiK)
  have heq := count_split (reads K) (reads (insert q K)) post hle
  have ht := count_two (fun g => reads (insert q K) g && !reads K g) post a b ha hb hab
    (by simp [ha0,ha1]) (by simp [hb0,hb1])
  omega

theorem direct_filters (K : Finset Nat) (q v w : Nat) (pre post : List Gate)
    (hq : q ∉ K) (hv : v ∉ K) (hw : w ∉ K) (hvw : v ≠ w)
    (hbase : 2 ≤ pre.countP (reads K) + post.countP (reads K))
    (hvpost : (⟨GateOp.and,[v,q]⟩ : Gate) ∈ post)
    (hwpost : (⟨GateOp.and,[w,q]⟩ : Gate) ∈ post) :
    4 ≤ pre.countP (reads K) + post.countP (reads (insert q K)) := by
  apply pair_charge K q pre post ⟨GateOp.and,[v,q]⟩ ⟨GateOp.and,[w,q]⟩ hbase
    hvpost hwpost
  · intro h
    have hi := congrArg Gate.inputs h
    simp only [List.cons.injEq] at hi
    exact hvw hi.1
  · simp [reads,hv,hq]
  · simp [reads,hw,hq]
  · simp [reads]
  · simp [reads]

end PEqualNP.Outside.L_meta_1884.PairReaderCharge
