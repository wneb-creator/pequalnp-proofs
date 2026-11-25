namespace PEqualNP.Outside.L_meta_6659_aux

lemma first_false_filter_chain {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) {a b : Nat}
    (path : Relation.ReflTransGen (sem_step n D) a b)
    (start : val D x a = true) (finish : val D x b = false)
    (unbranched : ∀ w, Relation.ReflTransGen (sem_step n D) a w →
      val D x w = true → fanout D w ≤ 1) :
    ∃ j s, j < D.length ∧ sem_Chain n D a (src D (j,s)) ∧
      val D x (src D (j,s)) = true ∧ tag D j = true ∧
      val D x (src D (j,!s)) = false ∧ val D x (n+j) = false := by
  revert start unbranched
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro start _
    simp only [start,Bool.true_eq_false] at finish
  | @head a c step rest ih =>
    intro start unbranched
    by_cases nextTrue : val D x c = true
    · have remaining : ∀ w, Relation.ReflTransGen (sem_step n D) c w →
          val D x w = true → fanout D w ≤ 1 := by
        intro w reach value
        exact unbranched w (Relation.ReflTransGen.head step reach) value
      obtain ⟨j,s,hj,chain,value,tag,opposite,last⟩ := ih nextTrue remaining
      have one : fanout D a = 1 := Nat.le_antisymm
        (unbranched a Relation.ReflTransGen.refl start) (sem_step_fanout step)
      exact ⟨j,s,hj,Relation.ReflTransGen.head ⟨step,one⟩ chain,value,tag,opposite,last⟩
    · have nextFalse : val D x c = false := by
        cases value : val D x c <;> simp_all
      obtain ⟨j,s,hj,rfl,source⟩ := sem_step_iff.mp step
      have carried : val D x (src D (j,s)) = true := by rw [source]; exact start
      have operation := val_gate hS x j hj
      have andFalse : tag D j = true ∧ val D x (src D (j,!s)) = false := by
        cases ht : tag D j <;> cases s <;>
          simp only [src,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,
            Bool.not_true] at carried ⊢ <;>
          simp [ht,gop,carried,nextFalse] at operation ⊢ <;> exact operation
      refine ⟨j,s,hj,?_,carried,andFalse.1,andFalse.2,nextFalse⟩
      rw [source]
      exact Relation.ReflTransGen.refl

end PEqualNP.Outside.L_meta_6659_aux
