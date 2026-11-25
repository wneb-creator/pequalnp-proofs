namespace PEqualNP.Outside.L_meta_6659_aux

lemma consuming_ancestors_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k)
    (target : Nat)
    (consumers : ∀ e ∈ sem_W n D i,
      Relation.ReflTransGen (sem_step n D) (n + e.1) target →
      val D x (n + e.1) = val D y (n + e.1)) :
    i ∉ supp n D target → val D x target = val D y target := by
  have aux : ∀ w, Relation.ReflTransGen (sem_step n D) w target →
      i ∉ supp n D w → val D x w = val D y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro reach absent
      by_cases input : w < n
      · rw [supp_input D ⟨w,input⟩] at absent
        have ne : (⟨w,input⟩ : Fin n) ≠ i := by
          intro eq
          apply absent
          simpa only [eq] using Finset.mem_singleton_self i
        rw [val_input D x w input,val_input D y w input]
        exact inputs _ ne
      · by_cases valid : w < n + D.length
        · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha,hb,_⟩ := hS j hj
          by_cases carryA : i ∈ supp n D (opA D j)
          · apply consumers (j,false) _ reach
            apply sem_mem_W.mpr
            exact ⟨hj,by simpa only [src,Bool.false_eq_true,ite_false] using carryA,absent⟩
          · by_cases carryB : i ∈ supp n D (opB D j)
            · apply consumers (j,true) _ reach
              apply sem_mem_W.mpr
              exact ⟨hj,by simpa only [src,ite_true] using carryB,absent⟩
            · have stepA : sem_step n D (opA D j) (n+j) := by
                simpa only [src,Bool.false_eq_true,ite_false] using (sem_step_src (n := n) hj false)
              have stepB : sem_step n D (opB D j) (n+j) := by
                simpa only [src,ite_true] using (sem_step_src (n := n) hj true)
              rw [val_gate hS x j hj,val_gate hS y j hj,
                ih _ ha (Relation.ReflTransGen.head stepA reach) carryA,
                ih _ hb (Relation.ReflTransGen.head stepB reach) carryB]
        · rw [val_ge D x w (by omega),val_ge D y w (by omega)]

  exact aux target Relation.ReflTransGen.refl

lemma consuming_gates_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) (i : Fin n)
    (inputs : ∀ k, k ≠ i → x k = y k)
    (consumers : ∀ e ∈ sem_W n D i,
      val D x (n + e.1) = val D y (n + e.1)) :
    ∀ w, i ∉ supp n D w → val D x w = val D y w :=
  fun w => consuming_ancestors_agreement hS x y i inputs w (fun e he _ => consumers e he)

end PEqualNP.Outside.L_meta_6659_aux
