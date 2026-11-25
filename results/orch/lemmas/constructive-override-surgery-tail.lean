namespace PEqualNP.Outside.L_meta_6659_aux

lemma override_smaller_of_barriers {n : Nat} {D : Dag} (hS : Strict n D)
    (edit : Nat) (he : edit<D.length) (andGate : tag D edit=true) (output : Nat)
    (safe : ∀ x : Fin n → Bool,val D x output=false →
      val D x (opA D edit)=true ∨
      ∃ j side,j<D.length ∧ j≠edit ∧ tag D j=true ∧
        (¬ Relation.ReflTransGen (sem_step n D) (n+edit) (src D (j,side))) ∧
        val D x (src D (j,side))=false ∧
        sem_Chain n D (n+edit) (n+j) ∧ n+j≤output) :
    (∃ b : Bool,∀ x : Fin n → Bool,val D x output=b) ∨
    (∃ i : Fin n,∀ x : Fin n → Bool,val D x output=x i) ∨
    (∃ E : Dag,Strict n E ∧ E≠[] ∧ E.length<D.length ∧
      ∀ x : Fin n → Bool,val E x (outW n E)=val D x output) := by
  have equivalent : ∀ x : Fin n → Bool,
      val (overrideAlias D edit) x output=val D x output := by
    intro x
    have trace := overrideAlias_trace hS x edit
    have aliasEq := overrideAlias_value hS x edit he
    cases original : val D x output with
    | true =>
      exact override_alias_increases hS x edit _ trace andGate aliasEq output original
    | false =>
      rcases safe x original with leftTrue | ⟨j,side,hj,different,operation,unreachable,zero,chain,after⟩
      · simpa only [original] using
          (override_alias_left_true hS x edit _ trace he andGate aliasEq leftTrue output).symm
      · simpa only [original] using (override_and_barrier hS x edit _ trace j hj different operation side
          unreachable zero chain output after).symm
  rcases overrideAlias_smaller (n := n) (D := D) edit he output with
    constant | input | ⟨E,strict,nonempty,size,correct⟩
  · obtain ⟨b,hb⟩ := constant
    exact Or.inl ⟨b,fun x => (equivalent x).symm.trans (hb x)⟩
  · obtain ⟨i,hi⟩ := input
    exact Or.inr (Or.inl ⟨i,fun x => (equivalent x).symm.trans (hi x)⟩)
  · exact Or.inr (Or.inr ⟨E,strict,nonempty,size,fun x => (correct x).trans (equivalent x)⟩)

end PEqualNP.Outside.L_meta_6659_aux
