namespace PEqualNP.Outside.L_meta_6659_aux

abbrev GateOverride (n : Nat) (D : Dag) (x : Fin n → Bool) (edit : Nat)
    (f : Nat → Bool) : Prop :=
  (∀ w (hw : w < n), f w = x ⟨w,hw⟩) ∧
  (∀ j, j < D.length → j ≠ edit →
    f (n+j) = gop (tag D j) (f (opA D j)) (f (opB D j))) ∧
  (∀ w, n+D.length ≤ w → f w = false)

lemma override_changed_path {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (w : Nat)
    (changed : val D x w ≠ f w) :
    val D x (n+edit) ≠ f (n+edit) ∧
      Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ f b)
        (n+edit) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · exact False.elim (changed ((val_input D x w input).trans (trace.1 w input).symm))
    · by_cases bound : w < n+D.length
      · obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
        have hj : j < D.length := by omega
        by_cases same : j=edit
        · subst j
          exact ⟨changed,Relation.ReflTransGen.refl⟩
        · obtain ⟨ha,hb,_⟩ := hS j hj
          have outputs := changed
          rw [val_gate hS x j hj,trace.2.1 j hj same] at outputs
          by_cases first : val D x (opA D j) = f (opA D j)
          · have second : val D x (opB D j) ≠ f (opB D j) := by
              intro equal
              exact outputs (by rw [first,equal])
            obtain ⟨initial,path⟩ := ih _ hb second
            exact ⟨initial,Relation.ReflTransGen.tail path ⟨sem_step_src hj true,changed⟩⟩
          · obtain ⟨initial,path⟩ := ih _ ha first
            exact ⟨initial,Relation.ReflTransGen.tail path ⟨sem_step_src hj false,changed⟩⟩
      · exact False.elim (changed ((val_ge D x w (by omega)).trans
          (trace.2.2 w (by omega)).symm))

lemma override_agree_of_unreachable {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (w : Nat)
    (unreachable : ¬ Relation.ReflTransGen (sem_step n D) (n+edit) w) :
    val D x w = f w := by
  by_contra changed
  exact unreachable (sem_rtg_mono (fun _ _ h => h.1)
    (override_changed_path hS x edit f trace w changed).2)

lemma override_agree_before {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (w : Nat) (before : w < n+edit) :
    val D x w = f w := by
  apply override_agree_of_unreachable hS x edit f trace w
  intro path
  have order := single_reader_path_le hS path
  omega

lemma override_agree_if_initial {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f)
    (same : val D x (n+edit) = f (n+edit)) : ∀ w,val D x w = f w := by
  intro w
  by_contra changed
  exact (override_changed_path hS x edit f trace w changed).1 same

lemma override_chain_agreement {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (barrier : Nat)
    (chain : sem_Chain n D (n+edit) barrier)
    (same : val D x barrier = f barrier) (target : Nat) (after : barrier ≤ target) :
    val D x target = f target := by
  by_contra changed
  obtain ⟨initial,path⟩ := override_changed_path hS x edit f trace target changed
  exact (single_reader_chain_hits hS chain (fun w => val D x w ≠ f w)
    target path initial after) same

lemma override_alias_left_true {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (he : edit < D.length)
    (andGate : tag D edit = true) (aliasEq : f (n+edit) = f (opB D edit))
    (leftTrue : val D x (opA D edit) = true) : ∀ w,val D x w = f w := by
  apply override_agree_if_initial hS x edit f trace
  rw [val_gate hS x edit he,andGate,leftTrue,aliasEq]
  simpa [gop] using override_agree_before hS x edit f trace _ (hS edit he).2.1

lemma override_and_barrier {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (j : Nat) (hj : j < D.length)
    (different : j ≠ edit) (andGate : tag D j = true) (side : Bool)
    (unreachable : ¬ Relation.ReflTransGen (sem_step n D) (n+edit) (src D (j,side)))
    (zero : val D x (src D (j,side)) = false)
    (chain : sem_Chain n D (n+edit) (n+j))
    (target : Nat) (after : n+j ≤ target) : val D x target = f target := by
  have modifiedZero : f (src D (j,side)) = false :=
    (override_agree_of_unreachable hS x edit f trace _ unreachable).symm.trans zero
  apply override_chain_agreement hS x edit f trace (n+j) chain _ target after
  rw [val_gate hS x j hj,trace.2.1 j hj different,andGate]
  cases side <;> simp only [src,Bool.false_eq_true,ite_false,ite_true] at zero modifiedZero
    <;> simp [gop,zero,modifiedZero]

lemma override_alias_increases {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (f : Nat → Bool)
    (trace : GateOverride n D x edit f) (andGate : tag D edit=true)
    (aliasEq : f (n+edit)=f (opB D edit)) :
    ∀ w,val D x w=true → f w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro positive
    by_cases input : w<n
    · rw [trace.1 w input]
      exact (val_input D x w input).symm.trans positive
    · by_cases bound : w<n+D.length
      · obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
        have hj : j<D.length := by omega
        obtain ⟨ha,hb,_⟩ := hS j hj
        rw [val_gate hS x j hj] at positive
        by_cases same : j=edit
        · subst j
          rw [andGate,gop_true,Bool.and_eq_true] at positive
          rw [aliasEq]
          exact ih _ hb positive.2
        · rw [trace.2.1 j hj same]
          cases operation : tag D j with
          | false =>
            rw [operation,gop_false,Bool.or_eq_true] at positive
            rw [gop_false,Bool.or_eq_true]
            rcases positive with first | second
            · exact Or.inl (ih _ ha first)
            · exact Or.inr (ih _ hb second)
          | true =>
            rw [operation,gop_true,Bool.and_eq_true] at positive
            rw [gop_true,Bool.and_eq_true]
            exact ⟨ih _ ha positive.1,ih _ hb positive.2⟩
      · rw [val_ge D x w (by omega)] at positive
        exact False.elim (Bool.noConfusion positive)

end PEqualNP.Outside.L_meta_6659_aux
