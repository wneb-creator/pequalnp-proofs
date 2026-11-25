namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma override_duplicate_step (n : Nat) (st : List Ref × Dag) (g : Gate)
    (a : Nat) (ha : g.inputs=[a,a]) : (na_step n st g).2.length=st.2.length := by
  simp only [na_step,ha]
  cases hr : na_look st.1 a with
  | inl b => cases b <;> cases ht : na_isAnd g.op <;> simp [na_comb]
  | inr k => simp [na_comb]

lemma override_fold_duplicate (n : Nat) (gs : List Gate) (st : List Ref × Dag)
    (duplicate : ∃ g ∈ gs, ∃ a,g.inputs=[a,a]) :
    (gs.foldl (na_step n) st).2.length < st.2.length+gs.length := by
  induction gs generalizing st with
  | nil => simp at duplicate
  | cons g gs ih =>
    obtain ⟨k,hk,a,ha⟩ := duplicate
    rw [List.foldl_cons,List.length_cons]
    rcases List.mem_cons.mp hk with rfl | hk
    · have zero := override_duplicate_step n st k a ha
      have bound := surgery_fold_count n gs (na_step n st k)
      have count := surgery_binaryCount_le gs
      omega
    · have strict := ih (na_step n st g) ⟨k,hk,a,ha⟩
      have bound := surgery_step_count n st g
      split at bound <;> omega

lemma override_strict_of_duplicate {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (duplicate : ∃ g ∈ C.gates, ∃ a,g.inputs=[a,a]) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length < C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp),?_⟩
    intro r hr
    simp only [List.mem_map,List.mem_range] at hr
    obtain ⟨k,hk,rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS,hok⟩,_,hsem⟩ := na_fold_spec n C.gates hmono _ h0
  have hcost := override_fold_duplicate n C.gates ((List.range n).map Sum.inr, ([] : Dag)) duplicate
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hsem hcost
  obtain ⟨m,D⟩ := st
  dsimp only at hS hok hsem hcost
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val,hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b,fun x => by rw [hev x,hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k,hkn⟩,fun x => by rw [hev x,hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k-n+1)).length = k-n+1 := by
        rw [List.length_take]
        omega
      refine Or.inr (Or.inr ⟨D.take (k-n+1),na_strict_take hS _,?_,?_,fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · change (D.take (k-n+1)).length < C.gates.length
        rw [hl]
        simp only [List.length_nil,Nat.zero_add] at hcost
        omega
      · have ho : outW n (D.take (k-n+1)) = k := by unfold outW; rw [hl]; omega
        rw [ho,val_take D x (k-n+1) k (by omega) (by omega),hev x,hr]
        rfl


end PEqualNP.Outside.L_meta_6659_aux
