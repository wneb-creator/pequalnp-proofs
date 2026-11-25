import PNPAccepted6659
namespace PEqualNP.Outside.L_meta_6659_aux

lemma single_reader_path_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : Relation.ReflTransGen (sem_step n D) a b) : a ≤ b := by
  induction path with
  | refl => rfl
  | tail path step ih => exact Nat.le_trans ih (Nat.le_of_lt (sem_step_lt hS step))

lemma single_reader_chain_le {n : ℕ} {D : Dag} (hS : Strict n D) {a b : ℕ}
    (path : sem_Chain n D a b) : a ≤ b :=
  single_reader_path_le hS (sem_rtg_mono (fun _ _ h => h.1) path)

lemma single_reader_other_unreachable {n : ℕ} {D : Dag} (hS : Strict n D)
    {v a b c : ℕ} (chain : sem_Chain n D v a)
    (last : sem_step n D a b) (one : fanout D a = 1)
    (other : sem_step n D c b) (different : c ≠ a) :
    ¬ Relation.ReflTransGen (sem_step n D) v c := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,first,rest⟩
    · exact different equal.symm
    · have same : b = z := sem_step_unique last first one
      have le := single_reader_path_le hS rest
      have lt := sem_step_lt hS other
      omega
  | @head start next first rest ih =>
    intro reach
    rcases Relation.ReflTransGen.cases_head reach with equal | ⟨z,initial,remaining⟩
    · have direct : sem_step n D start b := by simpa [equal] using other
      have same : next = b := sem_step_unique first.1 direct first.2
      have le := single_reader_chain_le hS rest
      have lt := sem_step_lt hS last
      omega
    · have same : next = z := sem_step_unique first.1 initial first.2
      subst z
      exact ih remaining

lemma single_reader_chain_hits {n : ℕ} {D : Dag} (hS : Strict n D)
    {a b : ℕ} (chain : sem_Chain n D a b) (P : ℕ → Prop) :
    ∀ w, Relation.ReflTransGen (fun u v => sem_step n D u v ∧ P v) a w →
      P a → b ≤ w → P b := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => intro w path start bound; exact start
  | @head a next step rest ih =>
    intro w path start bound
    rcases Relation.ReflTransGen.cases_head path with equal | ⟨z,first,remaining⟩
    · have increasing := sem_step_lt hS step.1
      have restLe := single_reader_chain_le hS rest
      omega
    · have same : next = z := sem_step_unique step.1 first.1 step.2
      subst z
      exact ih w remaining first.2 bound

end PEqualNP.Outside.L_meta_6659_aux
namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def surgery_binaryCount (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (2 ≤ g.inputs.length))).length

lemma surgery_binaryCount_cons (g : Gate) (gs : List Gate) :
    surgery_binaryCount (g :: gs) =
      surgery_binaryCount gs + if 2 ≤ g.inputs.length then 1 else 0 := by
  by_cases h : 2 ≤ g.inputs.length <;> simp [surgery_binaryCount,h]

lemma surgery_step_count (n : ℕ) (st : List Ref × Dag) (g : Gate) :
    (na_step n st g).2.length ≤
      st.2.length + if 2 ≤ g.inputs.length then 1 else 0 := by
  cases h : g.inputs with
  | nil => simp [na_step,h]
  | cons a rest =>
    cases rest with
    | nil => simp [na_step,h]
    | cons b rest =>
      simp only [na_step,h]
      split <;> simp

lemma surgery_fold_count (n : ℕ) (gs : List Gate) (st : List Ref × Dag) :
    (gs.foldl (na_step n) st).2.length ≤ st.2.length + surgery_binaryCount gs := by
  induction gs generalizing st with
  | nil => simp [surgery_binaryCount]
  | cons g gs ih =>
    have step := surgery_step_count n st g
    have tail := ih (na_step n st g)
    rw [List.foldl_cons,surgery_binaryCount_cons]
    omega

lemma surgery_binaryCount_le (gs : List Gate) : surgery_binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [surgery_binaryCount]
  | cons g gs ih =>
    rw [surgery_binaryCount_cons,List.length_cons]
    split <;> omega

lemma surgery_binaryCount_lt (gs : List Gate)
    (short : ∃ g ∈ gs, g.inputs.length ≤ 1) : surgery_binaryCount gs < gs.length := by
  induction gs with
  | nil => simp at short
  | cons g gs ih =>
    rw [surgery_binaryCount_cons,List.length_cons]
    by_cases hg : 2 ≤ g.inputs.length
    · have hs : ∃ k ∈ gs, k.inputs.length ≤ 1 := by
        obtain ⟨k,hk,hlen⟩ := short
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact ⟨k,hk,hlen⟩
      have := ih hs
      simp only [hg,ite_true]
      omega
    · have := surgery_binaryCount_le gs
      simp only [hg,ite_false]
      omega

lemma surgery_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ surgery_binaryCount C.gates ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp),?_⟩
    intro r hr
    simp only [List.mem_map,List.mem_range] at hr
    obtain ⟨k,hk,rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS,hok⟩,_,hsem⟩ := na_fold_spec n C.gates hmono _ h0
  have hcost := surgery_fold_count n C.gates ((List.range n).map Sum.inr, ([] : Dag))
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
      · rw [hl]
        simp only [List.length_nil,Nat.zero_add] at hcost
        omega
      · have ho : outW n (D.take (k-n+1)) = k := by unfold outW; rw [hl]; omega
        rw [ho,val_take D x (k-n+1) k (by omega) (by omega),hev x,hr]
        rfl

lemma surgery_one_short_gate {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (short : ∃ g ∈ C.gates, g.inputs.length ≤ 1) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length < C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  rcases surgery_strict_of_monotone2 C hmono with constant | input | ⟨D,hS,hne,hlen,hval⟩
  · exact Or.inl constant
  · exact Or.inr (Or.inl input)
  · exact Or.inr (Or.inr ⟨D,hS,hne,lt_of_le_of_lt hlen (surgery_binaryCount_lt _ short),hval⟩)

end PEqualNP.Outside.L_meta_6659_aux
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
namespace PEqualNP.Outside.L_meta_6659_aux

lemma override_val_gate_bounded {n : Nat} {D : Dag} (x : Fin n → Bool) (j : Nat)
    (hj : j < D.length) (ha : opA D j < n+j) (hb : opB D j < n+j) :
    val D x (n+j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  have equation := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at equation
  unfold val
  rw [equation,wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

def overrideAlias (D : Dag) (edit : Nat) : Dag :=
  List.ofFn (fun j : Fin D.length =>
    if j.val=edit then (false,opB D edit,opB D edit) else D[j])

lemma overrideAlias_length (D : Dag) (edit : Nat) :
    (overrideAlias D edit).length = D.length := by simp [overrideAlias]

lemma overrideAlias_gate (D : Dag) (edit j : Nat) (hj : j < D.length) :
    tag (overrideAlias D edit) j = (if j=edit then false else tag D j) ∧
    opA (overrideAlias D edit) j = (if j=edit then opB D edit else opA D j) ∧
    opB (overrideAlias D edit) j = (if j=edit then opB D edit else opB D j) := by
  have bound : j < (overrideAlias D edit).length := by simpa [overrideAlias_length] using hj
  rw [tag_eq _ _ bound,opA_eq _ _ bound,opB_eq _ _ bound,
    tag_eq _ _ hj,opA_eq _ _ hj,opB_eq _ _ hj]
  simp only [overrideAlias,List.getElem_ofFn]
  split <;> simp_all

lemma overrideAlias_trace {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) :
    GateOverride n D x edit (val (overrideAlias D edit) x) := by
  refine ⟨fun w hw => val_input _ _ w hw,?_,?_⟩
  · intro j hj different
    have facts := overrideAlias_gate D edit j hj
    simp only [ite_eq_right different] at facts
    rw [override_val_gate_bounded (D := overrideAlias D edit) x j (by simpa [overrideAlias_length] using hj)
      (by rw [facts.2.1]; exact (hS j hj).1)
      (by rw [facts.2.2]; exact (hS j hj).2.1),facts.1,facts.2.1,facts.2.2]
  · intro w hw
    exact val_ge _ x w (by simpa [overrideAlias_length] using hw)

lemma overrideAlias_value {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (he : edit < D.length) :
    val (overrideAlias D edit) x (n+edit) = val (overrideAlias D edit) x (opB D edit) := by
  have facts := overrideAlias_gate D edit edit he
  simp only at facts
  rw [override_val_gate_bounded (D := overrideAlias D edit) x edit (by simpa [overrideAlias_length] using he)
    (by rw [facts.2.1]; exact (hS edit he).2.1)
    (by rw [facts.2.2]; exact (hS edit he).2.1),facts.1,facts.2.1,facts.2.2]
  simp [gop]

end PEqualNP.Outside.L_meta_6659_aux
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
namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def overrideOfficialGate (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def overrideOfficial (D : Dag) (output : ℕ) : Circuit :=
  ⟨D.map overrideOfficialGate, output⟩

lemma overrideOfficial_size (D : Dag) (output : ℕ) : (overrideOfficial D output).size = D.length := by
  simp [overrideOfficial, Circuit.size]

lemma overrideOfficial_monotone (D : Dag) (output : ℕ) : Monotone2 (overrideOfficial D output) := by
  intro g hg
  obtain ⟨⟨t,a,b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases t <;> simp [overrideOfficialGate]

lemma overrideOfficial_fold (D : Dag) (x : List Bool) :
    (D.map overrideOfficialGate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = wl D x := by
  induction D generalizing x with
  | nil => rfl
  | cons g D ih =>
    obtain ⟨t,a,b⟩ := g
    cases t
    · simpa [overrideOfficialGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop false (x.getD a false) (x.getD b false)])
    · simpa [overrideOfficialGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop true (x.getD a false) (x.getD b false)])

lemma overrideOfficial_wires (D : Dag) (output : ℕ) (x : List Bool) :
    (overrideOfficial D output).wires x = wl D x := overrideOfficial_fold D x

lemma overrideOfficial_eval (D : Dag) (output : ℕ) {n : ℕ} (x : Fin n → Bool) :
    (overrideOfficial D output).eval (List.ofFn x) = val D x output := by
  rw [Circuit.eval, overrideOfficial_wires]
  rfl

lemma overrideAlias_smaller {n : Nat} {D : Dag} (edit : Nat) (he : edit < D.length)
    (output : Nat) :
    (∃ b : Bool, ∀ x : Fin n → Bool,val (overrideAlias D edit) x output=b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool,val (overrideAlias D edit) x output=x i) ∨
    (∃ E : Dag,Strict n E ∧ E≠[] ∧ E.length<D.length ∧
      ∀ x : Fin n → Bool,val E x (outW n E)=val (overrideAlias D edit) x output) := by
  let C := overrideOfficial (overrideAlias D edit) output
  have duplicate : ∃ g ∈ C.gates, ∃ a,g.inputs=[a,a] := by
    have bound : edit < (overrideAlias D edit).length := by simpa [overrideAlias_length] using he
    refine ⟨overrideOfficialGate ((overrideAlias D edit)[edit]),?_,opB D edit,?_⟩
    · apply List.mem_map.mpr
      exact ⟨_,List.getElem_mem bound,rfl⟩
    · simp [overrideOfficialGate,overrideAlias]
  rcases override_strict_of_duplicate C (overrideOfficial_monotone _ _) duplicate with
    constant | input | ⟨E,strict,nonempty,size,correct⟩
  · obtain ⟨b,hb⟩ := constant
    exact Or.inl ⟨b,fun x => (overrideOfficial_eval _ output x).symm.trans (hb x)⟩
  · obtain ⟨i,hi⟩ := input
    exact Or.inr (Or.inl ⟨i,fun x => (overrideOfficial_eval _ output x).symm.trans (hi x)⟩)
  · have size' : E.length < D.length := by
      simpa only [C,overrideOfficial_size,overrideAlias_length] using size
    exact Or.inr (Or.inr ⟨E,strict,nonempty,size',fun x =>
      (correct x).trans (overrideOfficial_eval _ output x)⟩)

end PEqualNP.Outside.L_meta_6659_aux
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
