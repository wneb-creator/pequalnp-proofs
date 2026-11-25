lemma not_inputs_eval (gs : List Gate) (ins : List Nat) (n : Nat) (x : Fin n → Bool) :
    GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false) =
      !(Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) := by
  cases ins with
  | nil =>
    have hlen := wf_len gs (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    change true = !(wf gs (List.ofFn x)).getD (n + gs.length) false
    rw [List.getD_eq_default _ _ (by omega)]
    rfl
  | cons j ins => rfl

lemma output_not_eval_all (gs : List Gate) (ins : List Nat) (n : Nat) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) =
      !(Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) := by
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change ((wf gs (List.ofFn x)) ++
    [GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false)]).getD
    (n + gs.length) false = _
  have hlen := wf_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  have reading := getD_snoc_eq (wf gs (List.ofFn x))
    (GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false))
  rw [hlen] at reading
  exact reading.trans (not_inputs_eval gs ins n x)

lemma insert_not_wires (before : List Gate) (ins : List Nat) (after : List Gate)
    (n : Nat) (x : Fin n → Bool) :
    wf (before ++ ⟨GateOp.not, ins⟩ :: after) (List.ofFn x) =
      wf after (wf before (List.ofFn x) ++
        [!(Circuit.mk before (ins.headD (n + before.length))).eval (List.ofFn x)]) := by
  unfold wf
  rw [List.foldl_append]
  change wf after (wf before (List.ofFn x) ++
    [GateOp.not.eval (ins.map fun i => (wf before (List.ofFn x)).getD i false)]) = _
  rw [not_inputs_eval]
  rfl

lemma split_unique_not (gs : List Gate)
    (count : PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 1) :
    ∃ before g after, gs = before ++ g :: after ∧ g.op = GateOp.not ∧
      (∀ a ∈ before, a.op ≠ GateOp.not) ∧ (∀ a ∈ after, a.op ≠ GateOp.not) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  let isN := fun a : Gate => decide (a.op = GateOp.not)
  have hc : (gs.filter isN).length = 1 := count
  obtain ⟨g, hg⟩ : ∃ g, g ∈ gs.filter isN := by
    cases h : gs.filter isN with
    | nil => simp [h] at hc
    | cons a rest => exact ⟨a, by simp [h]⟩
  obtain ⟨member, yes⟩ := List.mem_filter.mp hg
  have gn : g.op = GateOp.not := by simpa [isN] using yes
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have parts : (before.filter isN).length + 1 + (after.filter isN).length = 1 := by
    simpa [split, List.filter_append, isN, gn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
  have none (l : List Gate) (zero : (l.filter isN).length = 0) :
      ∀ a ∈ l, a.op ≠ GateOp.not := by
    intro a ha hn
    have ha' : a ∈ l.filter isN := by simp [ha, isN, hn]
    have positive := List.length_pos_of_mem ha'
    omega
  exact ⟨before, g, after, split, gn, none before (by omega), none after (by omega)⟩

lemma two_not_output_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (gs : List Gate) (ins : List Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 2)
    (computes : ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) = f x) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 2 ≤ (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).size ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have countGs : PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 1 := by
    simpa [PEqualNP.NotBracket.notCount, List.filter_append] using count
  obtain ⟨before, g, after, split, gn, beforeNot, afterNot⟩ := split_unique_not gs countGs
  have geq : g = ⟨GateOp.not, g.inputs⟩ := by cases g; simp_all
  let P : Circuit := ⟨before, g.inputs.headD (n + before.length)⟩
  let Q : Circuit := ⟨after, ins.headD (n + gs.length)⟩
  have beforeFan (a : Gate) (ha : a ∈ before) :
      a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
    apply legal a
    apply List.mem_append_left
    rw [split]
    exact List.mem_append_left _ ha
  have afterFan (a : Gate) (ha : a ∈ after) :
      a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
    apply legal a
    apply List.mem_append_left
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
  have pMono : ∀ a ∈ P.gates, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    have hop := (beforeFan a ha).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (beforeNot a ha h)
  have qMono : ∀ a ∈ Q.gates, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    have hop := (afterFan a ha).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (afterNot a ha h)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨pMono a ha, (beforeFan a ha).2⟩
  · simp only [Circuit.size, P, split, List.length_append, List.length_cons, List.length_nil]
    omega
  · apply two_not_terminal_reduces n f bottom top P Q pMono qMono
    intro x
    have original := computes x
    rw [output_not_eval_all] at original
    have middle : (Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
      change (wf gs (List.ofFn x)).getD (ins.headD (n + gs.length)) false =
        (wf after (wf before (List.ofFn x) ++
          [!(Circuit.mk before (g.inputs.headD (n + before.length))).eval (List.ofFn x)])).getD
            (ins.headD (n + gs.length)) false
      rw [split, geq, insert_not_wires]
    rw [middle] at original
    exact original
