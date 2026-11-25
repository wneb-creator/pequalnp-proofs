import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate) (hasNot : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre post : List Gate) (g : Gate),
      gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
        ∀ h ∈ post, h.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at hasNot
  | cons first rest ih =>
    by_cases tailHasNot : ∃ g ∈ rest, g.op = GateOp.not
    · obtain ⟨pre, post, g, eq, op, tail⟩ := ih tailHasNot
      exact ⟨first :: pre, post, g, by simp [eq], op, tail⟩
    · have firstNot : first.op = GateOp.not := by
        obtain ⟨g, mem, op⟩ := hasNot
        rcases List.mem_cons.mp mem with rfl | mem
        · exact op
        · exact (tailHasNot ⟨g, mem, op⟩).elim
      exact ⟨[], rest, first, rfl, firstNot, fun h mem op => tailHasNot ⟨h, mem, op⟩⟩

lemma gate_fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_singleton, List.length_cons]
    omega

lemma not_count_split (pre post : List Gate) (g : Gate) (gNot : g.op = GateOp.not)
    (postNot : ∀ h ∈ post, h.op ≠ GateOp.not) :
    PEqualNP.NotBracket.notCount (⟨pre ++ g :: post, 0⟩ : Circuit) =
      PEqualNP.NotBracket.notCount (⟨pre, 0⟩ : Circuit) + 1 := by
  let keep : Gate → Bool := fun h => @decide (h.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
  have dropPost : post.filter keep = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro h mem
    simp [keep, postNot h mem]
  have keepGate : keep g = true := by simp [keep, gNot]
  change ((pre ++ g :: post).filter keep).length = (pre.filter keep).length + 1
  rw [List.filter_append, List.filter_cons_of_pos keepGate, dropPost]
  simp

lemma cut_last_not_count (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      PEqualNP.NotBracket.notCount P + 1 = PEqualNP.NotBracket.notCount C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, post, g, split, gNot, postNot⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro h mem
    apply fan h
    rw [split]
    exact List.mem_append_left _ mem
  · intro h mem
    have legal := fan h (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    refine ⟨?_, legal.2⟩
    rcases legal.1 with op | op | op
    · exact Or.inl op
    · exact Or.inr op
    · exact (postNot h mem op).elim
  · change pre.length + post.length + 1 = C.gates.length
    rw [split]
    simp only [List.length_append, List.length_cons]
    omega
  · have count := not_count_split pre post g gNot postNot
    change PEqualNP.NotBracket.notCount (⟨pre, 0⟩ : Circuit) + 1 =
      PEqualNP.NotBracket.notCount (⟨C.gates, 0⟩ : Circuit)
    rw [split]
    exact count.symm
  · intro x
    let w := P.wires (List.ofFn x)
    have evalNot : g.op.eval (g.inputs.map fun i => w.getD i false) = !P.eval (List.ofFn x) := by
      rw [gNot]
      change (!(g.inputs.map fun i => w.getD i false).headD false) = !(w.getD P.output false)
      cases inputEq : g.inputs with
      | nil =>
        have len : w.length = n + pre.length := by
          change (pre.foldl _ (List.ofFn x)).length = _
          rw [gate_fold_length]
          simp
        have hout : P.output = n + pre.length := by simp [P, inputEq]
        change (!false) = !(w.getD P.output false)
        rw [hout, List.getD_eq_default _ _ (by omega)]
      | cons i rest =>
        have hout : P.output = i := by simp [P, inputEq]
        change !(w.getD i false) = !(w.getD P.output false)
        rw [hout]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [split, List.foldl_append, List.foldl_cons]
    change (post.foldl _ (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD C.output false = _
    rw [evalNot]
    rfl

lemma cut_last_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨P, Q, hp, hq, cost, count, same⟩ := cut_last_not_count n C fan hasNot
  exact ⟨P, Q, hp, hq, cost, same⟩

lemma monotone_of_not_count_zero (C : Circuit) (fan : FanInTwo C)
    (count : PEqualNP.NotBracket.notCount C = 0) : Monotone2 C := by
  intro g mem
  obtain ⟨allowed, arity⟩ := fan g mem
  refine ⟨?_, arity⟩
  rcases allowed with op | op | op
  · exact Or.inl op
  · exact Or.inr op
  · let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
    have survives : g ∈ C.gates.filter (fun h : Gate => decide (h.op = GateOp.not)) :=
      List.mem_filter.mpr ⟨mem, decide_eq_true op⟩
    have empty := List.length_eq_zero_iff.mp count
    rw [empty] at survives
    cases survives

lemma cut_only_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (unique : PEqualNP.NotBracket.notCount C = 1) :
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨P, Q, hp, hq, cost, count, same⟩ := cut_last_not_count n C fan hasNot
  have zero : PEqualNP.NotBracket.notCount P = 0 := by omega
  exact ⟨P, Q, monotone_of_not_count_zero P hp zero, hq, cost, same⟩

end PEqualNP.Outside.L_meta_2592_aux
