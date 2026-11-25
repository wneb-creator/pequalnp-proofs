import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962.Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this


lemma wire_input {n : Nat} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  change (run C.gates (List.ofFn x)).getD i.val false = _
  rw [run_getD _ _ _ (by simpa using i.isLt)]
  simp

lemma wire_gate {n : Nat} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool)
    (j : Nat) (hj : j < C.gates.length) :
    wval C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) :=
  cval_gate n C (List.ofFn x) (by simp) ao.2.1 j hj

lemma wire_all_true {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · exact wire_input C (fun _ => true) ⟨w, hn⟩
    · have hj : w-n < C.gates.length := by omega
      have wi : n + (w-n) = w := by omega
      rw [← wi, wire_gate C ao _ _ hj]
      have mem : gateAt C (w-n) ∈ C.gates := by
        rw [gateAt_eq C _ hj]
        exact List.getElem_mem _
      obtain ⟨a, b, ins⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
      have av : wval C (fun _ : Fin n => true) a = true := by
        have h := ao.2.1 (w-n) hj a (by simp [ins])
        exact ih a (by omega) (by omega)
      have bv : wval C (fun _ : Fin n => true) b = true := by
        have h := ao.2.1 (w-n) hj b (by simp [ins])
        exact ih b (by omega) (by omega)
      rcases ao.1 _ mem with op | op <;> simp [ins, op, av, bv, GateOp.eval]

lemma graph_unit_false {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : graphFun G ∅ (fun i => decide (i = a)) = false := by
  simp [graphFun]

lemma below_wire_gate {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (w : Nat) (hw : w < n + C.gates.length)
    (below : ∀ x, wval C x w = true → graphFun G ∅ x = true) :
    IsImpOperand G C w := by
  have hn : n ≤ w := by
    by_contra h
    have wn : w < n := by omega
    let a : Fin n := ⟨w, wn⟩
    have yes : wval C (fun i => decide (i = a)) w = true := by
      simpa using wire_input C (fun i => decide (i = a)) a
    have bad := below _ yes
    rw [graph_unit_false] at bad
    contradiction
  refine ⟨hn, ?_, fun _ => true, ?_⟩
  · intro x hx
    apply below x
    simpa only [gateVal, wval, Nat.add_sub_of_le hn] using hx
  · simpa only [gateVal, wval, Nat.add_sub_of_le hn] using wire_all_true C ao w hw

lemma opnd_member {n : Nat} (C : Circuit) (ao : IsAO2 n C) (j : Nat)
    (hj : j < C.gates.length) (b : Fin 2) : opnd C j b ∈ (gateAt C j).inputs := by
  have mem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C _ hj]
    exact List.getElem_mem _
  have len := ao.2.2 _ mem
  unfold opnd
  rw [List.getD_eq_getElem _ _ (by simpa only [len] using b.isLt)]
  exact List.getElem_mem _

lemma core_is_and {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (core : IsCore G C j) :
    (gateAt C j).op = GateOp.and := by
  have mem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C _ core.1]
    exact List.getElem_mem _
  rcases ao.1 _ mem with hand | hor
  · exact hand
  · exfalso
    apply core.2.2.1
    have operand (b : Fin 2) : IsImpOperand G C (opnd C j b) := by
      have member := opnd_member C ao j core.1 b
      have bound := ao.2.1 j core.1 _ member
      have hj := core.1
      apply below_wire_gate G C ao _ (by omega)
      intro x hx
      apply core.2.1.1 x
      change wval C x (n+j) = true
      rw [wire_gate C ao x j core.1, hor]
      simp only [GateOp.eval, List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨opnd C j b, member, hx⟩, rfl⟩
    exact ⟨operand 0, operand 1⟩

lemma core_has_nonimplicant_operand {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C) (j : Nat)
    (core : IsCore G C j) : ∃ b : Fin 2,
      ¬ (∀ x, wval C x (opnd C j b) = true → graphFun G ∅ x = true) := by
  by_contra all
  push_neg at all
  apply core.2.2.1
  have operand (b : Fin 2) : IsImpOperand G C (opnd C j b) := by
    have bound := ao.2.1 j core.1 _ (opnd_member C ao j core.1 b)
    have hj := core.1
    exact below_wire_gate G C ao _ (by omega) (all b)
  exact ⟨operand 0, operand 1⟩

end PEqualNP.Outside.L_meta_2962.Semantic
