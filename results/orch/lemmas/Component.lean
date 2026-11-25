namespace component

def ClosedCore : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs =>
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs ≠ [] ∧
        (∀ i ∈ g.inputs, i < n) ∧ ClosedCore (n + 1) gs

lemma gate_join (u : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (xs : List Bool) (hx : xs ≠ []) :
    op.eval (xs.map fun b => u || b) = (u || op.eval xs) := by
  cases xs with
  | nil => contradiction
  | cons b bs => cases u <;> rcases hop with rfl | rfl <;> simp [GateOp.eval]

lemma getD_map_join (w : List Bool) (u : Bool) (i : ℕ) (hi : i < w.length) :
    (w.map fun b => u || b).getD i false = (u || w.getD i false) := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma wf_join (gs : List Gate) (w : List Bool) (u : Bool) (h : ClosedCore w.length gs) :
    wf gs (w.map fun b => u || b) = (wf gs w).map (fun b => u || b) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, hne, hread, htail⟩ := h
    have hmap : g.inputs.map (fun i => (w.map fun b => u || b).getD i false) =
        (g.inputs.map fun i => w.getD i false).map (fun b => u || b) := by
      rw [List.map_map]
      exact List.map_congr_left fun i hi => getD_map_join w u i (hread i hi)
    have heval : g.op.eval (g.inputs.map fun i => (w.map fun b => u || b).getD i false) =
        (u || g.op.eval (g.inputs.map fun i => w.getD i false)) := by
      rw [hmap]
      exact gate_join u g.op hop _ (by simpa using hne)
    change wf gs (_ ++ [_]) = (wf gs (w ++ [_])).map _
    rw [heval]
    have happ : w.map (fun b => u || b) ++ [u || g.op.eval (g.inputs.map fun i => w.getD i false)] =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map (fun b => u || b) := by
      simp
    rw [happ]
    exact ih _ (by simpa using htail)

def shiftGate (d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => d + i⟩

lemma getD_shift (pre w : List Bool) (i : ℕ) :
    (pre ++ w).getD (pre.length + i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma wf_shift (gs : List Gate) (pre w : List Bool) :
    wf (gs.map (shiftGate pre.length)) (pre ++ w) = pre ++ wf gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hmap : (shiftGate pre.length g).inputs.map
        (fun i => (pre ++ w).getD i false) = g.inputs.map (fun i => w.getD i false) := by
      simp only [shiftGate, List.map_map]
      exact List.map_congr_left fun i _ => getD_shift pre w i
    change wf (gs.map (shiftGate pre.length))
        ((pre ++ w) ++ [(shiftGate pre.length g).op.eval _]) = pre ++ wf gs (w ++ [_])
    rw [hmap]
    change wf (gs.map (shiftGate pre.length))
        ((pre ++ w) ++ [g.op.eval _]) = pre ++ wf gs (w ++ [_])
    rw [List.append_assoc]
    exact ih _

def boundaryGates (outs : List ℕ) : List Gate :=
  outs.map fun i => ⟨GateOp.or, [0, 1 + i]⟩

lemma wf_boundary (outs : List ℕ) (w : List Bool) (hzero : 0 < w.length)
    (hread : ∀ i ∈ outs, 1 + i < w.length) :
    wf (boundaryGates outs) w =
      w ++ outs.map (fun i => w.getD 0 false || w.getD (1 + i) false) := by
  induction outs generalizing w with
  | nil => simp [boundaryGates, wf]
  | cons i outs ih =>
    have hi := hread i List.mem_cons_self
    let b := w.getD 0 false || w.getD (1 + i) false
    have hstep : wf (boundaryGates (i :: outs)) w = wf (boundaryGates outs) (w ++ [b]) := by
      simp [boundaryGates, wf, b, GateOp.eval]
    rw [hstep, ih (w ++ [b]) (by simp) (by
      intro j hj
      have := hread j (List.mem_cons_of_mem i hj)
      simp; omega)]
    have hm : outs.map (fun j => (w ++ [b]).getD 0 false || (w ++ [b]).getD (1 + j) false) =
        outs.map (fun j => w.getD 0 false || w.getD (1 + j) false) := by
      apply List.map_congr_left
      intro j hj
      rw [List.getD_append _ _ _ _ hzero,
        List.getD_append _ _ _ _ (hread j (List.mem_cons_of_mem i hj))]
    rw [hm]
    simp [b]

def allInputs (n : ℕ) : List ℕ := List.ofFn fun i : Fin n => i.val

def joinedBlock (n : ℕ) (gs : List Gate) : List Gate :=
  boundaryGates (allInputs n) ++ gs.map (shiftGate (n + 1))

def extractedBlock (gs : List Gate) (outs : List ℕ) : List Gate :=
  gs.map (shiftGate 1) ++ boundaryGates outs

lemma joinedBlock_length (n : ℕ) (gs : List Gate) :
    (joinedBlock n gs).length = n + gs.length := by
  simp [joinedBlock, boundaryGates, allInputs]

lemma extractedBlock_length (gs : List Gate) (outs : List ℕ) :
    (extractedBlock gs outs).length = gs.length + outs.length := by
  simp [extractedBlock, boundaryGates]

lemma wf_allInputs (u : Bool) (x : List Bool) :
    wf (boundaryGates (allInputs x.length)) (u :: x) =
      (u :: x) ++ x.map (fun b => u || b) := by
  rw [wf_boundary _ _ (by simp) (by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    simp; omega)]
  congr 1
  apply List.ext_getElem
  · simp [allInputs]
  · intro i hi hj
    have hil : i < x.length := by simpa [allInputs] using hi
    simp [allInputs, List.getD_eq_getElem?_getD, Nat.add_comm 1, hil]

lemma wf_joinedBlock (gs : List Gate) (u : Bool) (x : List Bool) :
    wf (joinedBlock x.length gs) (u :: x) =
      (u :: x) ++ wf gs (x.map fun b => u || b) := by
  unfold joinedBlock
  rw [show wf (boundaryGates (allInputs x.length) ++ gs.map (shiftGate (x.length + 1)))
      (u :: x) = wf (gs.map (shiftGate (x.length + 1)))
      (wf (boundaryGates (allInputs x.length)) (u :: x)) from List.foldl_append]
  rw [wf_allInputs]
  exact wf_shift gs (u :: x) _

lemma wf_extractedBlock (gs : List Gate) (outs : List ℕ) (u : Bool) (x : List Bool)
    (houts : ∀ i ∈ outs, i < x.length + gs.length) :
    wf (extractedBlock gs outs) (u :: x) =
      (u :: wf gs x) ++ outs.map (fun i => u || (wf gs x).getD i false) := by
  unfold extractedBlock
  rw [show wf (gs.map (shiftGate 1) ++ boundaryGates outs) (u :: x) =
      wf (boundaryGates outs) (wf (gs.map (shiftGate 1)) (u :: x)) from List.foldl_append]
  have hshift : wf (gs.map (shiftGate 1)) (u :: x) = u :: wf gs x :=
    wf_shift gs [u] x
  rw [hshift, wf_boundary _ _ (by simp) (by
    intro i hi
    have := houts i hi
    simp [wf_len]; omega)]
  simp [List.getD_eq_getElem?_getD, Nat.add_comm 1]

lemma component_extraction (gs : List Gate) (outs : List ℕ) (u : Bool) (x : List Bool)
    (hcore : ClosedCore x.length gs)
    (houts : ∀ i ∈ outs, i < x.length + gs.length) :
    wf (extractedBlock gs outs) (u :: x) =
      (u :: wf gs x) ++ outs.map (fun i =>
        (wf (joinedBlock x.length gs) (u :: x)).getD (x.length + 1 + i) false) := by
  rw [wf_extractedBlock gs outs u x houts, wf_joinedBlock]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [show x.length + 1 + i = (u :: x).length + i by simp]
  rw [getD_shift, wf_join gs x u hcore, getD_map_join _ _ _ (by
    rw [wf_len]
    exact houts i hi)]

lemma component_gate_saving (gs : List Gate) (outs : List ℕ) (n : ℕ) :
    (extractedBlock gs outs).length + n = (joinedBlock n gs).length + outs.length := by
  rw [extractedBlock_length, joinedBlock_length]
  omega

lemma component_no_larger (gs : List Gate) (outs : List ℕ) (n : ℕ)
    (hboundary : outs.length ≤ n) :
    (extractedBlock gs outs).length ≤ (joinedBlock n gs).length := by
  rw [extractedBlock_length, joinedBlock_length]
  omega

end component
