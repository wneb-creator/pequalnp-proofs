import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# The ladder, step 4: the De Morgan dual of an AND/OR list

Unverified, a conjecture until a checker accepts a row (hub row L-meta-1048, build plan step 4).

For a list of AND/OR gates on `n` inputs, the dual is built gate by gate. At gate position `k`
the wires `0 .. W - 1` exist, `W = n + k`, and a read at or beyond `W` reads `false`:
* an AND gate with a read at or beyond `W` is constant false; its dual is `AND []` (true);
* any other AND gate becomes an OR gate with the same reads;
* an OR gate becomes an AND gate of its reads below `W` (the dropped reads were `false`).
Then every wire below `n + length` of the dual on `x` is the negation of the same wire of the
original on `not x`. Wires at or beyond `n + length` read `false` in both, so they are excluded.
-/

namespace PEqualNP.MetaComplexity.Ladder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- The dual of one gate placed where the wires `0 .. W - 1` exist. -/
def ld_dualGate (W : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
      if g.inputs.all (fun i => decide (i < W)) then ⟨GateOp.or, g.inputs⟩
      else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, g.inputs.filter (fun i => decide (i < W))⟩
  | _ => g

/-- The dual of a gate list whose first gate sees the wires `0 .. W - 1`. -/
def ld_dualFrom : ℕ → List Gate → List Gate
  | _, [] => []
  | W, g :: gs => ld_dualGate W g :: ld_dualFrom (W + 1) gs

/-- The De Morgan dual of a gate list on `n` inputs. -/
def ld_dual (n : ℕ) (gs : List Gate) : List Gate := ld_dualFrom n gs

theorem ld_length_dualFrom : ∀ (gs : List Gate) (W : ℕ), (ld_dualFrom W gs).length = gs.length
  | [], _ => rfl
  | _ :: gs, W => by simp [ld_dualFrom, ld_length_dualFrom gs (W + 1)]

theorem ld_dualGate_ok (W : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((ld_dualGate W g).op = GateOp.and ∨ (ld_dualGate W g).op = GateOp.or) ∧
      (ld_dualGate W g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  rcases hop with rfl | rfl
  · simp only [ld_dualGate]
    split_ifs <;> simp [hl]
  · simp only [ld_dualGate]
    exact ⟨by simp, le_trans (List.length_filter_le _ _) hl⟩

theorem ld_dualFrom_ok : ∀ (gs : List Gate) (W : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ g ∈ ld_dualFrom W gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
  | [], _, _ => by simp [ld_dualFrom]
  | g :: gs, W, h => by
    intro g' hg'
    simp only [ld_dualFrom, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact ld_dualGate_ok W g (h g (by simp))
    · exact ld_dualFrom_ok gs (W + 1) (fun g'' hg'' => h g'' (by simp [hg''])) g' hg'

/-- AND of reads all present, dualised: an OR of the dual reads. -/
theorem ld_and_present (W : ℕ) (w v : List Bool)
    (hv : ∀ i < W, v.getD i false = !w.getD i false) :
    ∀ ins : List ℕ, ins.all (fun i => decide (i < W)) = true →
      (ins.map fun i => v.getD i false).any id = !(ins.map fun i => w.getD i false).all id
  | [], _ => rfl
  | i :: ins, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ld_and_present W w v hv ins h.2
    simp only [List.map_cons, List.any_cons, List.all_cons, id] at ih ⊢
    rw [hv i h.1, ih]
    cases w.getD i false <;> simp

/-- AND with a missing read is constant false. -/
theorem ld_and_missing (W : ℕ) (w : List Bool) (hw : w.length = W) :
    ∀ ins : List ℕ, ins.all (fun i => decide (i < W)) = false →
      (ins.map fun i => w.getD i false).all id = false
  | [], h => by simp at h
  | i :: ins, h => by
    simp only [List.all_cons, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at h
    simp only [List.map_cons, List.all_cons, id, Bool.and_eq_false_iff]
    rcases h with h | h
    · left; rw [List.getD_eq_default _ _ (by omega)]
    · right; exact ld_and_missing W w hw ins h

/-- OR dualised: an AND of the dual reads that are present. -/
theorem ld_or_dual (W : ℕ) (w v : List Bool) (hw : w.length = W)
    (hv : ∀ i < W, v.getD i false = !w.getD i false) :
    ∀ ins : List ℕ,
      ((ins.filter fun i => decide (i < W)).map fun i => v.getD i false).all id
        = !(ins.map fun i => w.getD i false).any id
  | [] => rfl
  | i :: ins => by
    have ih := ld_or_dual W w v hw hv ins
    by_cases hi : i < W
    · simp only [List.filter_cons, hi, decide_true, if_true, List.map_cons, List.all_cons,
        List.any_cons, id] at ih ⊢
      rw [hv i hi, ih]
      cases w.getD i false <;> simp
    · simp only [List.filter_cons, hi, decide_false, Bool.false_eq_true, if_false,
        List.map_cons, List.any_cons, id] at ih ⊢
      rw [ih, List.getD_eq_default _ _ (by omega)]
      simp

/-- One gate: the dual gate on the dual wires is the negation of the gate on the wires. -/
theorem ld_dualGate_eval (W : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hw : w.length = W)
    (hv : ∀ i < W, v.getD i false = !w.getD i false) :
    (ld_dualGate W g).op.eval ((ld_dualGate W g).inputs.map fun i => v.getD i false)
      = !(g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  rcases hop with rfl | rfl
  · simp only [ld_dualGate]
    by_cases ha : ins.all (fun i => decide (i < W)) = true
    · rw [if_pos ha]
      exact ld_and_present W w v hv ins ha
    · rw [if_neg ha]
      have ha' : ins.all (fun i => decide (i < W)) = false := by simpa using ha
      simp only [GateOp.eval]
      rw [ld_and_missing W w hw ins ha']
      rfl
  · simp only [ld_dualGate, GateOp.eval]
    exact ld_or_dual W w v hw hv ins

/-- The whole list: every wire below `W + length` of the dual run is the negation. -/
theorem ld_wires_dual : ∀ (gs : List Gate) (W : ℕ) (w v : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    w.length = W → v.length = W → (∀ i < W, v.getD i false = !w.getD i false) →
    ∀ i < W + gs.length,
      (wiresFrom (ld_dualFrom W gs) v).getD i false = !(wiresFrom gs w).getD i false
  | [], W, w, v, _, _, _, hv => by
    intro i hi
    simpa [ld_dualFrom, wiresFrom] using hv i (by simpa using hi)
  | g :: gs, W, w, v, hop, hw, hvl, hv => by
    intro i hi
    have e1 : wiresFrom (ld_dualFrom W (g :: gs)) v
        = wiresFrom (ld_dualFrom (W + 1) gs)
            (v ++ [(ld_dualGate W g).op.eval
              ((ld_dualGate W g).inputs.map fun i => v.getD i false)]) := rfl
    have e2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e1, e2]
    refine ld_wires_dual gs (W + 1) _ _ (fun g' hg' => hop g' (by simp [hg']))
      (by simp [hw]) (by simp [hvl]) ?_ i (by simp at hi; omega)
    intro j hj
    rw [ld_dualGate_eval W g (hop g (by simp)) w v hw hv]
    by_cases hjW : j < W
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hv j hjW
    · have hj' : j = W := by omega
      subst hj'
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [hw, hvl]

/-- STEP 4 OF THE LADDER: the De Morgan dual. Same length, AND/OR gates of fan-in at most
two, and every wire below `n + length` of the dual on `x` is the negation of the original's
on `not x`. -/
theorem ld_dual_spec (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    (ld_dual n gs).length = gs.length ∧
    (∀ g ∈ ld_dual n gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ∀ o : ℕ, o < n + gs.length → ∀ x : Fin n → Bool,
      Circuit.eval ⟨ld_dual n gs, o⟩ (List.ofFn x)
        = !Circuit.eval ⟨gs, o⟩ (List.ofFn fun i => !x i) := by
  refine ⟨ld_length_dualFrom gs n, ld_dualFrom_ok gs n hg, ?_⟩
  intro o ho x
  show (wiresFrom (ld_dualFrom n gs) (List.ofFn x)).getD o false
    = !(wiresFrom gs (List.ofFn fun i => !x i)).getD o false
  refine ld_wires_dual gs n _ _ (fun g hg' => (hg g hg').1) (by simp) (by simp) ?_ o ho
  intro i hi
  simp [List.getD_eq_getElem?_getD, hi]

end PEqualNP.MetaComplexity.Ladder
