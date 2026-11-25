import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.ThreeBlockers

open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 4

def weak (a : Sig) : Bool := !a.getLsbD 0 ||
  ((a.getLsbD 1 && a.getLsbD 2) || (a.getLsbD 1 && a.getLsbD 3) ||
    (a.getLsbD 2 && a.getLsbD 3))

def strong (a : Sig) : Bool := !a.getLsbD 0 ||
  a.getLsbD 1 || a.getLsbD 2 || a.getLsbD 3

lemma weak_strong : ∀ a : Sig, weak a = true → strong a = true := by decide

lemma weak_or : ∀ a b : Sig,
    weak a = true → weak b = true → weak (a ||| b) = true := by decide

lemma strong_or : ∀ a b : Sig,
    strong a = true → strong b = true → strong (a ||| b) = true := by decide

lemma weak_and_strong : ∀ a b : Sig,
    weak a = true → weak b = true → strong (a &&& b) = true := by decide

lemma and_fifteen : ∀ a : Sig, a &&& 15 = a := by decide

def evalGate (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (fun a b => a &&& b) 15
  | .or => xs.foldr (fun a b => a ||| b) 0
  | _ => 0

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun a g => a ++ [evalGate a g]) w

def isAnd (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

lemma weak_get (w : List Sig) (h : ∀ a ∈ w, weak a = true) (i : Nat) :
    weak (w.getD i 0) = true := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

lemma strong_get (w : List Sig) (h : ∀ a ∈ w, strong a = true) (i : Nat) :
    strong (w.getD i 0) = true := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

lemma weak_or_fold (xs : List Sig) (h : ∀ a ∈ xs, weak a = true) :
    weak (xs.foldr (fun a b => a ||| b) 0) = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    exact weak_or a _ (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma strong_or_fold (xs : List Sig) (h : ∀ a ∈ xs, strong a = true) :
    strong (xs.foldr (fun a b => a ||| b) 0) = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    exact strong_or a _ (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma or_gate_weak (w : List Sig) (g : Gate) (hg : g.op = .or)
    (h : ∀ a ∈ w, weak a = true) : weak (evalGate w g) = true := by
  simp only [evalGate, hg]
  apply weak_or_fold
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact weak_get w h i

lemma or_gate_strong (w : List Sig) (g : Gate) (hg : g.op = .or)
    (h : ∀ a ∈ w, strong a = true) : strong (evalGate w g) = true := by
  simp only [evalGate, hg]
  apply strong_or_fold
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact strong_get w h i

lemma and_gate_strong (w : List Sig) (g : Gate) (hg : g.op = .and)
    (hlen : g.inputs.length ≤ 2) (h : ∀ a ∈ w, weak a = true) :
    strong (evalGate w g) = true := by
  have hi : ∀ i, weak (w.getD i 0) = true := weak_get w h
  obtain ⟨op, ins⟩ := g
  simp only at hg hlen
  subst op
  cases ins with
  | nil => change strong 15 = true; decide
  | cons i ins =>
    cases ins with
    | nil =>
      change strong (w.getD i 0 &&& 15) = true
      rw [and_fifteen]
      exact weak_strong _ (hi i)
    | cons j ins =>
      cases ins with
      | nil =>
        change strong (w.getD i 0 &&& (w.getD j 0 &&& 15)) = true
        rw [and_fifteen]
        exact weak_and_strong _ _ (hi i) (hi j)
      | cons k rest => simp at hlen

lemma execute_or_strong (gs : List Gate) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op = .or) (hw : ∀ a ∈ w, strong a = true) :
    ∀ a ∈ execute gs w, strong a = true := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih _ (fun g' hg' => hg g' (by simp [hg']))
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · have ha' : a = evalGate w g := List.mem_singleton.mp ha
      rw [ha']
      exact or_gate_strong w g (hg g (by simp)) hw

theorem execute_one_and_strong (gs : List Gate) (w : List Sig)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hc : gs.countP isAnd ≤ 1) (hw : ∀ a ∈ w, weak a = true) :
    ∀ a ∈ execute gs w, strong a = true := by
  induction gs generalizing w with
  | nil => exact fun a ha => weak_strong a (hw a ha)
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    rcases hop with hop | hop
    · have hc0 : gs.countP isAnd = 0 := by
        simpa [List.countP_cons, isAnd, hop] using hc
      have hor : ∀ g' ∈ gs, g'.op = .or := by
        intro g' hg'
        have hn : isAnd g' = false := by simpa using List.countP_eq_zero.mp hc0 g' hg'
        rcases (hg g' (by simp [hg'])).1 with h | h
        · simp [isAnd, h] at hn
        · exact h
      apply execute_or_strong gs _ hor
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact weak_strong a (hw a ha)
      · have ha' : a = evalGate w g := List.mem_singleton.mp ha
        rw [ha']
        exact and_gate_strong w g hop hlen hw
    · apply ih _ (fun g' hg' => hg g' (by simp [hg']))
        (by simpa [List.countP_cons, isAnd, hop] using hc)
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · have ha' : a = evalGate w g := List.mem_singleton.mp ha
        rw [ha']
        exact or_gate_weak w g hop hw

def bit (r : Fin 4) (a : Sig) : Bool := a.getLsbD r.val

lemma and_fold_rows (xs : List Sig) (r : Fin 4) :
    bit r (xs.foldr (fun a b => a &&& b) 15) = (xs.map (bit r)).all id := by
  induction xs with
  | nil => fin_cases r <;> decide
  | cons a xs ih =>
    simpa [bit, List.foldr_cons, List.all_cons, BitVec.getLsbD_and] using
      congrArg (fun b => bit r a && b) ih

lemma or_fold_rows (xs : List Sig) (r : Fin 4) :
    bit r (xs.foldr (fun a b => a ||| b) 0) = (xs.map (bit r)).any id := by
  induction xs with
  | nil => simp [bit]
  | cons a xs ih =>
    simpa [bit, List.foldr_cons, List.any_cons, BitVec.getLsbD_or] using
      congrArg (fun b => bit r a || b) ih

lemma reads_rows (w : List Sig) (g : Gate) (r : Fin 4) :
    (g.inputs.map (fun i => w.getD i 0)).map (bit r) =
      g.inputs.map (fun i => (w.map (bit r)).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  simpa [bit] using (List.getD_map w (0 : Sig) (n := i) (bit r)).symm

lemma gate_rows (w : List Sig) (g : Gate) (r : Fin 4)
    (hg : g.op = .and ∨ g.op = .or) :
    bit r (evalGate w g) =
      g.op.eval (g.inputs.map (fun i => (w.map (bit r)).getD i false)) := by
  rcases hg with hg | hg
  · simp only [evalGate, hg, GateOp.eval]
    rw [and_fold_rows, reads_rows]
  · simp only [evalGate, hg, GateOp.eval]
    rw [or_fold_rows, reads_rows]

lemma execute_rows (gs : List Gate) (w : List Sig) (r : Fin 4)
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (execute gs w).map (bit r) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map (fun i => a.getD i false))])
        (w.map (bit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [evalGate w g])).map (bit r) = _
    rw [ih _ (fun g' hg' => hg g' (by simp [hg']))]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil]
    rw [gate_rows w g r (hg g (by simp))]

lemma output_row (C : Circuit) (w : List Sig) (r : Fin 4)
    (hg : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    bit r ((execute C.gates w).getD C.output 0) = C.eval (w.map (bit r)) := by
  unfold Circuit.eval Circuit.wires
  rw [← execute_rows C.gates w r hg]
  simpa [bit] using (List.getD_map (execute C.gates w) (0 : Sig)
    (n := C.output) (bit r)).symm

theorem at_least_two_ands (C : Circuit) (w : List Sig)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hw : ∀ a ∈ w, weak a = true)
    (h0 : C.eval (w.map (bit 0)) = true)
    (h1 : C.eval (w.map (bit 1)) = false)
    (h2 : C.eval (w.map (bit 2)) = false)
    (h3 : C.eval (w.map (bit 3)) = false) : 2 ≤ C.gates.countP isAnd := by
  by_contra hsmall
  have hc : C.gates.countP isAnd ≤ 1 := by omega
  have hstrong := strong_get (execute C.gates w)
    (execute_one_and_strong C.gates w hg hc hw) C.output
  have hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g h => (hg g h).1
  have hr0 := output_row C w 0 hop
  have hr1 := output_row C w 1 hop
  have hr2 := output_row C w 2 hop
  have hr3 := output_row C w 3 hop
  rw [h0] at hr0
  rw [h1] at hr1
  rw [h2] at hr2
  rw [h3] at hr3
  change bit 0 ((execute C.gates w).getD C.output 0) = true at hr0
  change bit 1 ((execute C.gates w).getD C.output 0) = false at hr1
  change bit 2 ((execute C.gates w).getD C.output 0) = false at hr2
  change bit 3 ((execute C.gates w).getD C.output 0) = false at hr3
  change (!bit 0 ((execute C.gates w).getD C.output 0) ||
    bit 1 ((execute C.gates w).getD C.output 0) ||
    bit 2 ((execute C.gates w).getD C.output 0) ||
    bit 3 ((execute C.gates w).getD C.output 0)) = true at hstrong
  rw [hr0, hr1, hr2, hr3] at hstrong
  cases hstrong

end PEqualNP.Outside.L_meta_1884.ThreeBlockers
