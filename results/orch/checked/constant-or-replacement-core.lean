import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896.ConstantOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateValue g w]) w

def Below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma below_refl (a : List Bool) : Below a a := ⟨rfl, fun _ h => h⟩

lemma below_zero (a : List Bool) : Below (List.replicate a.length false) a := by
  refine ⟨by simp, ?_⟩
  intro i h
  simp at h

lemma below_snoc {a b : List Bool} {x y : Bool} (h : Below a b)
    (hxy : x = true → y = true) : Below (a ++ [x]) (b ++ [y]) := by
  have hl := h.1
  refine ⟨by simp [hl], ?_⟩
  intro i hi
  by_cases hil : i < a.length
  · rw [List.getD_append _ _ _ _ hil] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h.2 i hi
  · by_cases hie : i = a.length
    · subst i
      have he : a.length = b.length := h.1
      have hx : x = true := by simpa [List.getD_eq_getElem?_getD] using hi
      simpa [List.getD_eq_getElem?_getD, he] using hxy hx
    · have ha : (a ++ [x]).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [ha] at hi
      cases hi

lemma gateValue_mono (g : Gate) (legal : g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (h : Below a b) : gateValue g a = true → gateValue g b = true := by
  rcases legal with ha | ho
  · simp only [gateValue, ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hg i hi => h.2 i (hg i hi)
  · simp only [gateValue, ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h.2 i hv⟩

def stripGate (z : List Bool) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => if gateValue g z then ⟨GateOp.and, []⟩ else g
  | _ => g

def stripGates : List Bool → List Gate → List Gate
  | _, [] => []
  | z, g :: gs => stripGate z g :: stripGates (z ++ [gateValue g z]) gs

lemma stripGate_eval (z w : List Bool) (g : Gate)
    (legal : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Below z w) :
    gateValue (stripGate z g) w = gateValue g w := by
  rcases legal with ha | ho
  · simp [stripGate, ha]
  · by_cases hv : gateValue g z = true
    · have hw := gateValue_mono g (Or.inr ho) h hv
      have hs : stripGate z g = ⟨GateOp.and, []⟩ := by
        unfold stripGate
        rw [ho]
        simp [hv]
      rw [hs, hw]
      rfl
    · have hs : stripGate z g = g := by
        unfold stripGate
        rw [ho]
        simp [hv]
      rw [hs]

lemma stripGates_run (gs : List Gate) (z w : List Bool)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h : Below z w) : run (stripGates z gs) w = run gs w := by
  induction gs generalizing z w with
  | nil => rfl
  | cons g gs ih =>
    simp only [stripGates, run, List.foldl_cons]
    rw [stripGate_eval z w g (legal g (by simp)).1 h]
    exact ih (z ++ [gateValue g z]) (w ++ [gateValue g w])
      (fun g hg => legal g (by simp [hg]))
      (below_snoc h (gateValue_mono g (legal g (by simp)).1 h))

lemma stripGates_length (gs : List Gate) (z : List Bool) :
    (stripGates z gs).length = gs.length := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih => simp [stripGates, ih]

lemma stripGate_or (z : List Bool) (g : Gate) :
    (stripGate z g).op = GateOp.or → g.op = GateOp.or := by
  cases h : g.op <;> simp [stripGate, h]

lemma stripGate_or_false (z : List Bool) (g : Gate) :
    (stripGate z g).op = GateOp.or → gateValue g z = false := by
  cases h : g.op <;> simp [stripGate, h]
  split_ifs <;> simp_all

lemma stripGate_legal (z : List Bool) (g : Gate)
    (legal : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((stripGate z g).op = GateOp.and ∨ (stripGate z g).op = GateOp.or) ∧
      (stripGate z g).inputs.length ≤ 2 := by
  rcases legal.1 with ha | ho
  · simpa [stripGate, ha] using legal
  · simp only [stripGate, ho]
    split_ifs <;> simp_all

lemma stripGates_legal (gs : List Gate) (z : List Bool)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ stripGates z gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing z with
  | nil => simp [stripGates]
  | cons g gs ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact stripGate_legal z g (legal g (by simp))
    · exact ih _ (fun g hg => legal g (by simp [hg])) h hh

lemma stripGates_op (gs : List Gate) (z : List Bool) (j : ℕ) (hj : j < gs.length) :
    ((stripGates z gs)[j]'(by simpa [stripGates_length] using hj)).op = GateOp.or →
      (gs[j]'hj).op = GateOp.or := by
  induction gs generalizing z j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => exact stripGate_or z g
    | succ j => exact ih _ j (by simpa using hj)

end PEqualNP.Outside.L_meta_1896.ConstantOr
