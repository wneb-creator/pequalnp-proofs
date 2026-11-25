import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit

open PEqualNP.CircuitLowerBounds

def binaryOp (d : Bool) : GateOp := if d then .or else .and

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

lemma getD_snoc_ne (w : List Bool) (v : Bool) (k : ℕ) (ne : k ≠ w.length) :
    (w ++ [v]).getD k false = w.getD k false := by
  by_cases lt : k < w.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma snoc_agree (i : ℕ) (w w' : List Bool) (v : Bool)
    (len : w.length = w'.length)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false) :
    ∀ k, k ≠ i → (w ++ [v]).getD k false = (w' ++ [v]).getD k false := by
  intro k ki
  by_cases eq : k = w.length
  · subst k
    simp [len]
  · rw [getD_snoc_ne w v k eq, getD_snoc_ne w' v k (by omega)]
    exact agree k ki

lemma gate_agree (i j : ℕ) (d : Bool) (g : Gate) (w w' : List Bool)
    (spec : i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i]))
    (left : w.getD j false = d) (right : w'.getD j false = d)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false) :
    g.op.eval (g.inputs.map fun k => w.getD k false) =
      g.op.eval (g.inputs.map fun k => w'.getD k false) := by
  by_cases reads : i ∈ g.inputs
  · obtain ⟨op, args | args⟩ := spec reads
    · simp only [List.getD_eq_getElem?_getD] at left right
      cases d <;> simp [op, args, binaryOp, GateOp.eval, left, right]
    · simp only [List.getD_eq_getElem?_getD] at left right
      cases d <;> simp [op, args, binaryOp, GateOp.eval, left, right]
  · apply congrArg g.op.eval
    apply List.map_congr_left
    intro k hk
    exact agree k (fun eq => reads (eq ▸ hk))

lemma fold_agree (i j : ℕ) (d : Bool) : ∀ (gs : List Gate),
    (∀ g ∈ gs, i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i])) →
    ∀ (w w' : List Bool), w.length = w'.length → j < w.length →
      w.getD j false = d → w'.getD j false = d →
      (∀ k, k ≠ i → w.getD k false = w'.getD k false) →
      ∀ o, o ≠ i →
        (gs.foldl step w).getD o false = (gs.foldl step w').getD o false := by
  intro gs
  induction gs with
  | nil => intro _ w w' _ _ _ _ agree; exact agree
  | cons g gs ih =>
    intro spec w w' len lt left right agree
    have val := gate_agree i j d g w w' (spec g (by simp)) left right agree
    apply ih (fun g hg => spec g (by simp [hg])) (step w g) (step w' g)
    · simp [step, len]
    · simp only [step, List.length_append, List.length_singleton]; omega
    · exact (List.getD_append _ _ _ _ lt).trans left
    · exact (List.getD_append _ _ _ _ (by omega)).trans right
    · unfold step
      rw [val]
      exact snoc_agree i w w' _ len agree

lemma eval_agree (gs : List Gate) (o i j : ℕ) (d : Bool) (w w' : List Bool)
    (spec : ∀ g ∈ gs, i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i]))
    (len : w.length = w'.length) (lt : j < w.length)
    (left : w.getD j false = d) (right : w'.getD j false = d)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false)
    (output : o ≠ i) : Circuit.eval ⟨gs, o⟩ w = Circuit.eval ⟨gs, o⟩ w' :=
  fold_agree i j d gs spec w w' len lt left right agree o output

end PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit
