import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readMeet (x y z : List Bool) : Prop :=
  x.length = y.length ∧ y.length = z.length ∧
    ∀ i, z.getD i false = (x.getD i false && y.getD i false)

lemma read_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases he : i = w.length
  · subst i
    simp
  · rw [ite_eq_right he]
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma and_eval_meet (x y z : List Bool) (h : readMeet x y z) (is : List ℕ) :
    GateOp.and.eval (is.map fun i => z.getD i false) =
      (GateOp.and.eval (is.map fun i => x.getD i false) &&
       GateOp.and.eval (is.map fun i => y.getD i false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq,
    Bool.and_eq_true]
  simp_rw [h.2.2, Bool.and_eq_true]
  simp only [forall_and]

lemma run_and_meet (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and)
    (x y z : List Bool) (h : readMeet x y z) :
    readMeet (Circuit.wires ⟨gs, 0⟩ x) (Circuit.wires ⟨gs, 0⟩ y)
      (Circuit.wires ⟨gs, 0⟩ z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    change readMeet
      (Circuit.wires ⟨gs, 0⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]))
      (Circuit.wires ⟨gs, 0⟩ (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]))
      (Circuit.wires ⟨gs, 0⟩ (z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]))
    apply ih (fun g hg => ops g (by simp [hg]))
    refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
    intro i
    rw [read_snoc, read_snoc, read_snoc]
    rw [← h.2.1, ← h.1]
    by_cases hi : i = x.length
    · simp only [hi, ite_eq_left]
      rw [ops g (by simp)]
      exact and_eval_meet x y z h g.inputs
    · simp only [hi, ite_false]
      exact h.2.2 i

lemma circuit_and_meet {n : ℕ} (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op = GateOp.and) (x y : Fin n → Bool) :
    C.eval (List.ofFn (fun i => x i && y i)) =
      (C.eval (List.ofFn x) && C.eval (List.ofFn y)) := by
  have hm : readMeet (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i && y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD, hi]
  exact (run_and_meet C.gates ops _ _ _ hm).2.2 C.output

lemma edge_count_le_one_of_and_only {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ops : ∀ g ∈ C.gates, g.op = GateOp.and)
    (computes : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    G.edgeFinset.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  revert he hf
  refine Sym2.ind (fun u v => ?_) e
  refine Sym2.ind (fun a b => ?_) f
  intro he hf
  have uv : G.Adj u v := by simpa using he
  have ab : G.Adj a b := by simpa using hf
  let x : Fin n → Bool := fun i => decide (i = u ∨ i = v)
  let y : Fin n → Bool := fun i => decide (i = a ∨ i = b)
  have hx : C.eval (List.ofFn x) = true := by
    rw [computes]
    exact decide_eq_true ⟨u,v,uv,by simp [x],by simp [x]⟩
  have hy : C.eval (List.ofFn y) = true := by
    rw [computes]
    exact decide_eq_true ⟨a,b,ab,by simp [y],by simp [y]⟩
  have hz := circuit_and_meet C ops x y
  rw [hx,hy,computes] at hz
  obtain ⟨c,d,cd,hc,hd⟩ := of_decide_eq_true hz
  have hc' : (c = u ∨ c = v) ∧ (c = a ∨ c = b) := by
    simpa [x,y] using hc
  have hd' : (d = u ∨ d = v) ∧ (d = a ∨ d = b) := by
    simpa [x,y] using hd
  have same (p q : Fin n) (hp : c = p ∨ c = q) (hq : d = p ∨ d = q) :
      s(c,d) = s(p,q) := by
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact False.elim (cd.ne rfl)
    · rfl
    · exact Sym2.eq_swap
    · exact False.elim (cd.ne rfl)
  exact (same u v hc'.1 hd'.1).symm.trans (same a b hc'.2 hd'.2)

lemma or_exists_of_two_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (mono : Monotone2 C)
    (computes : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hE : 2 ≤ G.edgeFinset.card) : ∃ g ∈ C.gates, g.op = GateOp.or := by
  by_contra no_or
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and := by
    intro g hg
    have shape : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (mono g hg).1
    rcases shape with ha | ho
    · exact ha
    · exact False.elim (no_or ⟨g,hg,ho⟩)
  have bound := edge_count_le_one_of_and_only G C ops computes
  omega

end PEqualNP.Outside.L_meta_5282_aux
