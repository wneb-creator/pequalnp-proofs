import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.Capture

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def Step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Below (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, w.getD i false = true → v.getD i false = true

lemma below_append {w v : List Bool} (h : Below w v) {a b : Bool}
    (hab : a = true → b = true) : Below (w ++ [a]) (v ++ [b]) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro i hi
  by_cases small : i < w.length
  · rw [List.getD_append _ _ _ _ small] at hi
    rw [List.getD_append _ _ _ _ (h.1 ▸ small)]
    exact h.2 i hi
  · by_cases same : i = w.length
    · subst i
      have ai : a = true := by simpa [List.getD_eq_getElem?_getD] using hi
      simpa [h.1, List.getD_eq_getElem?_getD] using hab ai
    · have large : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ large] at hi
      contradiction

lemma gate_below {g : Gate} (op : g.op = GateOp.and ∨ g.op = GateOp.or)
    {w v : List Bool} (h : Below w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases op with ha | ho
  · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hw i hi
    exact h.2 i (hw i hi)
  · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hw⟩
    exact ⟨i, hi, h.2 i hw⟩

lemma fold_below (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {w v : List Bool} (h : Below w v) : Below (gs.foldl Step w) (gs.foldl Step v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun a ha => legal a (List.mem_cons_of_mem _ ha))
    exact below_append h (gate_below (legal g (by simp)) h)

lemma circuit_mono {n : ℕ} {C : Circuit} (legal : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have initial : Below (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases small : i < n
    · have hx : x ⟨i, small⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, small] using hi
      simpa [List.getD_eq_getElem?_getD, small] using hxy ⟨i, small⟩ hx
    · simp [List.getD_eq_getElem?_getD, small] at hi
  have allOps : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (legal g hg).1
  exact (fold_below C.gates allOps initial).2 C.output

lemma captured_output_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (H : (Fin n → Bool) → Bool)
    (correct : circuitFun n C = graphFun G ∅) (mono : Monotone2 D)
    (decreases : ∀ x, circuitFun n D x = true → circuitFun n C x = true)
    (outside : ∀ u v, G.Adj u v → H (pairInput u v) = false →
      circuitFun n D (pairInput u v) = circuitFun n C (pairInput u v))
    (captured : ∀ x, H x = true → circuitFun n D x = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    simpa only [correct] using decreases x hx
  · intro hx
    have hit : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u, v, edge, hu, hv⟩ := hit
    have atPair : circuitFun n D (pairInput u v) = true := by
      cases hH : H (pairInput u v) with
      | false =>
        rw [outside u v edge hH, correct]
        have hitPair : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
          ⟨u, v, edge, by simp [pairInput], by simp [pairInput]⟩
        simpa [graphFun] using hitPair
      | true => exact captured _ hH
    apply circuit_mono mono (x := pairInput u v) (y := x) _ atPair
    intro w hw
    have casesW : w = u ∨ w = v := by simpa [pairInput] using hw
    rcases casesW with rfl | rfl
    · exact hu
    · exact hv

end PEqualNP.Outside.L_meta_1772_aux.Capture
