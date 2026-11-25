import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.CircuitMonotone

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma append_mono (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = w.length
    · subst i
      have ha : a = true := by simpa using hi
      simpa [hlen] using hab ha
    · have hle : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hle] at hi
      cases hi

lemma run_mono (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (run gs w).getD i false = true → (run gs v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i,
      (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true →
      (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    · simpa using hlen
    · apply append_mono w v _ _ hlen h
      apply eval_mono g.op (hao g (by simp))
      intro i _
      exact h i

lemma circuitFun_mono (n : ℕ) (C : Circuit)
    (hao : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true := by
  apply run_mono C.gates hao (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases hin : i < n
  · have hx : i < (List.ofFn x).length := by simpa
    have hy : i < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact hxy ⟨i, hin⟩ hi
  · have hle : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hle] at hi
    cases hi

lemma ao2_mono (n : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true :=
  circuitFun_mono n C hao.1 x y hxy

end PEqualNP.Outside.L_meta_2585.CircuitMonotone
