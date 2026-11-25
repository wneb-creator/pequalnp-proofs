import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3457_aux

open PEqualNP.CircuitLowerBounds

lemma any_or_distribute (xs : List ℕ) (a b : ℕ → Bool) :
    xs.any (fun i => a i || b i) = (xs.any a || xs.any b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, ih]
    ac_rfl

lemma all_or_false (xs : List ℕ) (a b : ℕ → Bool)
    (h : xs.all (fun i => a i || b i) = false) :
    xs.all a = false ∧ xs.all b = false := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro ha
    have hu : xs.all (fun i => a i || b i) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      simp [List.all_eq_true.mp ha i hi]
    rw [h] at hu
    cases hu
  · apply Bool.eq_false_iff.mpr
    intro hb
    have hu : xs.all (fun i => a i || b i) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      simp [List.all_eq_true.mp hb i hi]
    rw [h] at hu
    cases hu

lemma gate_union (g : Gate) (a b c : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hoff : g.op = GateOp.and → g.op.eval (g.inputs.map fun i => c.getD i false) = false) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) ||
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  rcases hop with hop | hop
  · have h := hoff hop
    simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq] at h ⊢
    simp_rw [hval] at h ⊢
    obtain ⟨ha, hb⟩ := all_or_false g.inputs (fun i => a.getD i false) (fun i => b.getD i false) h
    rw [h, ha, hb]
    rfl
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq]
    simp_rw [hval]
    exact any_or_distribute _ _ _

lemma append_union (a b c : List Bool) (u v w : Bool)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hw : w = (u || v)) :
    ∀ i, (c ++ [w]).getD i false =
      ((a ++ [u]).getD i false || (b ++ [v]).getD i false) := by
  intro i
  by_cases hi : i < c.length
  · rw [List.getD_append c [w] false i hi,
        List.getD_append a [u] false i (by omega),
        List.getD_append b [v] false i (by omega)]
    exact hval i
  · rw [List.getD_append_right c [w] false i (by omega),
        List.getD_append_right a [u] false i (by omega),
        List.getD_append_right b [v] false i (by omega), ha, hb]
    cases h : i - c.length <;> simp [hw]

def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_union (gs : List Gate) (a b c : List Bool)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hoff : ∀ before g after, gs = before ++ g :: after →
      g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => (before.foldl runStep c).getD i false) = false) :
    ∀ i, (gs.foldl runStep c).getD i false =
      ((gs.foldl runStep a).getD i false || (gs.foldl runStep b).getD i false) := by
  induction gs generalizing a b c with
  | nil => exact hval
  | cons g gs ih =>
    have hgv := gate_union g a b c (hmono g (by simp)) hval (hoff [] g gs rfl)
    have hstep : ∀ i, (runStep c g).getD i false =
        ((runStep a g).getD i false || (runStep b g).getD i false) :=
      append_union a b c _ _ _ ha hb hval hgv
    simp only [List.foldl_cons]
    apply ih (runStep a g) (runStep b g) (runStep c g)
      (by simp [runStep, ha]) (by simp [runStep, hb]) hstep
      (fun q hq => hmono q (by simp [hq]))
    intro before q after heq hq
    have h := hoff (g :: before) q after (by simp only [List.cons_append]; rw [heq]) hq
    simpa only [List.foldl_cons] using h

lemma crossed_singletons (u v p q : Bool)
    (hpair : (u || p) && (v || q) = true)
    (hfirst : u && v = false) (hsecond : p && q = false) :
    (u = true ∧ v = false ∧ p = false ∧ q = true) ∨
    (u = false ∧ v = true ∧ p = true ∧ q = false) := by
  cases u <;> cases v <;> cases p <;> cases q <;> simp_all

end PEqualNP.Outside.L_meta_3457_aux
