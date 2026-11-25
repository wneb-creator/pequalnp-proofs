import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5399

open PEqualNP.CircuitLowerBounds

theorem getD_app_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem getD_app_gt (l : List Bool) (b : Bool) (i : ℕ) (h : l.length < i) :
    (l ++ [b]).getD i false = false := by
  rw [List.getD_eq_default]
  simp; omega

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_default _ _ h]

theorem wires_len (gs : List Gate) : ∀ (d : List Bool),
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).length
      = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; rw [List.foldl_cons, ih]; simp; omega

theorem reach_len (X : ℕ) (gs : List Gate) : ∀ (d : List Bool),
    (gs.foldl (fun (d : List Bool) (g : Gate) =>
        d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) d).length
      = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; rw [List.foldl_cons, ih]; simp; omega

theorem wires_prefix (gs : List Gate) : ∀ (d : List Bool) (i : ℕ), i < d.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false
      = d.getD i false := by
  induction gs with
  | nil => intro d i _; simp
  | cons g gs ih =>
    intro d i hi
    rw [List.foldl_cons, ih _ _ (by simp; omega), getD_app_lt _ _ _ hi]

theorem indep (X : ℕ) (gs : List Gate) : ∀ (d e r : List Bool),
    d.length = r.length → e.length = r.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD X false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD X false →
    (∀ i, i ≠ X → r.getD i false = false → d.getD i false = e.getD i false) →
    ∀ i, (gs.foldl (fun (d : List Bool) (g : Gate) =>
        d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) r).getD i false = false →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD i false := by
  induction gs with
  | nil =>
    intro d e r _ _ hX hinv i hi
    simp only [List.foldl_nil] at hX hi ⊢
    by_cases hiX : i = X
    · subst hiX; exact hX
    · exact hinv i hiX hi
  | cons g gs ih =>
    intro d e r hd he hX hinv
    have hdX : d.getD X false = e.getD X false := by
      by_cases hlt : X < d.length
      · rw [← wires_prefix (g :: gs) d X hlt, ← wires_prefix (g :: gs) e X (by omega)]
        exact hX
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    have hall : ∀ j, r.getD j false = false → d.getD j false = e.getD j false := by
      intro j hj
      by_cases hjX : j = X
      · subst hjX; exact hdX
      · exact hinv j hjX hj
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    apply ih
    · simp [hd]
    · simp [he]
    · rw [List.foldl_cons, List.foldl_cons] at hX; exact hX
    · intro i hiX hri
      rcases lt_trichotomy i r.length with h | h | h
      · rw [getD_app_lt _ _ _ h] at hri
        rw [getD_app_lt _ _ _ (by omega), getD_app_lt _ _ _ (by omega)]
        exact hinv i hiX hri
      · subst h
        rw [getD_app_eq] at hri
        rw [← hd, getD_app_eq, hd, ← he, getD_app_eq]
        have hne : decide (r.length ≠ X) = true := by simp; exact hiX
        rw [hne, Bool.true_and] at hri
        have hmap : (g.inputs.map fun i => d.getD i false) = (g.inputs.map fun i => e.getD i false) := by
          apply List.map_congr_left
          intro j hj
          apply hall
          have := List.any_eq_false.mp hri j hj
          simpa using this
        rw [hmap]
      · rw [getD_app_gt _ _ _ (by omega), getD_app_gt _ _ _ (by omega)]

theorem mono (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (d e : List Bool), d.length = e.length →
    (∀ i, d.getD i false = true → e.getD i false = true) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false = true →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD i false = true := by
  induction gs with
  | nil => intro d e _ h i; simpa using h i
  | cons g gs ih =>
    intro d e hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i d.length with hh | hh | hh
      · rw [getD_app_lt _ _ _ hh] at hi
        rw [getD_app_lt _ _ _ (by omega)]
        exact h i hi
      · subst hh
        rw [getD_app_eq] at hi
        rw [hl, getD_app_eq]
        rcases hop g (List.mem_cons_self) with ho | ho
        · rw [ho] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hi ⊢
          rintro _ ⟨j, hj, rfl⟩
          exact h j (by simpa using hi _ ⟨j, hj, rfl⟩)
        · rw [ho] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
          obtain ⟨_, ⟨j, hj, rfl⟩, hv⟩ := hi
          exact ⟨_, ⟨j, hj, rfl⟩, by simpa using h j (by simpa using hv)⟩
      · rw [getD_app_gt _ _ _ hh] at hi
        exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_5399

theorem PEqualNP.Outside.L_meta_5399 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (a c : Fin n) (X : ℕ), PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → G.Adj a c → (C.gates.foldl (fun (d : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X))).getD C.output false = false → ∀ J : Finset (Fin n), (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) → c ∈ J → PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = false ∧ PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
  intro n G _ C a c X hC _ hfun hac hreach J hJ hcJ
  have haJ : a ∉ J := fun ha => hJ a ha c hcJ hac
  -- values of the circuit on the two inputs
  have hF1 : C.eval (List.ofFn (PEqualNP.ReadK.setInput J)) = false := by
    have := congrFun hfun (PEqualNP.ReadK.setInput J)
    simp only [PEqualNP.MetaComplexity.circuitFun] at this
    rw [this]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, PEqualNP.ReadK.setInput]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, decide_eq_true_eq]
    rintro ⟨u, v, huv, hu, hv⟩
    exact hJ u hu v hv huv
  have hF2 : C.eval (List.ofFn (PEqualNP.ReadK.setInput (insert a J))) = true := by
    have := congrFun hfun (PEqualNP.ReadK.setInput (insert a J))
    simp only [PEqualNP.MetaComplexity.circuitFun] at this
    rw [this]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, PEqualNP.ReadK.setInput]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a, c, hac, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hcJ⟩
  -- the X values differ
  have hne : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J)
      ≠ PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) := by
    intro heq
    have key := L_meta_5399.indep X C.gates
      (List.ofFn (PEqualNP.ReadK.setInput J))
      (List.ofFn (PEqualNP.ReadK.setInput (insert a J)))
      (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X))
      (by simp) (by simp) heq
      (by
        intro i hiX hri
        by_cases hin : i < n
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_true, Option.getD_some] at hri ⊢
          have hia : (⟨i, hin⟩ : Fin n) ≠ a := by
            intro h; subst h; simp [hiX] at hri
          simp [PEqualNP.ReadK.setInput, Finset.mem_insert, hia]
        · rw [L_meta_5399.getD_ge _ _ (by simp; omega), L_meta_5399.getD_ge _ _ (by simp; omega)])
      C.output hreach
    have e1 : C.eval (List.ofFn (PEqualNP.ReadK.setInput J)) =
        C.eval (List.ofFn (PEqualNP.ReadK.setInput (insert a J))) := key
    rw [hF1, hF2] at e1
    exact Bool.false_ne_true e1
  -- monotonicity
  have hmono : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = true →
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
    intro h
    refine L_meta_5399.mono C.gates hC.1 _ _ (by simp) ?_ X h
    intro i hi
    by_cases hin : i < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_true, Option.getD_some] at hi ⊢
      simp only [PEqualNP.ReadK.setInput, decide_eq_true_eq] at hi ⊢
      exact Finset.mem_insert_of_mem hi
    · rw [L_meta_5399.getD_ge _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  cases h1 : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) <;>
    cases h2 : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) <;>
    simp_all
