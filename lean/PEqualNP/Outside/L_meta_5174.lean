import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5174_aux

-- Helpers adapted from PEqualNP/Outside/L_meta_1388.lean and Pre_L_meta_4871.lean.

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hgs g (List.mem_cons_self) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
        · simp only [List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨a, ha, rfl⟩
          exact h a (hall _ ⟨a, ha, rfl⟩)
        · simp only [List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      intro i hi
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_5174_aux

theorem PEqualNP.Outside.L_meta_5174 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1 → Bool),       (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) →         have x7 : (Fin x1 → Bool) → ℕ → Bool := fun (x7 : Fin x1 → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;         (∀ (x8 : Fin x1), x7 x5 ↑x8 = x5 x8) ∧ ∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate) (x10 : ℕ), x2.gates[x8]? = Option.some x9 → x10 ∈ x9.inputs → x7 x5 (x1 + x8) = Bool.false → (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ x14 ∈ x9.inputs, x14 ≠ x10 → x7 x4 x14 = Bool.true) → x7 x5 x10 = Bool.false := by
  intro n C hC x4 x5 hle x7
  open PEqualNP.Outside.L_meta_5174_aux in
  have mono : ∀ i, (C.wires (List.ofFn x4)).getD i false = true →
      (C.wires (List.ofFn x5)).getD i false = true := by
    intro i hi
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires at hi ⊢
    refine fold_mono C.gates hC.1 _ _ (by simp) ?_ i hi
    intro i hi
    by_cases h : i < n
    · rw [ofFn_getD_lt _ _ h] at hi ⊢
      exact hle _ hi
    · rw [getD_ge_len _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  refine ⟨?_, ?_⟩
  · intro i
    exact PEqualNP.Outside.L_meta_5174_aux.wires_input C x5 i i.isLt
  · intro j g k hj hk hfalse hcase
    change (C.wires (List.ofFn x5)).getD (n + j) false = false at hfalse
    change (C.wires (List.ofFn x5)).getD k false = false
    change g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ x14 ∈ g.inputs, x14 ≠ k →
      (C.wires (List.ofFn x4)).getD x14 false = true at hcase
    have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    have hrb : ∀ i ∈ g.inputs, i < n + j := by
      intro i hi
      exact hC.2.1 j hjlt i (hgat ▸ hi)
    rw [PEqualNP.Outside.L_meta_5174_aux.wires_gate_ofFn C x5 j g hj] at hfalse
    have hmap : (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x5)).getD i false else false)
        = g.inputs.map fun i => (C.wires (List.ofFn x5)).getD i false := by
      apply List.map_congr_left
      intro i hi
      simp [hrb i hi]
    rw [hmap] at hfalse
    have hgm : g ∈ C.gates := List.mem_of_getElem? hj
    rcases hC.1 g hgm with ho | ho
    · by_contra hne
      have hall : ∀ a ∈ g.inputs, (C.wires (List.ofFn x5)).getD a false = true := by
        intro a ha
        by_cases hak : a = k
        · subst hak; simpa using hne
        · rcases hcase with hc | hc
          · rw [ho] at hc; cases hc
          · exact mono a (hc a ha hak)
      rw [ho] at hfalse
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at hfalse
      have : (g.inputs.map fun i => (C.wires (List.ofFn x5)).getD i false).all id = true := by
        simp only [List.all_eq_true, List.mem_map]
        rintro _ ⟨a, ha, rfl⟩
        simpa using hall a ha
      rw [this] at hfalse
      exact absurd hfalse (by decide)
    · rw [ho] at hfalse
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at hfalse
      by_contra hne
      have : (g.inputs.map fun i => (C.wires (List.ofFn x5)).getD i false).any id = true := by
        simp only [List.any_eq_true, List.mem_map]
        exact ⟨_, ⟨k, hk, rfl⟩, by simpa using hne⟩
      rw [this] at hfalse
      exact absurd hfalse (by decide)
