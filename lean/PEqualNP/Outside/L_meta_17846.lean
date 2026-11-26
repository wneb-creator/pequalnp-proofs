import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17846

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

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])


lemma mono_of_ops (gs : List Gate) (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : ∀ g ∈ gs, g.inputs.length = 2) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ := by
  intro g hg
  refine ⟨?_, by rw [hl g hg]⟩
  rcases h g hg with h1 | h1 <;> simp [h1]

theorem main (n m o : ℕ) (f : ℕ → (Fin n → Bool) → Bool) (ho : o < n + m)
    (hin : ∀ i < n, ∃ k : Fin n, ∀ x : Fin n → Bool, f i x = x k)
    (hg : ∀ j < m, ∃ a < n + j, ∃ b < n + j,
      (∀ x : Fin n → Bool, f (n + j) x = (f a x && f b x)) ∨
        ∀ x : Fin n → Bool, f (n + j) x = (f a x || f b x)) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ m ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f o x := by
  classical
  let r : ℕ → ℕ := fun i => if h : i < n then (Classical.choose (hin i h)).val else i
  have hr_lt : ∀ i, i < n → r i < n := by
    intro i hi; simp only [r, hi, dite_true]; exact (Classical.choose (hin i hi)).isLt
  have hr_ge : ∀ i, ¬ i < n → r i = i := by
    intro i hi; simp only [r, hi, dite_false]
  let A : ℕ → ℕ := fun j => if h : j < m then Classical.choose (hg j h) else 0
  have hA : ∀ j (h : j < m), A j = Classical.choose (hg j h) := by
    intro j h; simp only [A, h, dite_true]
  let B : ℕ → ℕ := fun j => if h : j < m then Classical.choose (Classical.choose_spec (hg j h)).2 else 0
  have hB : ∀ j (h : j < m), B j = Classical.choose (Classical.choose_spec (hg j h)).2 := by
    intro j h; simp only [B, h, dite_true]
  have hAB : ∀ j < m, A j < n + j ∧ B j < n + j ∧
      ((∀ x : Fin n → Bool, f (n + j) x = (f (A j) x && f (B j) x)) ∨
        ∀ x : Fin n → Bool, f (n + j) x = (f (A j) x || f (B j) x)) := by
    intro j h
    rw [hA j h, hB j h]
    have s1 := Classical.choose_spec (hg j h)
    have s2 := Classical.choose_spec s1.2
    exact ⟨s1.1, s2.1, s2.2⟩
  let O : ℕ → GateOp := fun j =>
    if ∀ x : Fin n → Bool, f (n + j) x = (f (A j) x && f (B j) x) then GateOp.and else GateOp.or
  let gate : ℕ → Gate := fun j => ⟨O j, [r (A j), r (B j)]⟩
  let C : Circuit := ⟨(List.range m).map gate, r o⟩
  have hlen : C.gates.length = m := by simp [C]
  have hgate : ∀ j < m, C.gates[j]? = some (gate j) := by
    intro j hj; simp [C, List.getElem?_map, List.getElem?_range hj]
  have hval_r : ∀ x : Fin n → Bool, ∀ i, i < n + m → ∀ j, i < n + j →
      r i < n + j := by
    intro x i hi j hij
    by_cases h : i < n
    · have := hr_lt i h; omega
    · rw [hr_ge i h]; exact hij
  have key : ∀ x : Fin n → Bool, ∀ w, w < n + m →
      (C.wires (List.ofFn x)).getD (r w) false = f w x := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h : w < n
      · have hk := Classical.choose_spec (hin w h)
        have hrw : r w = (Classical.choose (hin w h)).val := by simp only [r, h, dite_true]
        rw [hrw, wires_input C x _ (Classical.choose (hin w h)).isLt, hk x]
      · rw [hr_ge w h]
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < m := by omega
        obtain ⟨ha, hb, hop⟩ := hAB j hj
        rw [wires_gate_ofFn C x j (gate j) (hgate j hj)]
        have e1 := hval_r x (A j) (by omega) j ha
        have e2 := hval_r x (B j) (by omega) j hb
        have i1 := ih (A j) (by omega) (by omega)
        have i2 := ih (B j) (by omega) (by omega)
        simp only [gate, List.map_cons, List.map_nil, e1, e2, ite_true, i1, i2]
        by_cases hc : ∀ x : Fin n → Bool, f (n + j) x = (f (A j) x && f (B j) x)
        · have hO : O j = GateOp.and := if_pos hc
          rw [hO, hc x]
          simp only [GateOp.eval]
          cases f (A j) x <;> cases f (B j) x <;> rfl
        · have hc2 : ∀ x : Fin n → Bool, f (n + j) x = (f (A j) x || f (B j) x) := by
            rcases hop with h1 | h1
            · exact absurd h1 hc
            · exact h1
          have hO : O j = GateOp.or := if_neg hc
          rw [hO, hc2 x]
          simp only [GateOp.eval]
          cases f (A j) x <;> cases f (B j) x <;> rfl
  refine ⟨C, ?_, by simp [Circuit.size, hlen], fun x => key x o ho⟩
  intro g hg
  simp only [C, List.mem_map, List.mem_range] at hg
  obtain ⟨j, _, rfl⟩ := hg
  refine ⟨?_, by simp [gate]⟩
  by_cases hc : ∀ x : Fin n → Bool, f (n + j) x = (f (A j) x && f (B j) x)
  · simp [gate, O, hc]
  · simp [gate, O, hc]

end PEqualNP.Outside.L_meta_17846

theorem PEqualNP.Outside.L_meta_17846 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → (Fin x1 → Bool) → Bool), x3 < x1 + x2 → (∀ x6 < x1, ∃ (x8 : Fin x1), ∀ (x9 : Fin x1 → Bool), x4 x6 x9 = x9 x8) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, (∀ (x11 : Fin x1 → Bool), x4 (x1 + x7) x11 = (x4 x9 x11 && x4 x10 x11)) ∨ ∀ (x11 : Fin x1 → Bool), x4 (x1 + x7) x11 = (x4 x9 x11 || x4 x10 x11)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2 ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4 x3 x9 := by
  intro n m o f ho hin hg
  exact PEqualNP.Outside.L_meta_17846.main n m o f ho hin hg
