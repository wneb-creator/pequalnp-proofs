import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.CircuitAdapter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gateStep {α : Type} (op : GateOp → List α → α) (dflt : α)
    (ws : List α) (g : Gate) : List α :=
  ws ++ [op g.op (g.inputs.map fun i => ws.getD i dflt)]

lemma gateStep_length {α : Type} (op : GateOp → List α → α) (dflt : α) (ws : List α) (g : Gate) :
    (gateStep op dflt ws g).length = ws.length + 1 := by
  simp [gateStep]

lemma prefix_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
    (gs.foldl (gateStep op dflt) ws).getD i dflt = ws.getD i dflt := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [gateStep_length]; omega)]
    simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wireCount {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) :
    (gs.foldl (gateStep op dflt) ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, gateStep_length, List.length_cons]
    omega

lemma indexed_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
    (gs.foldl (gateStep op dflt) ws).getD (ws.length + j) dflt =
      op g.op (g.inputs.map fun i => (gs.foldl (gateStep op dflt) ws).getD i dflt) := by
  induction gs generalizing ws j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst g0
      rw [Nat.add_zero, List.foldl_cons, prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
      have hstep : (gateStep op dflt ws g).getD ws.length dflt =
          op g.op (g.inputs.map fun i => ws.getD i dflt) := by
        simp only [gateStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl ws.length)]
        simp
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt : i < ws.length := by simpa using hback i hi
      rw [prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
      simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      rw [List.foldl_cons]
      have hidx : ws.length + (j + 1) = (gateStep op dflt ws g0).length + j := by
        rw [gateStep_length]
        omega
      rw [hidx]
      exact ih (gateStep op dflt ws g0) j hj (by simpa only [hidx] using hback)


def wire (n : ℕ) (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def isOr (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .or => true
  | _ => false

def left (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0

def right (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

lemma wire_input (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wire n C i x = x ⟨i,hi⟩ := by
  have hi' : i < (List.ofFn x).length := by simpa using hi
  change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = _
  rw [prefix_value _ _ _ _ _ hi', List.getD_eq_getElem _ _ hi', List.getElem_ofFn]

lemma wire_outside (n : ℕ) (C : Circuit) (i : ℕ) (hi : n + C.size ≤ i)
    (x : Fin n → Bool) : wire n C i x = false := by
  change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simpa only [wireCount, List.length_ofFn, Circuit.size] using hi

lemma gate_mem (C : Circuit) (j : ℕ) (hj : j < C.size) : gateAt C j ∈ C.gates := by
  change j < C.gates.length at hj
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : (gateAt C j).inputs = [left C j, right C j] := by
  obtain ⟨a,b,hg⟩ := List.length_eq_two.mp (hC.2.2 _ (gate_mem C j hj))
  simp [left, right, hg]

lemma left_lt (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : left C j < n + j := by
  apply hC.2.1 j hj
  simp [gate_inputs n C hC j hj]

lemma right_lt (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : right C j < n + j := by
  apply hC.2.1 j hj
  simp [gate_inputs n C hC j hj]

lemma wire_gate (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) (x : Fin n → Bool) :
    wire n C (n+j) x =
      if isOr C j then wire n C (left C j) x || wire n C (right C j) x
      else wire n C (left C j) x && wire n C (right C j) x := by
  have hit : C.gates[j]? = some (gateAt C j) := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem?_eq_getElem hj
  have hback : ∀ i ∈ (gateAt C j).inputs, i < (List.ofFn x).length + j := by
    simpa only [List.length_ofFn] using hC.2.1 j hj
  have hv := indexed_value GateOp.eval false C.gates (List.ofFn x) j (gateAt C j) hit hback
  rw [List.length_ofFn, gate_inputs n C hC j hj] at hv
  rcases hC.1 _ (gate_mem C j hj) with hop | hop
  · rw [hop] at hv
    change wire n C (n+j) x =
      (wire n C (left C j) x && (wire n C (right C j) x && true)) at hv
    simpa [isOr, hop] using hv
  · rw [hop] at hv
    change wire n C (n+j) x =
      (wire n C (left C j) x || (wire n C (right C j) x || false)) at hv
    simpa [isOr, hop] using hv

lemma wire_monotone (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ i < n + C.size, ∀ x y : Fin n → Bool,
      (∀ p, x p = true → y p = true) → wire n C i x = true → wire n C i y = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi x y hxy hx
    by_cases hin : i < n
    · rw [wire_input n C i hin] at hx ⊢
      exact hxy _ hx
    · let j := i - n
      have hij : i = n + j := by dsimp [j]; omega
      have hj : j < C.size := by omega
      have ha := left_lt n C hC j hj
      have hb := right_lt n C hC j hj
      rw [hij, wire_gate n C hC j hj] at hx ⊢
      cases hop : isOr C j
      · simp only [hop, Bool.false_eq_true, ↓reduceIte] at hx ⊢
        obtain ⟨hx1,hx2⟩ := Bool.and_eq_true_iff.mp hx
        exact Bool.and_eq_true_iff.mpr
          ⟨ih (left C j) (by omega) (by omega) x y hxy hx1,
           ih (right C j) (by omega) (by omega) x y hxy hx2⟩
      · simp only [hop, ↓reduceIte] at hx ⊢
        rcases Bool.or_eq_true_iff.mp hx with hx | hx
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ih (left C j) (by omega) (by omega) x y hxy hx))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ih (right C j) (by omega) (by omega) x y hxy hx))

lemma eval_is_wire (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wire n C C.output x := rfl

end PEqualNP.Outside.L_meta_2602_aux.CircuitAdapter
