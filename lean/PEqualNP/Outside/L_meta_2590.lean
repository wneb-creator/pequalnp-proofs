import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.FirstNonbelow

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Core
  PEqualNP.EdgeOwnership PEqualNP.ReadTwo

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  change val C (List.ofFn x) i.val = x i
  rw [val_input (by simp) i.isLt]
  simp

lemma gate_formula {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map (wval C x)) := by
  change val C (List.ofFn x) (n + j) = _
  rw [val_gate (by simp) hj]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (back j hj w hw)]
  rfl

lemma first_nonbelow_raw_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ j < C.gates.length, InOutputCone n C j)
    (productive : ∀ j < C.gates.length, ∃ u v : Fin n,
      G.Adj u v ∧ gateVal n C j (pairInput u v) = true)
    (fresh : ∀ j < C.gates.length, ∀ v : Fin n, gateVal n C j ≠ fun x => x v)
    (exists_bad : ∃ j < C.gates.length, ¬ BelowF G C j) :
    ∃ j < C.gates.length, ∃ u v : Fin n, u ≠ v ∧
      (gateAt C j).op = .or ∧ gateVal n C j = fun x => x u || x v := by
  classical
  let j := Nat.find exists_bad
  have hj : j < C.gates.length := (Nat.find_spec exists_bad).1
  have bad : ¬ BelowF G C j := (Nat.find_spec exists_bad).2
  have earlier : ∀ k < j, BelowF G C k := by
    intro k hk
    by_contra hn
    exact Nat.find_min exists_bad hk ⟨by omega, hn⟩
  have hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ao.1 _ (gateAt_mem hj)
  obtain ⟨a, b, inputs⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
  have ha : a < n + j := ao.2.1 j hj a (by rw [inputs]; simp)
  have hb : b < n + j := ao.2.1 j hj b (by rw [inputs]; simp)
  have formula (x : Fin n → Bool) : gateVal n C j x =
      (gateAt C j).op.eval [wval C x a, wval C x b] := by
    rw [gate_formula ao.2.1 j hj x, inputs]
    rfl
  have imp (w : ℕ) (hw : w < n + j) (hn : n ≤ w) : IsImpWire G C w := by
    have hk : w - n < j := by omega
    have eq : n + (w - n) = w := by omega
    obtain ⟨u, v, _, hp⟩ := productive (w - n) (by omega)
    refine ⟨?_, pairInput u v, ?_⟩
    · intro x hx
      apply earlier (w - n) hk x
      simpa only [gateVal, eq, wval] using hx
    · simpa only [gateVal, eq, wval] using hp
  have both_inputs : a < n ∧ b < n := by
    constructor
    all_goals
      by_contra hn
      have hw : n ≤ _ := Nat.le_of_not_gt hn
      have hi := imp _ (by assumption) hw
      rcases hop with hand | hor
      · apply bad
        intro x hx
        rw [formula x, hand] at hx
        simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq,
          Bool.and_eq_true_iff] at hx
        apply hi.1 x
        first | exact hx.1 | exact hx.2
      · apply fixed
        refine ⟨j, hj, ?_⟩
        first
        | exact ⟨(0 : Fin 2), live j hj, hor, bad, by simpa [opnd, inputs] using hi⟩
        | exact ⟨(1 : Fin 2), live j hj, hor, bad, by simpa [opnd, inputs] using hi⟩
  let u : Fin n := ⟨a, both_inputs.1⟩
  let v : Fin n := ⟨b, both_inputs.2⟩
  have input_formula (x : Fin n → Bool) : gateVal n C j x =
      (gateAt C j).op.eval [x u, x v] := by
    rw [formula x, wval_input C x u, wval_input C x v]
  have ne : u ≠ v := by
    intro he
    apply fresh j hj u
    funext x
    rw [input_formula x, he]
    rcases hop with hand | hor
    · simp [hand, GateOp.eval]
    · simp [hor, GateOp.eval]
  rcases hop with hand | hor
  · obtain ⟨p, l, hpl, hpair⟩ := productive j hj
    rw [input_formula, hand] at hpair
    have hits : (u = p ∨ u = l) ∧ (v = p ∨ v = l) := by
      simpa [GateOp.eval, pairInput] using hpair
    have huv : G.Adj u v := by
      rcases hits.1 with hup | hul <;> rcases hits.2 with hvp | hvl
      · exact False.elim (ne (hup.trans hvp.symm))
      · rw [hup, hvl]
        exact hpl
      · rw [hul, hvp]
        exact G.symm.symm p l hpl
      · exact False.elim (ne (hul.trans hvl.symm))
    exfalso
    apply bad
    intro x hx
    rw [input_formula, hand] at hx
    have on : x u = true ∧ x v = true := by simpa [GateOp.eval] using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, on.1, on.2⟩
  · refine ⟨j, hj, u, v, ne, hor, ?_⟩
    funext x
    rw [input_formula, hor]
    simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2590.FirstNonbelow
