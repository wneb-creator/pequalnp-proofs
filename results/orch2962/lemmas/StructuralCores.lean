import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962.Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Core


/-! ## Section 1: Basic Circuit Evaluation & Monotonicity -/

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl wireStep w

lemma wires_eq_wiresFrom (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_len (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [wireStep]; omega

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (wireStep w g).length := by simp [wireStep]; omega
    change (wiresFrom gs (wireStep w g)).getD i false = w.getD i false
    rw [ih (wireStep w g) hi']
    simp only [wireStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_wiresFrom, wiresFrom_len, List.length_ofFn]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem hj

lemma wireVal_input (n : ℕ) (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal
  rw [wires_eq_wiresFrom, wiresFrom_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wireVal_ge_len (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool)
    (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_default _ _ (by rw [wires_len]; exact hw)]

lemma gateVal_eq_wireVal (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

lemma circuitFun_eq_wireVal (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

lemma gateVal_eval (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hRB : ReadsBack n C) (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hw_pre_len : (wiresFrom pre (List.ofFn x)).length = n + j := by
    rw [wiresFrom_len, List.length_ofFn, hpre_len]
  have h1 : C.wires (List.ofFn x) =
      wiresFrom post (wireStep (wiresFrom pre (List.ofFn x)) gj) := by
    rw [wires_eq_wiresFrom, hsplit, wiresFrom_append]
    rfl
  have hlt : n + j < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]
  unfold gateVal
  rw [h1, wiresFrom_getD_lt _ _ _ hlt]
  have hmid : (wireStep (wiresFrom pre (List.ofFn x)) gj).getD (n + j) false =
      gj.op.eval (gj.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) := by
    simp only [wireStep, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hw_pre_len),
      hw_pre_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  unfold wireVal
  rw [h1]
  have hilt2 : i < (wireStep (wiresFrom pre (List.ofFn x)) gj).length := by
    simp [wireStep, hw_pre_len]; omega
  rw [wiresFrom_getD_lt _ _ _ hilt2]
  simp only [wireStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : i < (wiresFrom pre (List.ofFn x)).length)]

lemma eval_and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma list_length_two {α : Type} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩

lemma graphFun_empty_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_empty_unitInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n) : graphFun G ∅ (unitInput p) = false := by
  cases h : graphFun G ∅ (unitInput p) with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
    simp [unitInput] at hu hv
    subst hu; subst hv
    exact (G.ne_of_adj huv rfl).elim

lemma graphFun_empty_pairInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty_true_iff G _).mpr
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

/-! ## Section 2: Cones and OR-Reachability -/


variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem on_ones (ao : IsAO2 n C) (w : ℕ) (hb : w < n + C.gates.length) :
    wireVal n C w (fun _ => true) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · rw [show w=(⟨w,hw⟩ : Fin n).val from rfl, wireVal_input]
    let j:=w-n
    have hj : j<C.gates.length := by dsimp [j];omega
    have eq : w=n+j := by dsimp [j];omega
    rw [eq, ← gateVal_eq_wireVal, gateVal_eval n C j hj ao.2.1]
    have mem:=gateAt_mem C j hj
    obtain ⟨a,b,e⟩:=list_length_two (ao.2.2 _ mem)
    have ha:=ao.2.1 j hj a (by simp [e])
    have hh:=ao.2.1 j hj b (by simp [e])
    rw [e]
    simp only [List.map_cons,List.map_nil,ih a (by omega) (by omega),ih b (by omega) (by omega)]
    rcases ao.1 _ mem with ep|ep <;> rw [ep] <;> rfl


lemma opnd_mem (ao : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hb : b.val < (gateAt C j).inputs.length := by rw [ao.2.2 _ (gateAt_mem C j hj)]; exact b.isLt
  exact List.mem_of_getElem? (by simp [opnd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb])

lemma imp_wire_not_input (w : ℕ) (hi : IsImpWire G C w) : n ≤ w := by
  by_contra hn
  have hw : w < n := by omega
  let v : Fin n := ⟨w, hw⟩
  have hval : wval C (unitInput v) w = true := by
    change wireVal n C w (unitInput v) = true
    rw [show w = v.val from rfl, wireVal_input]
    simp [unitInput]
  have hfalse := graphFun_empty_unitInput G v
  rw [hi.1 _ hval] at hfalse
  contradiction

lemma imp_operand_of_wire {w : ℕ} (hi : IsImpWire G C w) : IsImpOperand G C w := by
  have hn := imp_wire_not_input w hi
  refine ⟨hn, ?_⟩
  have he : n + (w - n) = w := by omega
  simpa only [IsImpGate, BelowF, gateVal, he] using hi

lemma or_below_operand (ao : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (hbelow : BelowF G C j) (b : Fin 2) :
    IsImpOperand G C (opnd C j b) := by
  apply imp_operand_of_wire
  have hm := opnd_mem ao hj b
  have hb := ao.2.1 j hj _ hm
  refine ⟨?_, ⟨fun _ => true, ?_⟩⟩
  · intro x hx
    apply hbelow x
    rw [gateVal_eval n C j hj ao.2.1, hor]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨opnd C j b, hm, hx⟩
  · exact on_ones ao _ (by omega)

lemma core_is_and (ao : IsAO2 n C) {j : ℕ} (hj : IsCore G C j) :
    (gateAt C j).op = GateOp.and := by
  rcases ao.1 _ (gateAt_mem C j hj.1) with ha | ho
  · exact ha
  · exact False.elim (hj.2.2.1 ⟨or_below_operand ao hj.1 ho hj.2.1.1 0,
      or_below_operand ao hj.1 ho hj.2.1.1 1⟩)

lemma fixed_live_or_below (hf : IsLiftFixedPoint G C) {j : ℕ}
    (hj : InOutputCone n C j) (hor : (gateAt C j).op = GateOp.or)
    (b : Fin 2) (hb : IsImpWire G C (opnd C j b)) : BelowF G C j := by
  by_contra hn
  exact hf ⟨j, hj.1, b, hj, hor, hn, hb⟩

end PEqualNP.Outside.L_meta_2962.Structural
