import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Alias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)


private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private lemma substGate_nok (k a : ℕ) (g : Gate) (h : NOkGate g) : NOkGate (substGate k a g) :=
  ⟨substGate_ok k a g h.1, fun hop => by simp [substGate]; exact h.2 hop⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_nok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hnok : ∀ g ∈ C.gates, NOkGate g) : ∀ g ∈ (deleteGate m C j a).gates, NOkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hnok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_nok _ _ g0 (hnok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma wiresFrom_subst_aux (k a : ℕ) (hka : a < k) :
    ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length + 1 → k ≤ w₂.length →
      (∀ i < w₁.length, w₂.getD (substWire k a i) false = w₁.getD i false) →
      ∀ i < (wiresFrom gs w₁).length,
        (wiresFrom (gs.map (substGate k a)) w₂).getD (substWire k a i) false =
          (wiresFrom gs w₁).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ hag i hi
    exact hag i hi
  | cons g rest ih =>
    intro w₁ w₂ hlen hk hag
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((substGate k a g).inputs.map fun i => w₂.getD i false) =
        (g.inputs.map fun i => w₁.getD i false) := by
      simp only [substGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w₁.length
      · exact hag i hi
      · have hge : w₂.length ≤ substWire k a i := by
          unfold substWire
          split_ifs <;> omega
        rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
    rw [hmap]
    show ∀ i < (wiresFrom rest _).length,
        (wiresFrom (rest.map (substGate k a)) (w₂ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).getD
          (substWire k a i) false = _
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < w₁.length
    · have hsublt : substWire k a i < w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
      exact hag i hlt
    · have hieq : i = w₁.length := by omega
      have hsubeq : substWire k a i = w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]

private lemma deleteGate_wires_eq (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length)
    (ha : a < m + j) (x : List Bool) (hx : x.length = m)
    (heq : (C.wires x).getD (m + j) false = (C.wires x).getD a false) :
    ∀ i < m + C.gates.length,
      ((deleteGate m C j a).wires x).getD (substWire (m + j) a i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length,
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a)) x).getD
          (substWire (m + j) a i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hag0 : ∀ i < w₁.length, w₂.getD (substWire (m + j) a i) false = w₁.getD i false := by
    intro i hi
    by_cases hlt : i < m + j
    · simp only [substWire, hlt, ↓reduceIte]
      rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]
    · have hieq : i = m + j := by omega
      subst hieq
      simp only [substWire, lt_irrefl, ↓reduceIte]
      have h1 : (C.wires x).getD (m + j) false = w₁.getD (m + j) false := by
        show (wiresFrom C.gates x).getD (m + j) false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        exact wiresFrom_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD a false = w₂.getD a false := by
        show (wiresFrom C.gates x).getD a false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        rw [wiresFrom_getD_lt _ _ _ (by omega), hw₁, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_lt _ _ _ _ (by omega)]
      rw [← h2, ← heq, h1]
  intro i hi
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  exact wiresFrom_subst_aux (m + j) a ha (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hag0
    i (by omega)


lemma erase_alias {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (heq : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j a, deleteGate_ok m C j a hok,
    by show (deleteGate m C j a).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j a hj], ?_⟩
  intro x
  show ((deleteGate m C j a).wires (List.ofFn x)).getD (substWire (m + j) a C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_wires_eq m C j a hj ha (List.ofFn x) (by simp) (heq x) C.output hlt
  · have hge1 : (deleteGate m C j a).gates.length + m ≤ substWire (m + j) a C.output := by
      rw [deleteGate_len m C j a hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j a).wires (List.ofFn x)).length =
        m + (deleteGate m C j a).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma wire_eval_gate {m : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin m → Bool) :
    (C.wires (List.ofFn x)).getD (m + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < m + j then (C.wires (List.ofFn x)).getD i false else false) := by
  show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false = _
  have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
  by_cases hi : i < m + j
  · simp only [hi, ↓reduceIte]
    have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [show C.wires (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl, hsp, wiresFrom_append]
    exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

lemma no_alias {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j) :
    ¬ ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false := by
  intro same
  obtain ⟨E, hE, hsize, correct⟩ := erase_alias C fan j a hj ha same
  have lower := minimal E hE (funext correct)
  change E.size ≤ C.size - 1 at hsize
  change j < C.size at hj
  omega

lemma no_unary_copy {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) :
    C.gates[j].inputs ≠ [a] := by
  intro inputs
  apply no_alias C fan minimal j a hj ha
  intro x
  rw [wire_eval_gate C j hj x, inputs]
  rcases op with op | op <;> simp [op, ha, GateOp.eval]

lemma no_duplicate_copy {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) :
    C.gates[j].inputs ≠ [a, a] := by
  intro inputs
  apply no_alias C fan minimal j a hj ha
  intro x
  rw [wire_eval_gate C j hj x, inputs]
  rcases op with op | op <;> simp [op, ha, GateOp.eval]

end PEqualNP.Outside.L_meta_2592_aux.Alias
