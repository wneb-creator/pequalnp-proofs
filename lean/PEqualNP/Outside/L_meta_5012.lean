import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_5012


namespace Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
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

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
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
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

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
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

-- Erasing an unread gate gives a smaller circuit, as in L_meta_7696.
def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega


def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

lemma delDead_wires_eq (n k : ℕ) (C : Circuit) (l : List Bool) (hl : l.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).wires l).getD w false = (C.wires l).getD (unshiftW n k w) false :=
  delDead_evalStep_eq false GateOp.eval n k C l hl hRB hk hno w

private lemma delDead_ao2 {n k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    IsAO2 n (delDead n k C) := by
  have mapped : ∀ g ∈ (delDead n k C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hm := List.mem_of_mem_eraseIdx hg'
    exact ⟨h.1 g' hm, by simp [shiftGate, h.2.2 g' hm]⟩
  exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C h.2.1 hk hno,
    fun g hg => (mapped g hg).2⟩

private def IsSmallest (n : ℕ) (C : Circuit) : Prop :=
  ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size

private lemma reader {n k : ℕ} {C : Circuit} (h : IsAO2 n C) (hmin : IsSmallest n C)
    (hk : k < C.gates.length) (hout : C.output ≠ n + k) :
    ∃ j < C.gates.length, n + k ∈ (gateAt C j).inputs := by
  by_contra hnot
  have hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs :=
    fun j hj hj' => hnot ⟨j, hj, hj'⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    unfold circuitFun Circuit.eval
    rw [delDead_wires_eq n k C _ List.length_ofFn h.2.1 hk hno]
    change (C.wires (List.ofFn x)).getD (unshiftW n k (shiftW n k C.output)) false = _
    rw [unshiftW_shiftW n k C.output hout]
  have hle := hmin _ (delDead_ao2 h hk hno) heq
  have hsize := delDead_size n k C hk
  omega

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma readData {j k : ℕ} (h : k ∈ readers n C j) :
    k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  simpa only [readers, Finset.mem_filter, Finset.mem_range] using h

lemma readLt (hAO : IsAO2 n C) {j k : ℕ} (h : k ∈ readers n C j) : j < k := by
  have hlt := hAO.2.1 k (readData h).1 _ (readData h).2
  omega

lemma junkNotBelow {j : ℕ} (hj : j ∈ junk G C) : ¬ BelowF G C j := by
  obtain ⟨_, _, x, hx, hf⟩ := junkData hj
  intro h
  exact Bool.false_ne_true (hf.symm.trans (h x hx))

lemma leastRead (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hd : ¬ BelowF G C j) : (readers n C j).Nonempty := by
  have hout : C.output ≠ n + j := by
    intro heq
    apply hd
    intro x hx
    have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
    rw [heq] at h
    exact h.symm.trans hx
  obtain ⟨k, hk, hin⟩ := reader hL.1
    (fun D hD heq => hL.2.2 D hD (heq.trans hL.2.1)) hj hout
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩⟩

lemma emptySide {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (h : side (n := n) C a b = ∅) : a ∈ centreless G C := by
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_⟩
  fin_cases b
  · exact Or.inl h
  · exact Or.inr h

-- A reader of a dirty gate with no input in its OR closure consumes one of the two budgets.
lemma classifyReader (hAO : IsAO2 n C) (hE : centreless G C = ∅) {j k : ℕ}
    (hd : ¬ BelowF G C j) (hz : orIn n C (n + j) = ∅) (hr : k ∈ readers n C j) :
    k ∈ junk G C ∨ k ∈ orN G C \ lam G C := by
  obtain ⟨hk, hin⟩ := readData hr
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hk hin
  have hs : side (n := n) C k b = ∅ := by
    change orIn n C (opnd C k b) = ∅
    rwa [← hb]
  rcases hAO.1 _ (gateAt_mem hk) with hand | hor
  · left
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      have ht : k ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hk (And.intro hand hbelow)
      have hcen := emptySide ht hs
      rw [hE] at hcen
      exact Finset.notMem_empty _ hcen
    have hw : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra hnone
      apply hnb
      intro x hx
      by_contra hf
      exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand, hk, hw⟩
  · right
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      apply hd
      intro x hx
      exact hbelow x ((val_or (n := n) (by simp) hk hor).mpr
        ⟨_, hin, hAO.2.1 k hk _ hin, hx⟩)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
        And.intro hk (And.intro hor hnb)
    · intro hlam
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
      have hn : (orIn n C (opnd C k b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, hz] at hn
      exact Finset.not_nonempty_empty hn

lemma orEmpty {m : ℕ} (h : ∀ w ∈ (gateAt C m).inputs, orIn n C w = ∅) :
    orIn n C (n + m) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w, hw, tail⟩
  · have := u.isLt
    omega
  · obtain ⟨k, _, he, _, hi, _⟩ := hw
    have e : k = m := by omega
    subst k
    have hu' := reach_mem_orIn u tail
    rw [h w hi] at hu'
    exact Finset.notMem_empty _ hu'

lemma twoInputs (hAO : IsAO2 n C) {m p q : ℕ} (hm : m < C.gates.length)
    (hpq : p ≠ q) (hp : p ∈ (gateAt C m).inputs) (hq : q ∈ (gateAt C m).inputs)
    {w : ℕ} (hw : w ∈ (gateAt C m).inputs) : w = p ∨ w = q := by
  obtain ⟨r, s, hrs⟩ := binaryInputs hAO hm
  simp only [hrs, List.mem_cons, List.not_mem_nil, or_false] at hp hq hw
  omega

lemma dichotomy (hL : IsLeastAO G C) (hT : TopForm G C) (hJ : (junk G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card ∨
      ∃ a b m : ℕ, junk G C = {a, b} ∧ InCone n C a b ∧ centreless G C = ∅ ∧
        readers n C a = {b} ∧ readers n C b = {m} ∧ orN G C \ lam G C = {m} ∧
        ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
          gateVal n C a (pairInput u v) = true ∧ gateVal n C b (pairInput u v) = true := by
  by_cases h : 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card
  · exact Or.inl h
  right
  have hE : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hSmall : (orN G C \ lam G C).card ≤ 1 := by omega
  obtain ⟨a, b, hab, hPair⟩ : ∃ a b : ℕ, a < b ∧ junk G C = {a, b} := by
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hJ
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i, j, hlt, he⟩
    · exact ⟨j, i, hlt, he.trans (Finset.pair_comm _ _)⟩
  have ha : a ∈ junk G C := by simp [hPair]
  have hb : b ∈ junk G C := by simp [hPair]
  have noLaterJunk {k : ℕ} (hk : k ∈ junk G C) (hlt : b < k) : False := by
    simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have junkReader {j k : ℕ} (hj : j ∈ junk G C) (hr : k ∈ readers n C j) :
      k ∈ junk G C ∨ k ∈ orN G C \ lam G C :=
    classifyReader hL.1 hE (junkNotBelow hj) (andRawEmpty (junkData hj).2.1) hr
  obtain ⟨m, hbm⟩ := leastRead hL (junkData hb).1 (junkNotBelow hb)
  have hbmLt := readLt hL.1 hbm
  have hm := (junkReader hb hbm).resolve_left (fun hk => noLaterJunk hk hbmLt)
  have mUnique {k : ℕ} (hk : k ∈ orN G C \ lam G C) : k = m :=
    Finset.card_le_one.mp hSmall k hk m hm
  have hM : orN G C \ lam G C = {m} := by
    ext k
    exact ⟨fun hk => Finset.mem_singleton.mpr (mUnique hk),
      fun hk => Finset.mem_singleton.mp hk ▸ hm⟩
  have hB : readers n C b = {m} := by
    ext k
    refine ⟨fun hk => Finset.mem_singleton.mpr (mUnique ?_),
      fun hk => Finset.mem_singleton.mp hk ▸ hbm⟩
    exact (junkReader hb hk).resolve_left (fun hj => noLaterJunk hj (readLt hL.1 hk))
  have noAM (ham : m ∈ readers n C a) : False := by
    have hmData : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using (Finset.mem_sdiff.mp hm).1
    have hmEmpty : orIn n C (n + m) = ∅ := by
      apply orEmpty
      intro w hw
      rcases twoInputs hL.1 hmData.1 (show n + a ≠ n + b by omega)
          (readData ham).2 (readData hbm).2 hw with rfl | rfl
      · exact andRawEmpty (junkData ha).2.1
      · exact andRawEmpty (junkData hb).2.1
    obtain ⟨k, hmk⟩ := leastRead hL hmData.1 hmData.2.2
    have hmkLt := readLt hL.1 hmk
    rcases classifyReader hL.1 hE hmData.2.2 hmEmpty hmk with hk | hk
    · exact noLaterJunk hk (hbmLt.trans hmkLt)
    · have := mUnique hk
      omega
  have aRead {k : ℕ} (hk : k ∈ readers n C a) : k = b := by
    rcases junkReader ha hk with hj | hj
    · have hlt := readLt hL.1 hk
      simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
      omega
    · exact (noAM (mUnique hj ▸ hk)).elim
  obtain ⟨k, hak⟩ := leastRead hL (junkData ha).1 (junkNotBelow ha)
  have habRead : b ∈ readers n C a := aRead hak ▸ hak
  have hA : readers n C a = {b} := by
    ext i
    exact ⟨fun hi => Finset.mem_singleton.mpr (aRead hi),
      fun hi => Finset.mem_singleton.mp hi ▸ habRead⟩
  have habCone : InCone n C a b := (inCone_iff n C a b).mpr
    ⟨(readData habRead).1, a, hab, (readData habRead).2, Or.inl rfl⟩
  refine ⟨a, b, m, hPair, habCone, hE, hA, hB, hM, ?_⟩
  intro u v he
  obtain ⟨t, ht, d, j, hj, path, hv⟩ := residualTrace hL hT he
  have hjb : j = b := by
    simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h
    · exfalso
      subst j
      rcases lastOrBefore (orReaches_reach a _ path).1 with heq | ⟨r, hr, hop, hin, _, _⟩
      · have hs : side (n := n) C t d = ∅ := by
          change orIn n C (opnd C t d) = ∅
          rw [heq]
          exact andRawEmpty (junkData ha).2.1
        have hbad := emptySide ht hs
        rw [hE] at hbad
        exact Finset.notMem_empty _ hbad
      · have hr' : r ∈ readers n C a := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hin⟩
        rw [aRead hr', (junkData hb).2.1] at hop
        cases hop
    · exact h
  subst j
  have haVal := (val_and (n := n) (by simp) (junkData hb).1 (junkData hb).2.1).mp hv
    (n + a) (readData habRead).2
  exact ⟨haVal.2, hv⟩

end Budget


section RootHelpers1

open PEqualNP.EdgeOwnership

def setOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)


lemma setOr_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    setOr A (pairInput u v) = decide (u ∈ A ∨ v ∈ A) := by
  simp [setOr, pairInput, and_or_left, exists_or]





def Increasing {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma graph_eq_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Increasing f)
    (hbelow : ∀ x, f x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hpairs : ∀ u v, G.Adj u v → f (pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro h
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  apply hf (pairInput u v) x ?_ (hpairs u v huv)
  intro w hw
  simp only [pairInput, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv


lemma clean_context_below {α : Type*} (F H K : α → Bool) (context : α → Bool → Bool)
    (hcontext : ∀ x b c, (b = true → c = true) →
      context x b = true → context x c = true)
    (hK : ∀ x, K x = true → F x = true)
    (hOld : ∀ x, context x (H x) = true → F x = true) :
    ∀ x, context x (K x) = true → F x = true := by
  intro x hx
  by_cases hk : K x = true
  · exact hK x hk
  · apply hOld x
    exact hcontext x (K x) (H x) (fun h => (hk h).elim) hx

lemma clean_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (context : (Fin n → Bool) → Bool → Bool) (H K : (Fin n → Bool) → Bool)
    (hcontext : ∀ x y b c, (∀ v, x v = true → y v = true) →
      (b = true → c = true) → context x b = true → context y c = true)
    (hKmono : Increasing K)
    (hKclean : ∀ x, K x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hcritical : ∀ u v, G.Adj u v → context (pairInput u v) false = false →
      K (pairInput u v) = true)
    (hF : ∀ x, context x (H x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    (fun x => context x (K x)) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_pair G
  · intro x y hxy hx
    exact hcontext x y (K x) (K y) hxy (hKmono x y hxy) hx
  · exact clean_context_below _ H K context
      (fun x b c => hcontext x x b c (fun _ => id)) hKclean
      (fun x hx => (hF x).symm ▸ hx)
  · intro u v huv
    have hEdge : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
        decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    by_cases hz : context (pairInput u v) false = true
    · exact hcontext _ _ false (K (pairInput u v)) (fun _ => id)
        (fun h => Bool.false_ne_true h |>.elim) hz
    · have hk := hcritical u v huv (Bool.eq_false_iff.mpr hz)
      have hOld : context (pairInput u v) (H (pairInput u v)) = true :=
        (hF (pairInput u v)).trans hEdge
      exact hcontext _ _ (H (pairInput u v)) (K (pairInput u v))
        (fun _ => id) (fun _ => hk) hOld

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma shared_raw_critical_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : (Fin n → Bool) → Bool) (R S : Finset (Fin n)) (r u v : Fin n)
    (hr : r ∈ R)
    (hclean : ∀ x, ((setOr R x || H x) && setOr S x) = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hR : setOr R (pairInput u v) = false)
    (hS : setOr S (pairInput u v) = true) :
    r ≠ u ∧ r ≠ v ∧ ∃ w : Fin n, (w = u ∨ w = v) ∧ G.Adj r w ∧
      ∀ x, H x = true → x w = true →
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
  have hRu : u ∉ R := by
    intro h
    have ht : setOr R (pairInput u v) = true := by simp [setOr_pair, h]
    exact Bool.false_ne_true (hR.symm.trans ht)
  have hRv : v ∉ R := by
    intro h
    have ht : setOr R (pairInput u v) = true := by simp [setOr_pair, h]
    exact Bool.false_ne_true (hR.symm.trans ht)
  have hs : u ∈ S ∨ v ∈ S := by simpa only [setOr_pair, decide_eq_true_eq] using hS
  obtain ⟨w, hw, hwS⟩ : ∃ w, (w = u ∨ w = v) ∧ w ∈ S := by
    rcases hs with hs | hs
    · exact ⟨u, Or.inl rfl, hs⟩
    · exact ⟨v, Or.inr rfl, hs⟩
  refine ⟨fun h => hRu (h ▸ hr), fun h => hRv (h ▸ hr), w, hw, ?_, ?_⟩
  · apply (graph_pair_iff G r w).mp
    apply hclean (pairInput r w)
    have h1 : setOr R (pairInput r w) = true := by simp [setOr_pair, hr]
    have h2 : setOr S (pairInput r w) = true := by simp [setOr_pair, hwS]
    simp [h1, h2]
  · intro x hx hxw
    apply hclean x
    have hs : setOr S x = true := by
      simpa only [setOr, decide_eq_true_eq] using (show ∃ w ∈ S, x w = true from ⟨w, hwS, hxw⟩)
    simp [hx, hs]

end RootHelpers1

namespace Geometry

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a b u v : Fin n) (hab : a ≠ b)
    (hau : G.Adj a u) (hbu : G.Adj b u) (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
  exact Finset.card_le_one.mp (h4 a b hab) u
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau, hbu⟩) v
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hav, hbv⟩)

lemma common_neighbor_color {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (r u v : Fin n) (hru : G.Adj r u) (hrv : G.Adj r v) : s u = s v := by
  have h1 := hbip r u hru
  have h2 := hbip r v hrv
  cases hr : s r <;> cases hu : s u <;> cases hv : s v <;> simp_all

def clauseClean {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Fin k → Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, x w = true →
    (∀ i, ∃ a ∈ S i, x a = true) → graphFun G ∅ x = true

lemma bool_same_away (u v w : Bool) (hu : u ≠ w) (hv : v ≠ w) : u = v := by
  cases u <;> cases v <;> cases w <;> simp_all

lemma monochrome_filter_universal {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (d w : Fin n) (hdw : s d ≠ s w)
    (hpair : ∀ i, d ∈ S i ∨ w ∈ S i)
    (hclean : clauseClean G S w) :
    ∃ i, t i ≠ s w ∧ ∀ a ∈ S i, G.Adj w a := by
  classical
  by_contra hnone
  let x : Fin n → Bool := fun a => decide (a = w ∨ (s a ≠ s w ∧ ¬ G.Adj w a))
  have hw : x w = true := by simp [x]
  have hhit : ∀ i, ∃ a ∈ S i, x a = true := by
    intro i
    by_cases hi : t i = s w
    · have hwi : w ∈ S i := by
        rcases hpair i with hd | hw
        · exact False.elim (hdw ((hmono i d hd).trans hi))
        · exact hw
      exact ⟨w, hwi, hw⟩
    · by_contra hmiss
      have huni : ∀ a ∈ S i, G.Adj w a := by
        intro a ha
        by_contra hwa
        have hax : x a = true := by
          apply decide_eq_true
          exact Or.inr ⟨by rw [hmono i a ha]; exact hi, hwa⟩
        exact hmiss ⟨a, ha, hax⟩
      exact hnone ⟨i, hi, huni⟩
  obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp (hclean x hw hhit)
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with hu | ⟨huc, hun⟩
  · subst u
    rcases hv with hv | ⟨hvc, hvn⟩
    · subst v
      exact G.loopless.irrefl w huv
    · exact hvn huv
  · rcases hv with hv | ⟨hvc, hvn⟩
    · subst v
      exact hun huv.symm
    · exact hbip u v huv (bool_same_away (s u) (s v) (s w) huc hvc)

lemma monochrome_common_reader_star {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (R : Fin n → Fin n → Prop) (hRn : ∃ d w, R d w)
    (hcolor : ∀ d w, R d w → s d ≠ s w)
    (hpair : ∀ d w, R d w → ∀ i, d ∈ S i ∨ w ∈ S i)
    (hclean : ∀ d w, R d w → clauseClean G S w)
    (r : Fin n) (hraw : ∀ d w, R d w → G.Adj r w)
    (hne : ∀ d w, R d w → r ≠ d) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      ∀ d w, R d w → w = v ∧ d ∈ S i := by
  obtain ⟨d0, w0, h0⟩ := hRn
  obtain ⟨i0, hi0, huniv0⟩ := monochrome_filter_universal G s hbip S t hmono
    d0 w0 (hcolor d0 w0 h0) (hpair d0 w0 h0) (hclean d0 w0 h0)
  have hd0 : d0 ∈ S i0 := by
    rcases hpair d0 w0 h0 i0 with h | h
    · exact h
    · exact False.elim (hi0 (hmono i0 w0 h).symm)
  refine ⟨w0, i0, huniv0, ?_⟩
  intro d w h
  have hsame := common_neighbor_color G s hbip r w w0 (hraw d w h) (hraw d0 w0 h0)
  obtain ⟨i, hi, huniv⟩ := monochrome_filter_universal G s hbip S t hmono
    d w (hcolor d w h) (hpair d w h) (hclean d w h)
  have hd0i : d0 ∈ S i := by
    rcases hpair d0 w0 h0 i with hh | hh
    · exact hh
    · exact False.elim (hi ((hmono i w0 hh).symm.trans hsame.symm))
  have hww0 := common_neighbor_unique G h4 r d0 w w0 (hne d0 w0 h0)
    (hraw d w h) (huniv d0 hd0i).symm (hraw d0 w0 h0) (huniv0 d0 hd0).symm
  refine ⟨hww0, ?_⟩
  rcases hpair d w h i0 with hh | hh
  · exact hh
  · exact False.elim (hi0 ((hmono i0 w hh).symm.trans hsame))

lemma monochrome_unoriented_star {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (E : Finset (Fin n × Fin n)) (hEn : E.Nonempty)
    (hadj : ∀ p ∈ E, G.Adj p.1 p.2)
    (hpair : ∀ p ∈ E, ∀ i, p.1 ∈ S i ∨ p.2 ∈ S i)
    (r : Fin n) (hne : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2)
    (hfilter : ∀ p ∈ E,
      (clauseClean G S p.1 ∧ G.Adj r p.1) ∨
      (clauseClean G S p.2 ∧ G.Adj r p.2)) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      ∀ p ∈ E, (p.1 = v ∧ p.2 ∈ S i) ∨ (p.2 = v ∧ p.1 ∈ S i) := by
  let R : Fin n → Fin n → Prop := fun d w =>
    ((d, w) ∈ E ∨ (w, d) ∈ E) ∧ clauseClean G S w ∧ G.Adj r w
  have hRn : ∃ d w, R d w := by
    obtain ⟨⟨d, w⟩, h⟩ := hEn
    rcases hfilter (d, w) h with ⟨hc, hr⟩ | ⟨hc, hr⟩
    · exact ⟨w, d, Or.inr h, hc, hr⟩
    · exact ⟨d, w, Or.inl h, hc, hr⟩
  have hcolR : ∀ d w, R d w → s d ≠ s w := by
    intro d w h
    rcases h.1 with h | h
    · exact hbip d w (hadj (d, w) h)
    · exact hbip d w (hadj (w, d) h).symm
  have hpR : ∀ d w, R d w → ∀ i, d ∈ S i ∨ w ∈ S i := by
    intro d w h i
    rcases h.1 with h | h
    · exact hpair (d, w) h i
    · exact (hpair (w, d) h i).symm
  have hnR : ∀ d w, R d w → r ≠ d := by
    intro d w h
    rcases h.1 with h | h
    · exact (hne (d, w) h).1
    · exact (hne (w, d) h).2
  obtain ⟨v, i, hu, hv⟩ := monochrome_common_reader_star G s hbip h4 S t hmono R hRn
    hcolR hpR (fun _ _ h => h.2.1) r (fun _ _ h => h.2.2) hnR
  refine ⟨v, i, hu, ?_⟩
  intro p hp
  rcases hfilter p hp with ⟨hc, hr⟩ | ⟨hc, hr⟩
  · exact Or.inl (hv p.2 p.1 ⟨Or.inr hp, hc, hr⟩)
  · exact Or.inr (hv p.1 p.2 ⟨Or.inl hp, hc, hr⟩)

end Geometry

section RootHelpers2

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def clauseProduct {n k : ℕ} (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i, ∃ a ∈ S i, x a = true)

lemma common_raw_clean_replacement {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (context : (Fin n → Bool) → Bool → Bool)
    (hcontext : ∀ x y b c, (∀ v, x v = true → y v = true) →
      (b = true → c = true) → context x b = true → context y c = true)
    (hF : ∀ x, context x (clauseProduct S x) = graphFun G ∅ x)
    (E : Finset (Fin n × Fin n)) (hEn : E.Nonempty)
    (hadj : ∀ p ∈ E, G.Adj p.1 p.2)
    (hcut : ∀ p ∈ E, context (pairInput p.1 p.2) false = false)
    (hcover : ∀ u v, G.Adj u v → context (pairInput u v) false = false → (u, v) ∈ E)
    (r : Fin n)
    (hshared : ∀ p ∈ E, ∃ R T : Finset (Fin n), r ∈ R ∧
      (∀ x, ((setOr R x || clauseProduct S x) && setOr T x) = true → graphFun G ∅ x = true) ∧
      setOr R (pairInput p.1 p.2) = false ∧ setOr T (pairInput p.1 p.2) = true) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      (fun x => context x (x v && setOr (S i) x)) = graphFun G ∅ := by
  have hH : ∀ p ∈ E, clauseProduct S (pairInput p.1 p.2) = true := by
    intro p hp
    have he := (hF (pairInput p.1 p.2)).trans ((graph_pair_iff G p.1 p.2).mpr (hadj p hp))
    cases h : clauseProduct S (pairInput p.1 p.2)
    · rw [h, hcut p hp] at he
      cases he
    · rfl
  have hpair : ∀ p ∈ E, ∀ i, p.1 ∈ S i ∨ p.2 ∈ S i := by
    intro p hp i
    have hh := (decide_eq_true_eq.mp (hH p hp)) i
    obtain ⟨a, ha, hx⟩ := hh
    simp only [pairInput, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
  have hdata : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2 ∧
      ((Geometry.clauseClean G S p.1 ∧ G.Adj r p.1) ∨
        (Geometry.clauseClean G S p.2 ∧ G.Adj r p.2)) := by
    intro p hp
    obtain ⟨R, T, hr, hclean, hR, hT⟩ := hshared p hp
    obtain ⟨h1, h2, w, hw, hadjw, hcw⟩ :=
      shared_raw_critical_filter G (clauseProduct S) R T r p.1 p.2 hr hclean hR hT
    have hc : Geometry.clauseClean G S w := by
      intro x hx hh
      exact hcw x (decide_eq_true hh) hx
    refine ⟨h1, h2, ?_⟩
    rcases hw with rfl | rfl
    · exact Or.inl ⟨hc, hadjw⟩
    · exact Or.inr ⟨hc, hadjw⟩
  obtain ⟨v, i, hu, hc⟩ := Geometry.monochrome_unoriented_star G s hbip h4 S t hmono
    E hEn hadj hpair r (fun p hp => ⟨(hdata p hp).1, (hdata p hp).2.1⟩)
    (fun p hp => (hdata p hp).2.2)
  refine ⟨v, i, hu, ?_⟩
  apply clean_critical_replacement G context (clauseProduct S) (fun x => x v && setOr (S i) x)
    hcontext ?_ ?_ ?_ hF
  · intro x y hxy hx
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at hx ⊢
    obtain ⟨hv, a, ha, hax⟩ := hx
    exact ⟨hxy v hv, a, ha, hxy a hax⟩
  · intro x hx
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at hx
    obtain ⟨hv, a, ha, hax⟩ := hx
    exact (Geometry.graph_true G x).mpr ⟨v, a, hu a ha, hv, hax⟩
  · intro u w huw hzero
    rcases hc (u, w) (hcover u w huw hzero) with ⟨h, hm⟩ | ⟨h, hm⟩
    · dsimp at h hm
      subst u
      simp [pairInput, setOr_pair, hm]
    · dsimp at h hm
      subst w
      simp [pairInput, setOr_pair, hm]

end RootHelpers2


namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  exact Budget.foldl_length gs x

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]


lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  exact Budget.foldl_getD_lt gs x i hi

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  intro j hj
  exact Budget.foldl_getD_gate gs x j hj

def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section Evaluation1
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end Evaluation1

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩



lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩
lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_eq_of_zero {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) (hz : val n C x (n + j) = false) :
    ∀ w < n + C.gates.length, cutVal n C {j} x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [cutVal, u_in hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hk
    by_cases hd : k ∈ ({j} : Finset ℕ)
    · have hkj : k = j := Finset.mem_singleton.mp hd
      subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hz]
    rw [val_rec C hC x k hk]
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb]
      exact congrArg₂ Bool.or ia ib
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb]
      simp only [List.any_nil, Bool.or_false]
      exact congrArg₂ Bool.and ia ib

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega



lemma cutVal_eq_set {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      cutVal n C {j} x w =
        (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [cutVal, u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (C.gates.set j ⟨GateOp.or, []⟩).length := by simpa using hk
    have hrec := run_gate (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x) k hk'
    rw [List.length_ofFn] at hrec
    by_cases hkj : k = j
    · subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hrec]
      simp [GateOp.eval]
    have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
    have hgt : (C.gates.set j ⟨GateOp.or, []⟩)[k] = C.gates[k] := by
      simp [List.getElem_set, hkj, Ne.symm hkj]
    obtain ⟨heq, hinp, ha, hb, hop⟩ := gate2 hC hk
    rw [hgt, heq, hinp] at hrec
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at hrec
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    rcases hop with hop | hop
    · have hA : isAnd C k = true := by simp [isAnd, hop]
      rw [cutVal, u_and hnot hA ha hb, hrec, hop]
      simp only [List.any_nil, Bool.or_false, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      exact congrArg₂ Bool.and ia ib
    · have hA : isAnd C k = false := by simp [isAnd, hop]
      rw [cutVal, u_or hnot hA ha hb, hrec, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      exact congrArg₂ Bool.or ia ib

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  have hkill : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
    change (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn (pairInput p q))).getD C.output false = false
    rw [← cutVal_eq_set C hL.1 j (pairInput p q) C.output (output_lt G C hL.2.1 hE)]
    exact hcut
  refine ⟨p, q, hpq, ?_, hkill⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma least_gate_critical_edge_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  exact least_gate_critical_edge G C hL (least_nonempty_of_gate G C hL j hj) j hj


end CriticalEdge


namespace Context

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  exact Budget.foldl_length gs w

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  exact Budget.foldl_getD_lt gs w i hi

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩




lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj


lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]






lemma AO2_monotone2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨hAO.1 g hg, by rw [hAO.2.2 g hg]⟩

def constantGate (b : Bool) : Gate := if b then ⟨GateOp.and, []⟩ else off

lemma constantGate_bit (w : List Bool) (b : Bool) : gateBit w (constantGate b) = b := by
  cases b <;> rfl

def gateContext {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (b : Bool) : Bool :=
  circuitFun n (patch C j (constantGate b)) x

lemma same_bit_wires {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = gateBit (earlierWires C j w) h) :
    (patch C j g).wires w = (patch C j h).wires w := by
  rw [wires_patch hj, wires_patch hj]
  simp only [stepWire, hbit]

lemma gateContext_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length)
    (x y : Fin n → Bool) (b c : Bool)
    (hxy : ∀ v, x v = true → y v = true) (hbc : b = true → c = true) :
    gateContext C j x b = true → gateContext C j y c = true := by
  have hC : Monotone2 C := AO2_monotone2 hAO
  have hp : WiresLE (earlierWires C j (List.ofFn x)) (earlierWires C j (List.ofFn y)) :=
    fold_mono _ (fun g hg => monoGate_of_mem hC (List.mem_of_mem_take hg)) (ofFn_mono hxy)
  have ha : WiresLE
      (stepWire (earlierWires C j (List.ofFn x)) (constantGate b))
      (stepWire (earlierWires C j (List.ofFn y)) (constantGate c)) := by
    apply append_mono hp
    simpa only [constantGate_bit] using hbc
  have hw : WiresLE
      ((patch C j (constantGate b)).wires (List.ofFn x))
      ((patch C j (constantGate c)).wires (List.ofFn y)) := by
    rw [wires_patch hj, wires_patch hj]
    exact fold_mono _ (fun g hg => monoGate_of_mem hC (List.mem_of_mem_drop hg)) ha
  exact hw.2 C.output

lemma gateContext_patch_bit {n : ℕ} {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) (g : Gate) (x : Fin n → Bool) :
    gateContext C j x (gateBit (earlierWires C j (List.ofFn x)) g) =
      circuitFun n (patch C j g) x := by
  have hw := same_bit_wires hj
    (constantGate (gateBit (earlierWires C j (List.ofFn x)) g)) g (List.ofFn x)
    (constantGate_bit _ _)
  exact congrArg (fun w : List Bool => w.getD C.output false) hw

lemma gateContext_patch_value {n : ℕ} {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) (g : Gate) (x : Fin n → Bool) :
    gateContext C j x (gateVal n (patch C j g) j x) = circuitFun n (patch C j g) x := by
  rw [patch_bit hj]
  exact gateContext_patch_bit hj g x

lemma gateContext_original {n : ℕ} {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateContext C j x (gateVal n C j x) = circuitFun n C x := by
  have h := gateContext_patch_value hj C.gates[j] x
  rwa [original_patch hj] at h






lemma earlierWires_length {n : ℕ} (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    (earlierWires C j (List.ofFn x)).length = n + j := by
  unfold earlierWires
  rw [fold_length]
  simp [Nat.min_eq_left (Nat.le_of_lt hj)]

lemma earlierWires_value {n : ℕ} (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) (w : ℕ) (hw : w < n + j) :
    (earlierWires C j (List.ofFn x)).getD w false = wireVal n C w x := by
  have hlen := earlierWires_length C hj x
  have heq := wires_patch hj C.gates[j] (List.ofFn x)
  rw [original_patch hj] at heq
  change _ = (C.wires (List.ofFn x)).getD w false
  rw [heq, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
  simp [stepWire, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (show w < (earlierWires C j (List.ofFn x)).length by omega)]

lemma raw_and_wire_bit {n : ℕ} (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) (v : Fin n)
    (w : ℕ) (hw : w < n + j) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and, [v.val, w]⟩ =
      (x v && wireVal n C w x) := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [earlierWires_value C hj x w hw]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), ofFn_getD]

lemma gateContext_star_patch {n : ℕ} {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) (v : Fin n) (w : ℕ) (hw : w < n + j)
    (x : Fin n → Bool) :
    gateContext C j x (x v && wireVal n C w x) =
      circuitFun n (patch C j ⟨GateOp.and, [v.val, w]⟩) x := by
  rw [← raw_and_wire_bit C hj x v w hw]
  exact gateContext_patch_bit hj _ x


lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output


lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv


end Context

namespace Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma lone_and_reader_orReach {g h w : ℕ}
    (hread : readers n C g = {h}) (hhand : (gateAt C h).op = GateOp.and)
    (hr : OrReaches n C w g) : w = n + g := by
  rcases lastOrBefore (orReaches_reach g w hr).1 with he | ⟨k, hk, hop, hin, _, _⟩
  · exact he
  · have hkr : k ∈ readers n C g :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩
    rw [hread, Finset.mem_singleton] at hkr
    rw [hkr, hhand] at hop
    cases hop

lemma tight_other_operand_pure {g h : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h})
    (hread : readers n C g = {h}) (b : Fin 2)
    (hne : opnd C h b ≠ n + g) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C h b) = true ↔
      ∃ u ∈ side (n := n) C h b, x u = true := by
  have hh : h ∈ junk G C := by simp [hpair]
  obtain ⟨hlen, hand, _⟩ := junkData hh
  constructor
  · intro hv
    obtain ⟨w, hr, hw, hcase⟩ := or_trace (n := n) (C := C)
      (x := List.ofFn x) (by simp) (opnd C h b) hv
    rcases hcase with hwlt | ⟨k, hk, rfl, hkop⟩
    · refine ⟨⟨w, hwlt⟩, reach_mem_orIn _ hr, ?_⟩
      exact (val_ofFn C x ⟨w, hwlt⟩).symm.trans hw
    · exfalso
      have hkand := (hAO.1 _ (gateAt_mem hk)).resolve_right hkop
      have hreach : OrReaches n C (opnd C h b) k := reach_orReaches hr k rfl hk
      have hkj := operandOrAndJunk hAO hT hlen hand hreach hkand
      simp only [hpair, Finset.mem_insert, Finset.mem_singleton] at hkj
      rcases hkj with rfl | rfl
      · exact hne (lone_and_reader_orReach hread hand hreach)
      · have hle := orStep_le hr
        have hlt := opndBound hAO hlen b
        omega
  · rintro ⟨u, hu, hux⟩
    exact sideVal hu hux


lemma common_raw_reaches {h m w : ℕ} (hread : readers n C h = {m})
    (hneq : w ≠ n + h) (hr : OrReaches n C w h)
    {r : Fin n} (hrm : r ∈ orIn n C (n + m)) : r ∈ orIn n C w := by
  rcases lastOrBefore (orReaches_reach h w hr).1 with he | ⟨k, hk, _, hin, _, hpath⟩
  · exact (hneq he).elim
  · have hkr : k ∈ readers n C h :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩
    rw [hread, Finset.mem_singleton] at hkr
    subst k
    exact reach_mem_orIn r (hpath.trans (mem_orIn_reach r hrm))

lemma top_operand_ne_junk {a h : ℕ} (hE : centreless G C = ∅)
    (ha : a ∈ tops G C) (hh : h ∈ junk G C) (b : Fin 2) :
    opnd C a b ≠ n + h := by
  intro heq
  have hempty : side (n := n) C a b = ∅ := by
    change orIn n C (opnd C a b) = ∅
    rw [heq]
    exact andRawEmpty (junkData hh).2.1
  have hbad := emptySide ha hempty
  rw [hE] at hbad
  exact Finset.notMem_empty _ hbad


lemma top_operand_support {g h a : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h})
    (hread : readers n C g = {h}) (hE : centreless G C = ∅)
    (ha : a ∈ tops G C) (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔
      (∃ u ∈ side (n := n) C a b, x u = true) ∨
      (OrReaches n C (opnd C a b) h ∧ gateVal n C h x = true) := by
  obtain ⟨halen, haand, _⟩ := topData ha
  have hh : h ∈ junk G C := by simp [hpair]
  constructor
  · intro hv
    obtain ⟨w, hr, hw, hcase⟩ := or_trace (n := n) (C := C)
      (x := List.ofFn x) (by simp) (opnd C a b) hv
    rcases hcase with hwlt | ⟨k, hk, rfl, hkop⟩
    · exact Or.inl ⟨⟨w, hwlt⟩, reach_mem_orIn _ hr,
        (val_ofFn C x ⟨w, hwlt⟩).symm.trans hw⟩
    · have hkand := (hAO.1 _ (gateAt_mem hk)).resolve_right hkop
      have hreach : OrReaches n C (opnd C a b) k := reach_orReaches hr k rfl hk
      have hkj := operandOrAndJunk hAO hT halen haand hreach hkand
      simp only [hpair, Finset.mem_insert, Finset.mem_singleton] at hkj
      rcases hkj with rfl | rfl
      · exact (top_operand_ne_junk hE ha (show k ∈ junk G C by simp [hpair]) b
          (lone_and_reader_orReach hread (junkData hh).2.1 hreach)).elim
      · exact Or.inr ⟨hreach, hw⟩
  · rintro (⟨u, hu, hux⟩ | ⟨hr, hv⟩)
    · exact sideVal hu hux
    · exact orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hv

lemma top_other_no_reach {h a : ℕ} (hAO : IsAO2 n C)
    (ha : a ∈ tops G C) (hh : h ∈ junk G C) (b : Fin 2)
    (hb : OrReaches n C (opnd C a b) h) :
    ¬ OrReaches n C (opnd C a (1 - b)) h := by
  intro hb'
  apply junkNotBelow hh
  intro x hx
  apply (topData ha).2.2 x
  apply (andValOperands hAO (topData ha).1 (topData ha).2.1 x).mpr
  intro d
  have hd : d = b ∨ d = 1 - b := by omega
  rcases hd with rfl | rfl
  · exact orStep_up (n := n) (by simp) (orReaches_reach h _ hb).1 hx
  · exact orStep_up (n := n) (by simp) (orReaches_reach h _ hb').1 hx

lemma selected_top_shared_raw {g h m a : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hE : centreless G C = ∅) (ha : a ∈ tops G C) (b : Fin 2)
    (u v r : Fin n) (hr : r ∈ orIn n C (n + m))
    (haval : gateVal n C a (pairInput u v) = true)
    (hraw : ¬ ∃ z ∈ side (n := n) C a b, pairInput u v z = true) :
    r ∈ side (n := n) C a b ∧
    (∀ x : Fin n → Bool,
      ((∃ z ∈ side (n := n) C a b, x z = true) ∨ gateVal n C h x = true) →
      (∃ z ∈ side (n := n) C a (1 - b), x z = true) → graphFun G ∅ x = true) ∧
    (∃ z ∈ side (n := n) C a (1 - b), pairInput u v z = true) := by
  have hh : h ∈ junk G C := by simp [hpair]
  have hvals := (andValOperands hAO (topData ha).1 (topData ha).2.1 _).mp haval
  obtain ⟨hb, _⟩ := ((top_operand_support hAO hT hpair hreadg hE ha b _).mp
    (hvals b)).resolve_left hraw
  have hother := ((top_operand_support hAO hT hpair hreadg hE ha (1 - b) _).mp
    (hvals (1 - b))).resolve_right (fun hz => top_other_no_reach hAO ha hh b hb hz.1)
  refine ⟨common_raw_reaches hreadh (top_operand_ne_junk hE ha hh b) hb hr, ?_, hother⟩
  intro x hxb hxo
  apply (topData ha).2.2 x
  apply (andValOperands hAO (topData ha).1 (topData ha).2.1 x).mpr
  have hvb : val C (List.ofFn x) (opnd C a b) = true :=
    (top_operand_support hAO hT hpair hreadg hE ha b x).mpr (hxb.imp_right (fun hx => ⟨hb, hx⟩))
  have hvo : val C (List.ofFn x) (opnd C a (1 - b)) = true := by
    obtain ⟨z, hz, hzx⟩ := hxo
    exact sideVal hz hzx
  intro d
  have hd : d = b ∨ d = 1 - b := by omega
  rcases hd with rfl | rfl
  · exact hvb
  · exact hvo

lemma selected_top_shared_boolean {g h m a : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hE : centreless G C = ∅) (ha : a ∈ tops G C) (b : Fin 2)
    (u v r : Fin n) (hr : r ∈ orIn n C (n + m))
    (haval : gateVal n C a (pairInput u v) = true)
    (hraw : ¬ ∃ z ∈ side (n := n) C a b, pairInput u v z = true) :
    ∃ R T : Finset (Fin n), r ∈ R ∧
      (∀ x : Fin n → Bool,
        ((decide (∃ z ∈ R, x z = true) || gateVal n C h x) &&
          decide (∃ z ∈ T, x z = true)) = true → graphFun G ∅ x = true) ∧
      (decide (∃ z ∈ R, pairInput u v z = true) : Bool) = false ∧
      (decide (∃ z ∈ T, pairInput u v z = true) : Bool) = true := by
  obtain ⟨hrr, hclean, ht⟩ := selected_top_shared_raw hAO hT hpair hreadg hreadh hE
    ha b u v r hr haval hraw
  refine ⟨side (n := n) C a b, side (n := n) C a (1 - b), hrr, ?_, by simp [hraw], by simp [ht]⟩
  intro x hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hx
  exact hclean x hx.1 hx.2


end Tight

namespace CutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

def off (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩

lemma off_gateAt {C : Circuit} {h j : ℕ} (hj : j < C.gates.length) (hjne : j ≠ h) :
    gateAt (off C h) j = gateAt C j := by
  rw [gateAt_eq (show j < (off C h).gates.length by simpa [off] using hj), gateAt_eq hj]
  simp [off, List.getElem_set, hjne, Ne.symm hjne]

lemma off_or_reach {n : ℕ} {C : Circuit} {h : ℕ}
    (hh : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) {w z : ℕ}
    (hr : Relation.ReflTransGen (OrStep n C) w z)
    (hv : val (off C h) (List.ofFn x) z = true) :
    val (off C h) (List.ofFn x) w = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    have hkh : k ≠ h := by intro heq; subst k; rw [hh] at hop; cases hop
    have heq := off_gateAt hk hkh
    apply (val_or (n := n) (by simp) (show k < (off C h).gates.length by simpa [off] using hk)
      (show (gateAt (off C h) k).op = GateOp.or by rw [heq]; exact hop)).mpr
    exact ⟨_, by rw [heq]; exact hin, hlt, ih⟩

lemma off_side_val {n : ℕ} {C : Circuit} {h : ℕ}
    (hh : (gateAt C h).op = GateOp.and) (x : Fin n → Bool)
    {a : ℕ} {b : Fin 2} {u : Fin n}
    (hu : u ∈ side (n := n) C a b) (hxu : x u = true) :
    val (off C h) (List.ofFn x) (opnd C a b) = true := by
  apply off_or_reach hh x (mem_orIn_reach u hu)
  rw [val_ofFn]
  exact hxu

lemma critical_top_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (h : ℕ) (hjunk : h ∈ junk G C) (u v : Fin n) (huv : G.Adj u v)
    (hcut : circuitFun n (off C h) (pairInput u v) = false) :
    ∃ a ∈ tops G C, ∃ b : Fin 2,
      gateVal n C a (pairInput u v) = true ∧
      val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) = false ∧
      (∀ t ∈ side (n := n) C a b, t ≠ u ∧ t ≠ v) := by
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hF x
  obtain ⟨a, ha, hnotor, hr, hav⟩ := edge_trace G (graphFun G ∅)
    (fun p q hpq => (graphFun_pair G p q).mp hpq) hout u v ((graphFun_pair G u v).mpr huv)
  have hand : (gateAt C a).op = GateOp.and :=
    (hAO.1 _ (gateAt_mem ha)).resolve_right hnotor
  have hbelow : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  have hatop : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro ha (And.intro hand hbelow)
  have hah : a ≠ h := by
    intro heq
    subst a
    exact junkNotBelow hjunk hbelow
  have hgAnd := (junkData hjunk).2.1
  have hzero : val (off C h) (List.ofFn (pairInput u v)) (n + a) = false := by
    cases hv : val (off C h) (List.ofFn (pairInput u v)) (n + a) with
    | false => rfl
    | true =>
      have ho := off_or_reach hgAnd (pairInput u v) hr hv
      change circuitFun n (off C h) (pairInput u v) = true at ho
      rw [hcut] at ho
      cases ho
  have hex : ∃ b : Fin 2, val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
    by_contra! hall
    have htrue : val (off C h) (List.ofFn (pairInput u v)) (n + a) = true := by
      apply (val_and (n := n) (by simp)
        (show a < (off C h).gates.length by simpa [off] using ha)
        (show (gateAt (off C h) a).op = GateOp.and by rw [off_gateAt ha hah]; exact hand)).mpr
      intro w hw
      rw [off_gateAt ha hah] at hw
      obtain ⟨b, rfl⟩ := inputsAsOpnd hAO ha hw
      refine ⟨opndBound hAO ha b, ?_⟩
      cases hv : val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) with
      | false => exact ((hall b) hv).elim
      | true => rfl
    rw [hzero] at htrue
    cases htrue
  obtain ⟨b, hb⟩ := hex
  refine ⟨a, hatop, b, ?_, hb, ?_⟩
  · rwa [gateVal_eq_val]
  · intro t ht
    constructor <;> intro heq
    · subst t
      have := off_side_val hgAnd (pairInput u v) ht (pairInput_left u v)
      rw [hb] at this
      cases this
    · subst t
      have := off_side_val hgAnd (pairInput u v) ht (pairInput_right u v)
      rw [hb] at this
      cases this

end CutTrace

namespace TightCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget PEqualNP.Outside.L_meta_5012.CutTrace
  PEqualNP.Outside.L_meta_5012.Tight

lemma critical_edge_shared_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) (g h m : ℕ) (hpair : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hE : centreless G C = ∅) (r : Fin n) (hr : r ∈ orIn n C (n + m))
    (u v : Fin n) (huv : G.Adj u v)
    (hcut : circuitFun n (off C h) (pairInput u v) = false) :
    ∃ R T : Finset (Fin n), r ∈ R ∧
      (∀ x : Fin n → Bool,
        ((decide (∃ z ∈ R, x z = true) || gateVal n C h x) &&
          decide (∃ z ∈ T, x z = true)) = true → graphFun G ∅ x = true) ∧
      (decide (∃ z ∈ R, pairInput u v z = true) : Bool) = false ∧
      (decide (∃ z ∈ T, pairInput u v z = true) : Bool) = true := by
  have hjunk : h ∈ junk G C := by rw [hpair]; simp
  obtain ⟨a, ha, b, haval, _, hraw⟩ :=
    critical_top_operand G C hAO hF h hjunk u v huv hcut
  apply selected_top_shared_boolean hAO hT hpair hreadg hreadh hE ha b u v r hr haval
  rintro ⟨z, hz, hzp⟩
  have hzuv : z = u ∨ z = v := by simpa [pairInput] using hzp
  exact hzuv.elim (hraw z hz).1 (hraw z hz).2

end TightCut

namespace SerialReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

def replaceGate (C : Circuit) (h : ℕ) (q : Gate) : Circuit := ⟨C.gates.set h q, C.output⟩

lemma replaceGate_at_ne {C : Circuit} {h k : ℕ} (q : Gate) (hkh : k ≠ h) :
    gateAt (replaceGate C h q) k = gateAt C k := by
  simp [replaceGate, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkh)]

lemma replaceGate_at_self {C : Circuit} {h : ℕ} (q : Gate) (hh : h < C.gates.length) :
    gateAt (replaceGate C h q) h = q := by
  rw [gateAt_eq (show h < (replaceGate C h q).gates.length by simpa [replaceGate] using hh)]
  simp [replaceGate, List.getElem_set]

lemma replaceGate_AO {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (h : ℕ) (q : Gate)
    (hqop : q.op = GateOp.and ∨ q.op = GateOp.or) (hqlen : q.inputs.length = 2)
    (hqback : ∀ w ∈ q.inputs, w < n + h) : IsAO2 n (replaceGate C h q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_or_eq_of_mem_set ha with ha | rfl
    · exact hAO.1 a ha
    · exact hqop
  · intro k hk w hw
    have hk' : k < C.gates.length := by simpa [replaceGate] using hk
    by_cases hkh : k = h
    · subst k
      rw [replaceGate_at_self q hk'] at hw
      exact hqback w hw
    · rw [replaceGate_at_ne q hkh] at hw
      exact hAO.2.1 k hk' w hw
  · intro a ha
    rcases List.mem_or_eq_of_mem_set ha with ha | rfl
    · exact hAO.2.2 a ha
    · exact hqlen

lemma sole_reader_replacement_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (g h : ℕ) (hg : g ∈ junk G C) (hread : readers n C g = {h})
    (q : Gate) (hqop : q.op = GateOp.and ∨ q.op = GateOp.or)
    (hqlen : q.inputs.length = 2) (hqback : ∀ w ∈ q.inputs, w < n + h)
    (hqavoid : n + g ∉ q.inputs)
    (hnew : circuitFun n (replaceGate C h q) = graphFun G ∅) : False := by
  have hmem : h ∈ readers n C g := by rw [hread]; simp
  have hh := (readData hmem).1
  have hgN := (junkData hg).1
  have hout : C.output ≠ n + g := by
    intro heq
    apply junkNotBelow hg
    intro x hx
    have hf : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
    rw [heq] at hf
    exact hf.symm.trans hx
  let D := replaceGate C h q
  have hD : IsAO2 n D := replaceGate_AO hL.1 h q hqop hqlen hqback
  have hsmall : ∀ E : Circuit, IsAO2 n E → circuitFun n E = circuitFun n D → D.size ≤ E.size := by
    intro E hE hEF
    have hs := hL.2.2 E hE (hEF.trans hnew)
    simpa [D, replaceGate, Circuit.size] using hs
  obtain ⟨k, hk, hkg⟩ := PEqualNP.Outside.L_meta_5012.Budget.reader hD hsmall
    (show g < D.gates.length by simpa [D, replaceGate] using hgN) hout
  have hk' : k < C.gates.length := by simpa [D, replaceGate] using hk
  by_cases hkh : k = h
  · subst k
    have hgate : gateAt D h = q := replaceGate_at_self q hh
    rw [hgate] at hkg
    exact hqavoid hkg
  · have hgate : gateAt D k = gateAt C k := replaceGate_at_ne q hkh
    rw [hgate] at hkg
    have hkr : k ∈ readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk', hkg⟩
    rw [hread, Finset.mem_singleton] at hkr
    exact hkh hkr

end SerialReplacement

namespace Color

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

lemma lam_has_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + k), G.Adj u c := by
  classical
  obtain ⟨_, _, _, a, ha, b, hc, hr⟩ := Finset.mem_filter.mp hk
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  refine ⟨c, ?_⟩
  intro u hu
  have huval : val C (List.ofFn (pairInput u c)) (n + k) = true :=
    reach_var_val (pairInput u c) _ u (mem_orIn_reach u hu) (pairInput_left u c)
  have hbval := orStep_up (n := n) (by simp) (orReaches_reach k _ hr).1 huval
  have hcside : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hcval := sideVal hcside (pairInput_right u c)
  apply (graphFun_pair G u c).mp
  apply (topData ha).2.2 _
  apply (andValOperands hAO (topData ha).1 (topData ha).2.1 _).mpr
  intro d
  have hd : d = b ∨ d = 1 - b := by omega
  rcases hd with rfl | rfl
  · exact hbval
  · exact hcval

lemma lam_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (k : ℕ) (hk : k ∈ lam G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  obtain ⟨c, hc⟩ := lam_has_common_neighbor G C hAO k hk
  intro u hu v hv
  have huc := hs u c (hc u hu)
  have hvc := hs v c (hc v hv)
  cases hsu : s u <;> cases hsv : s v <;> cases hsc : s c <;> simp_all

lemma tight_earlier_or_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (m : ℕ)
    (htight : orN G C \ lam G C = {m}) (k : ℕ) (hkm : k < m)
    (hk : k ∈ orN G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  apply lam_monochromatic G C hAO s hs k
  by_contra hn
  have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk, hn⟩
  rw [htight, Finset.mem_singleton] at hm
  omega

end Color

namespace Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget PEqualNP.Outside.L_meta_5012.Tight

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma early_operand_pure {g h : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h}) (hgh : g < h)
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C g b) = true ↔
      ∃ u ∈ side (n := n) C g b, x u = true := by
  have hg : g ∈ junk G C := by simp [hpair]
  obtain ⟨glen, gand, _⟩ := junkData hg
  constructor
  · intro hv
    obtain ⟨w, hr, hw, hcase⟩ := or_trace (n := n) (C := C)
      (x := List.ofFn x) (by simp) (opnd C g b) hv
    rcases hcase with hwlt | ⟨k, hk, rfl, hkop⟩
    · exact ⟨⟨w, hwlt⟩, reach_mem_orIn _ hr, (val_ofFn C x ⟨w, hwlt⟩).symm.trans hw⟩
    · exfalso
      have hkand := (hAO.1 _ (gateAt_mem hk)).resolve_right hkop
      have hreach : OrReaches n C (opnd C g b) k := reach_orReaches hr k rfl hk
      have hkj := operandOrAndJunk hAO hT glen gand hreach hkand
      simp only [hpair, Finset.mem_insert, Finset.mem_singleton] at hkj
      have hle := orStep_le hr
      have hlt := opndBound hAO glen b
      omega
  · rintro ⟨u, hu, hux⟩
    exact sideVal hu hux

lemma early_side_nonempty {g h : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h}) (hgh : g < h) (b : Fin 2) :
    (side (n := n) C g b).Nonempty := by
  have hg : g ∈ junk G C := by simp [hpair]
  obtain ⟨glen, gand, x, hx, _⟩ := junkData hg
  have hv := (andValOperands hAO glen gand x).mp hx b
  obtain ⟨u, hu, _⟩ := (early_operand_pure hAO hT hpair hgh b x).mp hv
  exact ⟨u, hu⟩

lemma raw_nonempty_not_below {k : ℕ} (hraw : (orIn n C (n + k)).Nonempty) :
    ¬ BelowF G C k := by
  obtain ⟨u, hu⟩ := hraw
  intro hbelow
  have hv : gateVal n C k (pairInput u u) = true :=
    reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
  exact G.irrefl ((graphFun_pair G u u).mp (hbelow _ hv))

lemma raw_factor_color {m : ℕ} (hAO : IsAO2 n C)
    (htight : orN G C \ lam G C = {m})
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (w : ℕ) (hwm : w < n + m) (hraw : (orIn n C w).Nonempty) :
    ∃ t : Bool, ∀ u ∈ orIn n C w, s u = t := by
  classical
  obtain ⟨u, hu⟩ := hraw
  refine ⟨s u, ?_⟩
  by_cases hwn : w < n
  · intro v hv
    have raw_eq (a : Fin n) (ha : a ∈ orIn n C w) : a.val = w := by
      simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain he | ⟨k, _, hr, _, _⟩ := ha
      · exact he
      · exact (Nat.not_le_of_lt hwn hr.1).elim
    have huv : v = u := Fin.ext ((raw_eq v hv).trans (raw_eq u hu).symm)
    rw [huv]
  · have hm : m ∈ orN G C := (Finset.mem_sdiff.mp (show m ∈ orN G C \ lam G C by simp [htight])).1
    have hmdata : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hm
    have hmlen := hmdata.1
    have hweq : w = n + (w - n) := by omega
    have hklen : w - n < C.gates.length := by omega
    have hkop : (gateAt C (w - n)).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hklen) with hand | hor
      · have hz := andRawEmpty (n := n) hand
        rw [← hweq] at hz
        exact (Finset.notMem_empty u (hz ▸ hu)).elim
      · exact hor
    have hnb : ¬ BelowF G C (w - n) := raw_nonempty_not_below (G := G)
      (hweq ▸ (show (orIn n C w).Nonempty from ⟨u, hu⟩))
    have hkor : w - n ∈ orN G C := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
        And.intro hklen (And.intro hkop hnb)
    intro v hv
    have hmono := PEqualNP.Outside.L_meta_5012.Color.tight_earlier_or_monochromatic
      G C hAO s hs m htight (w - n) (by omega) hkor
    rw [← hweq] at hmono
    exact hmono v hv u hu

lemma nested_and_value {g h : ℕ} (hAO : IsAO2 n C)
    (hh : h ∈ junk G C) (b : Fin 2) (hb : opnd C h b = n + g) (x : Fin n → Bool) :
    gateVal n C h x = true ↔ gateVal n C g x = true ∧
      val C (List.ofFn x) (opnd C h (1 - b)) = true := by
  have hv := andValOperands hAO (junkData hh).1 (junkData hh).2.1 x
  constructor
  · intro hx
    have hall := hv.mp hx
    refine ⟨?_, hall (1 - b)⟩
    have hgb := hall b
    rw [hb] at hgb
    exact hgb
  · intro hx
    apply hv.mpr
    intro d
    have hd : d = b ∨ d = 1 - b := by omega
    rcases hd with rfl | rfl
    · rw [hb]
      exact hx.1
    · exact hx.2

lemma third_factor {g h : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h}) (hgh : g < h)
    (hread : readers n C g = {h}) :
    ∃ p : ℕ, p < n + h ∧ p ≠ n + g ∧ (orIn n C p).Nonempty ∧
      (∀ x : Fin n → Bool, val C (List.ofFn x) p = true ↔ ∃ u ∈ orIn n C p, x u = true) ∧
      (∀ x : Fin n → Bool, gateVal n C h x = true ↔
        gateVal n C g x = true ∧ val C (List.ofFn x) p = true) := by
  have hg : g ∈ junk G C := by simp [hpair]
  have hh : h ∈ junk G C := by simp [hpair]
  have hgr : h ∈ readers n C g := by simp [hread]
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO (junkData hh).1 (readData hgr).2
  have hb' := hb.symm
  by_cases hdup : opnd C h (1 - b) = n + g
  · refine ⟨opnd C g 0, ?_, ?_, early_side_nonempty hAO hT hpair hgh 0,
      early_operand_pure hAO hT hpair hgh 0, ?_⟩
    · have := opndBound hAO (junkData hg).1 (0 : Fin 2)
      omega
    · exact ne_of_lt (opndBound hAO (junkData hg).1 (0 : Fin 2))
    · intro x
      rw [nested_and_value hAO hh b hb' x, hdup]
      constructor
      · intro hx
        exact ⟨hx.1, (andValOperands hAO (junkData hg).1 (junkData hg).2.1 x).mp hx.1 0⟩
      · intro hx
        exact ⟨hx.1, hx.1⟩
  · have hpure := tight_other_operand_pure hAO hT hpair hread (1 - b) hdup
    have hpne : (orIn n C (opnd C h (1 - b))).Nonempty := by
      obtain ⟨hlen, hand, x, hx, _⟩ := junkData hh
      obtain ⟨u, hu, _⟩ := (hpure x).mp ((andValOperands hAO hlen hand x).mp hx (1 - b))
      exact ⟨u, hu⟩
    exact ⟨opnd C h (1 - b), opndBound hAO (junkData hh).1 (1 - b), hdup, hpne,
      hpure, nested_and_value hAO hh b hb'⟩

lemma three_raw_factors {g h m : ℕ} (hAO : IsAO2 n C)
    (hT : TopForm G C) (hpair : junk G C = {g, h}) (hgh : g < h) (hhm : h < m)
    (hread : readers n C g = {h}) (htight : orN G C \ lam G C = {m})
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v) :
    ∃ (w : Fin 3 → ℕ) (t : Fin 3 → Bool),
      (∀ i, w i < n + h ∧ w i ≠ n + g ∧ (orIn n C (w i)).Nonempty) ∧
      (∀ i (x : Fin n → Bool), val C (List.ofFn x) (w i) = true ↔
        ∃ u ∈ orIn n C (w i), x u = true) ∧
      (∀ i, ∀ u ∈ orIn n C (w i), s u = t i) ∧
      (∀ x : Fin n → Bool, gateVal n C h x = true ↔
        ∀ i, ∃ u ∈ orIn n C (w i), x u = true) := by
  classical
  have hg : g ∈ junk G C := by simp [hpair]
  obtain ⟨p, hplen, hpneq, hpne, hpure, hsem⟩ := third_factor hAO hT hpair hgh hread
  let w : Fin 3 → ℕ := ![opnd C g 0, opnd C g 1, p]
  have hdata : ∀ i, w i < n + h ∧ w i ≠ n + g ∧ (orIn n C (w i)).Nonempty := by
    intro i
    fin_cases i
    · have := opndBound hAO (junkData hg).1 (0 : Fin 2)
      exact ⟨by dsimp [w]; omega, ne_of_lt this, early_side_nonempty hAO hT hpair hgh 0⟩
    · have := opndBound hAO (junkData hg).1 (1 : Fin 2)
      exact ⟨by dsimp [w]; omega, ne_of_lt this, early_side_nonempty hAO hT hpair hgh 1⟩
    · exact ⟨hplen, hpneq, hpne⟩
  have hwpure : ∀ i (x : Fin n → Bool), val C (List.ofFn x) (w i) = true ↔
      ∃ u ∈ orIn n C (w i), x u = true := by
    intro i x
    fin_cases i
    · exact early_operand_pure hAO hT hpair hgh 0 x
    · exact early_operand_pure hAO hT hpair hgh 1 x
    · exact hpure x
  have hcol : ∀ i, ∃ t : Bool, ∀ u ∈ orIn n C (w i), s u = t := by
    intro i
    exact raw_factor_color hAO htight s hs (w i) (by have := (hdata i).1; omega) (hdata i).2.2
  choose t ht using hcol
  refine ⟨w, t, hdata, hwpure, ht, ?_⟩
  intro x
  rw [hsem x, andValBoth hAO (junkData hg).1 (junkData hg).2.1 x]
  constructor
  · rintro ⟨⟨h0, h1⟩, hp⟩ i
    fin_cases i
    · exact (hwpure 0 x).mp h0
    · exact (hwpure 1 x).mp h1
    · exact (hwpure 2 x).mp hp
  · intro hx
    exact ⟨⟨(hwpure 0 x).mpr (hx 0), (hwpure 1 x).mpr (hx 1)⟩,
      (hwpure 2 x).mpr (hx 2)⟩

end Factor

namespace TightAssembly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012 PEqualNP.Outside.L_meta_5012.Budget

lemma contradiction_of_raw_clauses {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g h m : ℕ)
    (hpair : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hE : centreless G C = ∅) (hM : orN G C \ lam G C = {m})
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool) (w : Fin k → ℕ)
    (hw : ∀ i, w i < n + h ∧ w i ≠ n + g)
    (hwire : ∀ i x, wireVal n C (w i) x = setOr (S i) x)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (hproduct : ∀ x, gateVal n C h x = clauseProduct S x) : False := by
  classical
  have hg : g ∈ junk G C := by rw [hpair]; simp
  have hh : h ∈ junk G C := by rw [hpair]; simp
  have hghmem : h ∈ readers n C g := by rw [hreadg]; simp
  have hhmmem : m ∈ readers n C h := by rw [hreadh]; simp
  have hgh := readLt hL.1 hghmem
  have hhm := readLt hL.1 hhmmem
  have hhN := (junkData hh).1
  have hrawne : (orIn n C (n + m)).Nonempty := by
    have hm : m ∈ orN G C \ lam G C := by rw [hM]; simp
    have hmd : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
        (Finset.mem_sdiff.mp hm).1
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨j, hj⟩ := leastRead hL hmd.1 hmd.2.2
    have hmj := readLt hL.1 hj
    rcases classifyReader hL.1 hE hmd.2.2 hz hj with hjunk | hjM
    · rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hjunk
      rcases hjunk with rfl | rfl <;> omega
    · rw [hM, Finset.mem_singleton] at hjM
      omega
  obtain ⟨r, hr⟩ := hrawne
  let E : Finset (Fin n × Fin n) := Finset.univ.filter fun p =>
    G.Adj p.1 p.2 ∧ circuitFun n (CutTrace.off C h) (pairInput p.1 p.2) = false
  have hEn : E.Nonempty := by
    obtain ⟨u, v, huv, _, hcut⟩ := CriticalEdge.least_gate_critical_edge_of_least G C hL h hhN
    refine ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, ?_⟩⟩
    exact hcut
  have hadj : ∀ p ∈ E, G.Adj p.1 p.2 := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hcut : ∀ p ∈ E, Context.gateContext C h (pairInput p.1 p.2) false = false :=
    fun p hp => (Finset.mem_filter.mp hp).2.2
  have hcover : ∀ u v, G.Adj u v → Context.gateContext C h (pairInput u v) false = false →
      (u, v) ∈ E := by
    intro u v huv hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hz⟩
  have hF : ∀ x, Context.gateContext C h x (clauseProduct S x) = graphFun G ∅ x := by
    intro x
    rw [← hproduct x, Context.gateContext_original hhN]
    exact congrFun hL.2.1 x
  have hshared : ∀ p ∈ E, ∃ R T : Finset (Fin n), r ∈ R ∧
      (∀ x, ((setOr R x || clauseProduct S x) && setOr T x) = true → graphFun G ∅ x = true) ∧
      setOr R (pairInput p.1 p.2) = false ∧ setOr T (pairInput p.1 p.2) = true := by
    intro p hp
    obtain ⟨R, T, hR, hclean, hno, hyes⟩ := TightCut.critical_edge_shared_raw G C hL.1 hL.2.1
      hT g h m hpair hreadg hreadh hE r hr p.1 p.2 (hadj p hp) (hcut p hp)
    refine ⟨R, T, hR, ?_, hno, hyes⟩
    intro x hx
    apply hclean x
    simpa only [setOr, hproduct] using hx
  obtain ⟨v, i, _, heq⟩ := common_raw_clean_replacement G s hbip h4 S t hmono
    (Context.gateContext C h) (Context.gateContext_mono hL.1 hhN) hF E hEn hadj hcut hcover r hshared
  let q : Gate := ⟨GateOp.and, [v.val, w i]⟩
  apply SerialReplacement.sole_reader_replacement_impossible G C hL g h hg hreadg q
    (Or.inl rfl) rfl
  · intro z hz
    change z ∈ [v.val, w i] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · have := v.isLt; omega
    · exact (hw i).1
  · change n + g ∉ [v.val, w i]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by have := v.isLt; omega, Ne.symm (hw i).2⟩
  · funext x
    have hc := congrFun heq x
    rw [← hwire i x] at hc
    have hs := Context.gateContext_star_patch hhN v (w i) (hw i).1 x
    exact hs.symm.trans hc

end TightAssembly

namespace TightAssembly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012 PEqualNP.Outside.L_meta_5012.Budget

lemma tight_nested_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g h m : ℕ)
    (hpair : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hE : centreless G C = ∅) (hM : orN G C \ lam G C = {m}) : False := by
  have hgm : h ∈ readers n C g := by rw [hreadg]; simp
  have hhm : m ∈ readers n C h := by rw [hreadh]; simp
  obtain ⟨w, t, hw, heval, hmono, hprod⟩ := Factor.three_raw_factors hL.1 hT hpair
    (readLt hL.1 hgm) (readLt hL.1 hhm) hreadg hM s hbip
  apply contradiction_of_raw_clauses G C s hbip h4 hL hT g h m hpair hreadg hreadh hE hM
    (fun i => orIn n C (w i)) t w (fun i => ⟨(hw i).1, (hw i).2.1⟩)
  · intro i x
    apply Bool.eq_iff_iff.mpr
    simpa only [setOr, decide_eq_true_eq, Budget.val, CleanedNonEdge.wireVal] using heval i x
  · exact hmono
  · intro x
    apply Bool.eq_iff_iff.mpr
    simpa only [clauseProduct, setOr, decide_eq_true_eq] using hprod x

lemma two_junk_resource_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hj : (junk G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  rcases dichotomy hL hT hj with hbound | ⟨g, h, m, hpair, _, hE, hreadg, hreadh, hM, _⟩
  · exact hbound
  · exact (tight_nested_impossible G C s hbip h4 hL hT g h m hpair hreadg hreadh hE hM).elim

end TightAssembly


namespace Geometry

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

/-- A clean product of monochromatic OR clauses accepts only edges in one star,
and an existing clause supplies a clean star containing all those edges. -/
lemma clean_monochrome_product_star {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, ∃ a ∈ S i, x a = true) → graphFun G ∅ x = true)
    (hne : ∃ u v : Fin n, ∀ i, u ∈ S i ∨ v ∈ S i) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      ∀ u w : Fin n, (∀ j, u ∈ S j ∨ w ∈ S j) →
        (u = v ∧ w ∈ S i) ∨ (w = v ∧ u ∈ S i) := by
  have pair_adj : ∀ u v : Fin n, (∀ i, u ∈ S i ∨ v ∈ S i) → G.Adj u v := by
    intro u v hp
    apply (graph_pair_iff G u v).mp
    apply hclean (pairInput u v)
    intro i
    rcases hp i with hu | hv
    · exact ⟨u, hu, by simp [pairInput]⟩
    · exact ⟨v, hv, by simp [pairInput]⟩
  obtain ⟨a, b, hab⟩ := hne
  have habcol : s a ≠ s b := hbip a b (pair_adj a b hab)
  let R : Fin n → Fin n → Prop := fun u v =>
    s u = s a ∧ s v = s b ∧ ∀ i, u ∈ S i ∨ v ∈ S i
  have hbase : R a b := ⟨rfl, rfl, hab⟩
  have cross : ∀ u v d w, R u v → R d w → G.Adj u w := by
    intro u v d w huv hdw
    apply pair_adj u w
    intro i
    rcases huv.2.2 i with hu | hv
    · exact Or.inl hu
    · rcases hdw.2.2 i with hd | hw
      · have heq : s a = s b := hdw.1.symm.trans
          ((hmono i d hd).trans ((hmono i v hv).symm.trans huv.2.1))
        exact (habcol heq).elim
      · exact Or.inr hw
  have same_end : ∀ u v d w, R u v → R d w → u = d ∨ v = w := by
    intro u v d w huv hdw
    by_cases hud : u = d
    · exact Or.inl hud
    · exact Or.inr (common_neighbor_unique G h4 u d v w hud
        (pair_adj u v huv.2.2) (cross d w u v hdw huv)
        (cross u v d w huv hdw) (pair_adj d w hdw.2.2))
  have oriented_star :
      (∀ u v, R u v → u = a) ∨ (∀ u v, R u v → v = b) := by
    by_cases hleft : ∀ u v, R u v → u = a
    · exact Or.inl hleft
    · right
      push Not at hleft
      obtain ⟨d, w, hdw, hda⟩ := hleft
      have hwb : w = b := (same_end d w a b hdw hbase).resolve_left hda
      intro u v huv
      rcases same_end u v a b huv hbase with hua | hvb
      · rcases same_end d w u v hdw huv with hdu | hwv
        · exact (hda (hdu.trans hua)).elim
        · exact hwv.symm.trans hwb
      · exact hvb
  have orientation : ∀ u v, (∀ i, u ∈ S i ∨ v ∈ S i) → R u v ∨ R v u := by
    intro u v hp
    have huvcol := hbip u v (pair_adj u v hp)
    have hc : (s u = s a ∧ s v = s b) ∨ (s v = s a ∧ s u = s b) := by
      cases hsa : s a <;> cases hsb : s b <;>
        cases hsu : s u <;> cases hsv : s v <;> simp_all
    rcases hc with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inl ⟨hu, hv, hp⟩
    · exact Or.inr ⟨hv, hu, fun i => (hp i).symm⟩
  obtain ⟨c, hcenter⟩ : ∃ c : Fin n, ∀ u v : Fin n,
      (∀ i, u ∈ S i ∨ v ∈ S i) → u = c ∨ v = c := by
    rcases oriented_star with hl | hr
    · refine ⟨a, ?_⟩
      intro u v hp
      rcases orientation u v hp with huv | hvu
      · exact Or.inl (hl u v huv)
      · exact Or.inr (hl v u hvu)
    · refine ⟨b, ?_⟩
      intro u v hp
      rcases orientation u v hp with huv | hvu
      · exact Or.inr (hr u v huv)
      · exact Or.inl (hr v u hvu)
  obtain ⟨d, hdc⟩ : ∃ d : Fin n, ∀ i, d ∈ S i ∨ c ∈ S i := by
    rcases hcenter a b hab with hac | hbc
    · subst a
      exact ⟨b, fun i => (hab i).symm⟩
    · subst b
      exact ⟨a, hab⟩
  obtain ⟨i, hic, hstar⟩ := monochrome_filter_universal G s hbip S t hmono d c
    (hbip d c (pair_adj d c hdc)) hdc (fun x _ hx => hclean x hx)
  refine ⟨c, i, hstar, ?_⟩
  have hcnot : c ∉ S i := by
    intro hc
    exact hic (hmono i c hc).symm
  intro u w hp
  rcases hcenter u w hp with huc | hwc
  · subst u
    exact Or.inl ⟨rfl, (hp i).resolve_left hcnot⟩
  · subst w
    exact Or.inr ⟨rfl, (hp i).resolve_right hcnot⟩

lemma clean_monochrome_product_star_bool {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (hclean : ∀ x : Fin n → Bool, clauseProduct S x = true → graphFun G ∅ x = true)
    (hne : ∃ u v : Fin n, clauseProduct S (pairInput u v) = true) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      (∀ x : Fin n → Bool, (x v && setOr (S i) x) = true → graphFun G ∅ x = true) ∧
      ∀ u w : Fin n, clauseProduct S (pairInput u w) = true →
        (pairInput u w v && setOr (S i) (pairInput u w)) = true := by
  have hp : ∀ u v, clauseProduct S (pairInput u v) = true ↔
      ∀ i, u ∈ S i ∨ v ∈ S i := by
    intro u v
    simp only [clauseProduct, decide_eq_true_eq, pairInput]
    constructor
    · intro h i
      obtain ⟨a, ha, hax⟩ := h i
      rcases hax with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr ha
    · intro h i
      rcases h i with hu | hv
      · exact ⟨u, hu, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
  obtain ⟨u, w, huw⟩ := hne
  obtain ⟨v, i, hstar, hcover⟩ := clean_monochrome_product_star G s hbip h4 S t hmono
    (fun x hx => hclean x (by simpa only [clauseProduct, decide_eq_true_eq] using hx))
    ⟨u, w, (hp u w).mp huw⟩
  refine ⟨v, i, hstar, ?_, ?_⟩
  · intro x hx
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at hx
    obtain ⟨hv, a, ha, hax⟩ := hx
    exact (graph_true G x).mpr ⟨v, a, hstar a ha, hv, hax⟩
  · intro a b hab
    rcases hcover a b ((hp a b).mp hab) with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · simp [pairInput, setOr_pair, hb]
    · simp [pairInput, setOr_pair, ha]

end Geometry


namespace PureTopPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

lemma wire_imp_of_local {n : ℕ} {C D : Circuit} (hC : IsAO2 n C)
    (hlen : D.gates.length = C.gates.length) (x : Fin n → Bool)
    (hlocal : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨
      (gateVal n C j x = true → gateVal n D j x = true)) :
    ∀ w, val C (List.ofFn x) w = true → val D (List.ofFn x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · rw [val_input (n := n) (C := D) (by simp) hinput]
      rwa [val_input (n := n) (C := C) (by simp) hinput] at hw
    by_cases hbound : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hjD : j < D.gates.length := by omega
      rcases hlocal j hj with hgate | hspecial
      · rcases hC.1 _ (gateAt_mem hj) with hand | hor
        · apply (val_and (C := D) (by simp) hjD (by rw [hgate]; exact hand)).mpr
          intro u hu
          rw [hgate] at hu
          obtain ⟨hub, huv⟩ := (val_and (C := C) (by simp) hj hand).mp hw u hu
          exact ⟨hub, ih u hub huv⟩
        · obtain ⟨u, hu, hub, huv⟩ := (val_or (C := C) (by simp) hj hor).mp hw
          apply (val_or (C := D) (by simp) hjD (by rw [hgate]; exact hor)).mpr
          exact ⟨u, by rw [hgate]; exact hu, hub, ih u hub huv⟩
      · exact hspecial hw
    · have hz := val_ge (C := C) (by simp : (List.ofFn x).length = n) (by omega : n + C.gates.length ≤ w)
      rw [hz] at hw
      cases hw

lemma graph_preserved_of_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C D : Circuit} (hC : IsAO2 n C) (hD : IsAO2 n D)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (hF : circuitFun n C = graphFun G ∅)
    (hlocal : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨
      (BelowF G D j ∧ ∀ u v, G.Adj u v →
        gateVal n C j (pairInput u v) = true → gateVal n D j (pairInput u v) = true)) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    by_contra hn
    have hback : ∀ j < D.gates.length, gateAt C j = gateAt D j ∨
        (gateVal n D j x = true → gateVal n C j x = true) := by
      intro j hj
      rcases hlocal j (by omega) with hg | ⟨hc, _⟩
      · exact Or.inl hg.symm
      · exact Or.inr (fun hv => (hn (hc x hv)).elim)
    have hv : val D (List.ofFn x) C.output = true := by
      change val D (List.ofFn x) D.output = true at hx
      rwa [hout] at hx
    have hf := wire_imp_of_local hD hlen.symm x hback C.output hv
    change circuitFun n C x = true at hf
    rw [hF] at hf
    exact hn hf
  · intro hx
    obtain ⟨u, v, huv, hux, hvx⟩ := (Geometry.graph_true G x).mp hx
    have hedge : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graphFun_pair G u v).mpr huv
    have hforward : ∀ j < C.gates.length, gateAt D j = gateAt C j ∨
        (gateVal n C j (pairInput u v) = true → gateVal n D j (pairInput u v) = true) := by
      intro j hj
      rcases hlocal j hj with hg | ⟨_, he⟩
      · exact Or.inl hg
      · exact Or.inr (he u v huv)
    have hv := wire_imp_of_local hC hlen (pairInput u v) hforward C.output hedge
    have hd : circuitFun n D (pairInput u v) = true := by
      change val D (List.ofFn (pairInput u v)) D.output = true
      rwa [hout]
    exact Context.circuit_mono (Context.AO2_monotone2 hD) (Context.pair_le hux hvx) hd

def Pure (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ j < C.gates.length, Relation.ReflTransGen (OrStep n C) w (n + j) →
    (gateAt C j).op = GateOp.or

lemma pure_value_eq {n : ℕ} {C D : Circuit}
    (hlen : D.gates.length = C.gates.length)
    (hOR : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → gateAt D j = gateAt C j)
    (x : Fin n → Bool) : ∀ w, Pure n C w →
      val D (List.ofFn x) w = val C (List.ofFn x) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hpure
    by_cases hin : w < n
    · rw [val_input (n := n) (C := D) (by simp) hin,
        val_input (n := n) (C := C) (by simp) hin]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hjD : j < D.gates.length := by omega
      have hop := hpure j hj Relation.ReflTransGen.refl
      have hgate := hOR j hj hop
      have hchild : ∀ u ∈ (gateAt C j).inputs, u < n + j → Pure n C u := by
        intro u hu hub k hk hr
        exact hpure k hk ((Relation.ReflTransGen.single ⟨j, hj, rfl, hop, hu, hub⟩).trans hr)
      apply Bool.eq_iff_iff.mpr
      rw [val_or (C := D) (by simp) hjD (by rw [hgate]; exact hop),
        val_or (C := C) (by simp) hj hop, hgate]
      constructor <;> rintro ⟨u, hu, hub, huv⟩ <;> refine ⟨u, hu, hub, ?_⟩
      · rwa [← ih u hub (hchild u hu hub)]
      · rwa [ih u hub (hchild u hu hub)]
    · rw [val_ge (n := n) (C := C) (by simp) (by omega),
        val_ge (n := n) (C := D) (by simp) (by omega)]

def rewire (C : Circuit) (q : ℕ → Gate) : Circuit :=
  ⟨List.ofFn (fun i : Fin C.gates.length => q i.val), C.output⟩

lemma rewire_length (C : Circuit) (q : ℕ → Gate) :
    (rewire C q).gates.length = C.gates.length := by simp [rewire]

lemma rewire_gateAt {C : Circuit} (q : ℕ → Gate) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (rewire C q) j = q j := by
  rw [gateAt_eq (by simpa [rewire] using hj)]
  simp [rewire]

lemma rewire_AO {n : ℕ} {C : Circuit} (q : ℕ → Gate)
    (hq : ∀ j < C.gates.length,
      ((q j).op = GateOp.and ∨ (q j).op = GateOp.or) ∧
      (q j).inputs.length = 2 ∧ ∀ u ∈ (q j).inputs, u < n + j) :
    IsAO2 n (rewire C q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hjC : j < C.gates.length := by simpa [rewire] using hj
    simpa [rewire] using (hq j hjC).1
  · intro j hj u hu
    have hjC : j < C.gates.length := by simpa [rewire] using hj
    rw [rewire_gateAt q hjC] at hu
    exact (hq j hjC).2.2 u hu
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hjC : j < C.gates.length := by simpa [rewire] using hj
    simpa [rewire] using (hq j hjC).2.1

lemma rewire_clean_stars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (q : ℕ → Gate)
    (hchanges : ∀ j < C.gates.length, q j = gateAt C j ∨
      ((gateAt C j).op = GateOp.and ∧ ∃ v : Fin n, ∃ w : ℕ,
        q j = ⟨GateOp.and, [v.val, w]⟩ ∧ w < n + j ∧ Pure n C w ∧
        (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true → graphFun G ∅ x = true) ∧
        (∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
          pairInput a b v = true ∧ val C (List.ofFn (pairInput a b)) w = true))) :
    IsAO2 n (rewire C q) ∧ circuitFun n (rewire C q) = graphFun G ∅ := by
  have hOR : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      gateAt (rewire C q) j = gateAt C j := by
    intro j hj hop
    rw [rewire_gateAt q hj]
    rcases hchanges j hj with he | ⟨hand, _⟩
    · exact he
    · rw [hop] at hand
      cases hand
  have hD : IsAO2 n (rewire C q) := rewire_AO q (by
    intro j hj
    rcases hchanges j hj with he | ⟨_, v, w, he, hw, _⟩
    · rw [he]
      exact ⟨hC.1 _ (gateAt_mem hj), hC.2.2 _ (gateAt_mem hj), hC.2.1 j hj⟩
    · rw [he]
      refine ⟨Or.inl rfl, rfl, ?_⟩
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · exact hw)
  refine ⟨hD, graph_preserved_of_local G hC hD (rewire_length C q) rfl hF ?_⟩
  intro j hj
  rcases hchanges j hj with he | ⟨_, v, w, he, hw, hpure, hclean, hedge⟩
  · exact Or.inl ((rewire_gateAt q hj).trans he)
  · right
    have hgate : gateAt (rewire C q) j = ⟨GateOp.and, [v.val, w]⟩ :=
      (rewire_gateAt q hj).trans he
    have hval (x : Fin n → Bool) : gateVal n (rewire C q) j x = true ↔
        x v = true ∧ val C (List.ofFn x) w = true := by
      change val (rewire C q) (List.ofFn x) (n + j) = true ↔ _
      rw [val_and (n := n) (by simp) (by simpa [rewire] using hj) (by rw [hgate]), hgate]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        val_ofFn, pure_value_eq (rewire_length C q) hOR x w hpure]
      constructor
      · rintro ⟨⟨_, hv⟩, ⟨_, hww⟩⟩
        exact ⟨hv, hww⟩
      · rintro ⟨hv, hww⟩
        exact ⟨⟨by omega, hv⟩, hw, hww⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hclean x ((hval x).mp hx).1 ((hval x).mp hx).2
    · intro a b hab hv
      exact (hval _).mpr (hedge a b hab hv)

lemma least_gate_reader {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {k : ℕ} (hk : k < C.gates.length)
    (hout : C.output ≠ n + k) :
    ∃ j < C.gates.length, n + k ∈ (gateAt C j).inputs := by
  by_contra hnot
  have hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs :=
    fun j hj hj' => hnot ⟨j, hj, hj'⟩
  have hAO : IsAO2 n (delDead n k C) := by
    have mapped : ∀ g ∈ (delDead n k C).gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hm := List.mem_of_mem_eraseIdx hg'
      exact ⟨hL.1.1 g' hm, by simp [shiftGate, hL.1.2.2 g' hm]⟩
    exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C hL.1.2.1 hk hno,
      fun g hg => (mapped g hg).2⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    unfold circuitFun Circuit.eval
    rw [delDead_wires_eq n k C _ List.length_ofFn hL.1.2.1 hk hno]
    change (C.wires (List.ofFn x)).getD (unshiftW n k (shiftW n k C.output)) false = _
    rw [unshiftW_shiftW n k C.output hout]
  have hle := hL.2.2 _ hAO (heq.trans hL.2.1)
  have hsize := delDead_size n k C hk
  omega

lemma readerless_rewire_impossible {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {h : ℕ} (hh : h ∈ junk G C)
    (q : ℕ → Gate) (hAO : IsAO2 n (rewire C q))
    (hF : circuitFun n (rewire C q) = graphFun G ∅)
    (havoid : ∀ j < C.gates.length, n + h ∉ (q j).inputs) : False := by
  have hout : C.output ≠ n + h := by
    intro heq
    apply junkNotBelow hh
    intro x hx
    have hf : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
    rw [heq] at hf
    exact hf.symm.trans hx
  have hleast : IsLeastAO G (rewire C q) := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    have hs := hL.2.2 E hE hEF
    simpa [Circuit.size, rewire] using hs
  obtain ⟨j, hj, hread⟩ := least_gate_reader hleast
    (show h < (rewire C q).gates.length by simpa [rewire] using (junkData hh).1) hout
  have hjC : j < C.gates.length := by simpa [rewire] using hj
  rw [rewire_gateAt q hjC] at hread
  exact havoid j hjC hread

lemma star_reader_repair_impossible {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {h : ℕ} (hh : h ∈ junk G C)
    (hreader : ∀ j ∈ readers n C h, (gateAt C j).op = GateOp.and)
    (hrecipe : ∀ j ∈ readers n C h, ∃ v : Fin n, ∃ w : ℕ,
      w < n + j ∧ Pure n C w ∧
      (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
        pairInput a b v = true ∧ val C (List.ofFn (pairInput a b)) w = true)) : False := by
  classical
  choose v w hb hp hc he using hrecipe
  let q : ℕ → Gate := fun j => if hj : j ∈ readers n C h
    then ⟨GateOp.and, [(v j hj).val, w j hj]⟩ else gateAt C j
  have hchanges : ∀ j < C.gates.length, q j = gateAt C j ∨
      ((gateAt C j).op = GateOp.and ∧ ∃ v : Fin n, ∃ w : ℕ,
        q j = ⟨GateOp.and, [v.val, w]⟩ ∧ w < n + j ∧ Pure n C w ∧
        (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true → graphFun G ∅ x = true) ∧
        (∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
          pairInput a b v = true ∧ val C (List.ofFn (pairInput a b)) w = true)) := by
    intro j hj
    by_cases hr : j ∈ readers n C h
    · exact Or.inr ⟨hreader j hr, v j hr, w j hr, by simp [q, hr],
        hb j hr, hp j hr, hc j hr, he j hr⟩
    · exact Or.inl (by simp [q, hr])
  obtain ⟨hAO, hF⟩ := rewire_clean_stars G hL.1 hL.2.1 q hchanges
  apply readerless_rewire_impossible hL hh q hAO hF
  intro j hj hbad
  by_cases hr : j ∈ readers n C h
  · simp only [q, dite_eq_left hr, List.mem_cons, List.not_mem_nil, or_false] at hbad
    rcases hbad with hbad | hbad
    · have := (v j hr).isLt
      omega
    · have hor := hp j hr h (junkData hh).1
        (show Relation.ReflTransGen (OrStep n C) (w j hr) (n + h) by rw [← hbad])
      rw [(junkData hh).2.1] at hor
      cases hor
  · simp only [q, dite_eq_right hr] at hbad
    exact hr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hbad⟩)

end PureTopPatch


namespace NoNonLambda

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

def RawWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ j, OrReaches n C w j → (gateAt C j).op = GateOp.or

def NoJunkOrReaders {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ j ∈ junk G C, ∀ k ∈ readers n C j, (gateAt C k).op ≠ GateOp.or

def RawMonochrome {n : ℕ} (C : Circuit) (s : Fin n → Bool) : Prop :=
  ∀ w < n + C.gates.length, RawWire n C w →
    ∃ t : Bool, ∀ u ∈ orIn n C w, s u = t

lemma junk_no_or_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hN : orN G C \ lam G C = ∅)
    {j k : ℕ} (hj : j ∈ junk G C) (hread : k ∈ readers n C j) :
    (gateAt C k).op ≠ GateOp.or := by
  intro hkop
  obtain ⟨hk, hin⟩ := readData hread
  have hnb : ¬ BelowF G C k := by
    intro hbelow
    apply junkNotBelow hj
    intro x hx
    exact hbelow x ((val_or (n := n) (by simp) hk hkop).mpr
      ⟨n + j, hin, hAO.2.1 k hk _ hin, hx⟩)
  have hkor : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hk (And.intro hkop hnb)
  have hklam : k ∈ lam G C := by
    by_contra hn
    have hmem := Finset.mem_sdiff.mpr ⟨hkor, hn⟩
    rw [hN] at hmem
    exact Finset.notMem_empty _ hmem
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hk hin
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hklam
  have hraw : (orIn n C (opnd C k b)).Nonempty := by
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · exact h0
    · exact h1
  rw [← hb, andRawEmpty (junkData hj).2.1] at hraw
  exact Finset.not_nonempty_empty hraw

lemma junk_orReach_eq_of_no_or_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hR : NoJunkOrReaders G C)
    {j w : ℕ} (hj : j ∈ junk G C) (hr : OrReaches n C w j) : w = n + j := by
  rcases lastOrBefore (orReaches_reach j w hr).1 with he | ⟨k, hk, hop, hin, _, _⟩
  · exact he
  · exact (hR j hj _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩) hop).elim

lemma junk_orReach_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hN : orN G C \ lam G C = ∅)
    {j w : ℕ} (hj : j ∈ junk G C) (hr : OrReaches n C w j) : w = n + j := by
  exact junk_orReach_eq_of_no_or_readers G C
    (fun j hj k hk => junk_no_or_reader G C hAO hN hj hk) hj hr

lemma raw_wire_value {n : ℕ} (C : Circuit) (w : ℕ) (hraw : RawWire n C w)
    (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · intro hv
    obtain ⟨p, hr, hp, hcase⟩ := or_trace (n := n) (C := C)
      (x := List.ofFn x) (by simp) w hv
    rcases hcase with hpn | ⟨j, hj, rfl, hnotor⟩
    · exact ⟨⟨p, hpn⟩, reach_mem_orIn _ hr, (val_ofFn C x ⟨p, hpn⟩).symm.trans hp⟩
    · exact (hnotor (hraw j (reach_orReaches hr j rfl hj))).elim
  · rintro ⟨u, hu, hux⟩
    exact reach_var_val x _ u (mem_orIn_reach u hu) hux

lemma operand_raw_or_and_of_no_or_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hR : NoJunkOrReaders G C) {a : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (b : Fin 2) :
    RawWire n C (opnd C a b) ∨
      ∃ j < a, opnd C a b = n + j ∧ (gateAt C j).op = GateOp.and := by
  have hw := opndBound hAO ha b
  by_cases hinput : opnd C a b < n
  · left
    intro j hr
    exact (Nat.not_le_of_lt hinput hr.1).elim
  · let j := opnd C a b - n
    have hj : j < a := by dsimp [j]; omega
    have hweq : opnd C a b = n + j := by dsimp [j]; omega
    have hjlen : j < C.gates.length := by omega
    rcases hAO.1 _ (gateAt_mem hjlen) with hjand | hjor
    · exact Or.inr ⟨j, hj, hweq, hjand⟩
    · left
      intro k hr
      have hklen := (orReaches_reach k _ hr).2
      rcases hAO.1 _ (gateAt_mem hklen) with hkand | hkor
      · have hkjunk := operandOrAndJunk hAO hT ha hand hr hkand
        have heq := junk_orReach_eq_of_no_or_readers G C hR hkjunk hr
        have hkj : k = j := by omega
        rw [hkj, hjor] at hkand
        cases hkand
      · exact hkor

lemma operand_raw_or_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hN : orN G C \ lam G C = ∅) {a : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (b : Fin 2) :
    RawWire n C (opnd C a b) ∨
      ∃ j < a, opnd C a b = n + j ∧ (gateAt C j).op = GateOp.and := by
  exact operand_raw_or_and_of_no_or_readers G C hAO hT
    (fun j hj k hk => junk_no_or_reader G C hAO hN hj hk) ha hand b

lemma and_raw_factors_of_no_or_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hR : NoJunkOrReaders G C) :
    ∀ a < C.gates.length, (gateAt C a).op = GateOp.and →
      ∃ L : List ℕ, (∀ w ∈ L, w < n + a ∧ RawWire n C w) ∧
        ∀ x : Fin n → Bool, gateVal n C a x = true ↔
          ∀ w ∈ L, val C (List.ofFn x) w = true := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha hand
    have hoper : ∀ b : Fin 2, ∃ L : List ℕ,
        (∀ w ∈ L, w < n + a ∧ RawWire n C w) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C a b) = true ↔
          ∀ w ∈ L, val C (List.ofFn x) w = true := by
      intro b
      rcases operand_raw_or_and_of_no_or_readers G C hAO hT hR ha hand b with hraw | ⟨j, hja, hweq, hjand⟩
      · refine ⟨[opnd C a b], ?_, ?_⟩
        · intro w hw
          have heq : w = opnd C a b := by simpa using hw
          subst w
          exact ⟨opndBound hAO ha b, hraw⟩
        · intro x
          simp
      · obtain ⟨L, hL, hsem⟩ := ih j hja (by omega) hjand
        refine ⟨L, ?_, ?_⟩
        · intro w hw
          obtain ⟨hwb, hwr⟩ := hL w hw
          exact ⟨by omega, hwr⟩
        · intro x
          rw [hweq]
          exact hsem x
    choose L hL hsem using hoper
    refine ⟨L 0 ++ L 1, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with h0 | h1
      · exact hL 0 w h0
      · exact hL 1 w h1
    · intro x
      rw [andValBoth hAO ha hand x, hsem 0 x, hsem 1 x]
      simp only [List.mem_append, or_imp, forall_and]

lemma and_raw_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hN : orN G C \ lam G C = ∅) :
    ∀ a < C.gates.length, (gateAt C a).op = GateOp.and →
      ∃ L : List ℕ, (∀ w ∈ L, w < n + a ∧ RawWire n C w) ∧
        ∀ x : Fin n → Bool, gateVal n C a x = true ↔
          ∀ w ∈ L, val C (List.ofFn x) w = true := by
  exact and_raw_factors_of_no_or_readers G C hAO hT
    (fun j hj k hk => junk_no_or_reader G C hAO hN hj hk)

lemma raw_wire_or_path {n : ℕ} {C : Circuit} {w : ℕ}
    (hraw : RawWire n C w) (k : ℕ) (hk : k < C.gates.length)
    (hr : Relation.ReflTransGen (OrStep n C) w (n + k)) :
    (gateAt C k).op = GateOp.or :=
  hraw k (reach_orReaches hr k rfl hk)

lemma raw_factor_color_of_nonlambda {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (hNM : ∀ k ∈ orN G C \ lam G C, ∀ u ∈ orIn n C (n + k),
      ∀ v ∈ orIn n C (n + k), s u = s v)
    (w : ℕ) (hw : w < n + C.gates.length) :
    ∃ t : Bool, ∀ u ∈ orIn n C w, s u = t := by
  classical
  by_cases hraw : (orIn n C w).Nonempty
  · obtain ⟨u, hu⟩ := hraw
    refine ⟨s u, ?_⟩
    by_cases hwn : w < n
    · intro v hv
      have raw_eq (a : Fin n) (ha : a ∈ orIn n C w) : a.val = w := by
        simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain he | ⟨k, _, hr, _, _⟩ := ha
        · exact he
        · exact (Nat.not_le_of_lt hwn hr.1).elim
      have huv : v = u := Fin.ext ((raw_eq v hv).trans (raw_eq u hu).symm)
      rw [huv]
    · have hweq : w = n + (w - n) := by omega
      have hklen : w - n < C.gates.length := by omega
      have hkop : (gateAt C (w - n)).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hklen) with hand | hor
        · have hz := andRawEmpty (n := n) hand
          rw [← hweq] at hz
          exact (Finset.notMem_empty u (hz ▸ hu)).elim
        · exact hor
      have hnb : ¬ BelowF G C (w - n) := Factor.raw_nonempty_not_below (G := G)
        (hweq ▸ (show (orIn n C w).Nonempty from ⟨u, hu⟩))
      have hkor : w - n ∈ orN G C := by
        simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hklen (And.intro hkop hnb)
      have hmono : ∀ v ∈ orIn n C (n + (w - n)),
          ∀ z ∈ orIn n C (n + (w - n)), s v = s z := by
        by_cases hklam : w - n ∈ lam G C
        · exact Color.lam_monochromatic G C hAO s hs (w - n) hklam
        · exact hNM (w - n) (Finset.mem_sdiff.mpr ⟨hkor, hklam⟩)
      rw [← hweq] at hmono
      exact fun v hv => hmono v hv u hu
  · refine ⟨false, ?_⟩
    intro u hu
    exact (hraw ⟨u, hu⟩).elim

lemma raw_factor_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hN : orN G C \ lam G C = ∅)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (w : ℕ) (hw : w < n + C.gates.length) :
    ∃ t : Bool, ∀ u ∈ orIn n C w, s u = t := by
  apply raw_factor_color_of_nonlambda G C hAO s hs _ w hw
  intro k hk
  rw [hN] at hk
  exact (Finset.notMem_empty k hk).elim

lemma and_raw_clause_factors_of_raw_monochrome {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hR : NoJunkOrReaders G C)
    (s : Fin n → Bool) (hM : RawMonochrome C s)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) :
    ∃ (k : ℕ) (w : Fin k → ℕ) (t : Fin k → Bool),
      (∀ i, w i < n + a ∧ RawWire n C (w i)) ∧
      (∀ i x, wireVal n C (w i) x = setOr (orIn n C (w i)) x) ∧
      (∀ i, ∀ u ∈ orIn n C (w i), s u = t i) ∧
      ∀ x, gateVal n C a x = clauseProduct (fun i => orIn n C (w i)) x := by
  classical
  obtain ⟨L, hL, hsem⟩ := and_raw_factors_of_no_or_readers G C hAO hT hR a ha hand
  let w : Fin L.length → ℕ := fun i => L[i]
  have hw : ∀ i, w i < n + a ∧ RawWire n C (w i) := by
    intro i
    exact hL (w i) (List.getElem_mem i.isLt)
  have hcol : ∀ i, ∃ t : Bool, ∀ u ∈ orIn n C (w i), s u = t := by
    intro i
    exact hM (w i) (by have := (hw i).1; omega) (hw i).2
  choose t ht using hcol
  have hwire : ∀ i x, wireVal n C (w i) x = setOr (orIn n C (w i)) x := by
    intro i x
    apply Bool.eq_iff_iff.mpr
    simpa only [wireVal, val, setOr, decide_eq_true_eq] using raw_wire_value C (w i) (hw i).2 x
  refine ⟨L.length, w, t, hw, hwire, ht, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [hsem x]
  simp only [clauseProduct, decide_eq_true_eq]
  constructor
  · intro hall i
    exact (raw_wire_value C (w i) (hw i).2 x).mp
      (hall (w i) (List.getElem_mem i.isLt))
  · intro hall q hq
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
    have hv := (raw_wire_value C (w ⟨i, hi⟩) (hw ⟨i, hi⟩).2 x).mpr (hall ⟨i, hi⟩)
    change val C (List.ofFn x) L[i] = true at hv
    rw [heq] at hv
    exact hv

lemma and_raw_clause_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hN : orN G C \ lam G C = ∅)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) :
    ∃ (k : ℕ) (w : Fin k → ℕ) (t : Fin k → Bool),
      (∀ i, w i < n + a ∧ RawWire n C (w i)) ∧
      (∀ i x, wireVal n C (w i) x = setOr (orIn n C (w i)) x) ∧
      (∀ i, ∀ u ∈ orIn n C (w i), s u = t i) ∧
      ∀ x, gateVal n C a x = clauseProduct (fun i => orIn n C (w i)) x := by
  exact and_raw_clause_factors_of_raw_monochrome G C hAO hT
    (fun j hj k hk => junk_no_or_reader G C hAO hN hj hk) s
    (fun w hw _ => raw_factor_color G C hAO hN s hs w hw) ha hand

end NoNonLambda

namespace NoNonLambda

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget PEqualNP.Outside.L_meta_5012.Geometry

lemma maximal_junk_readers_top_of_no_or_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hR : NoJunkOrReaders G C)
    {h : ℕ} (hh : h ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ h) :
    ∀ j ∈ readers n C h, j ∈ tops G C := by
  classical
  intro j hread
  obtain ⟨hj, hin⟩ := readData hread
  have hlt : h < j := by have := hAO.2.1 j hj _ hin; omega
  have hand : (gateAt C j).op = GateOp.and :=
    (hAO.1 _ (gateAt_mem hj)).resolve_right (hR h hh j hread)
  have hbelow : BelowF G C j := by
    by_contra hn
    have hdirty : j ∈ junk G C := by
      simp only [BelowF, not_forall] at hn
      obtain ⟨x, hx⟩ := hn
      have hgt : gateVal n C j x = true := by tauto
      have hgf : graphFun G ∅ x = false := by
        cases he : graphFun G ∅ x <;> simp_all
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hand, hj, x, hgt, hgf⟩
    have := hmax j hdirty
    omega
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hj (And.intro hand hbelow)

lemma maximal_junk_readers_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hN : orN G C \ lam G C = ∅)
    {h : ℕ} (hh : h ∈ junk G C) (hmax : ∀ j ∈ junk G C, j ≤ h) :
    ∀ j ∈ readers n C h, j ∈ tops G C := by
  exact maximal_junk_readers_top_of_no_or_readers G C hAO
    (fun j hj k hk => junk_no_or_reader G C hAO hN hj hk) hh hmax

lemma top_available_star_of_raw_monochrome {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hR : NoJunkOrReaders G C)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hM : RawMonochrome C s) {a : ℕ} (ha : a ∈ tops G C) :
    ∃ v : Fin n, ∃ w : ℕ, w < n + a ∧ PureTopPatch.Pure n C w ∧
      (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true → graphFun G ∅ x = true) ∧
      (∀ p q, G.Adj p q → gateVal n C a (pairInput p q) = true →
        pairInput p q v = true ∧ val C (List.ofFn (pairInput p q)) w = true) := by
  obtain ⟨haN, hand, hbelow⟩ := topData ha
  obtain ⟨k, w, t, hraw, heval, hmono, hprod⟩ :=
    and_raw_clause_factors_of_raw_monochrome G C hL.1 hT hR s hM haN hand
  have heval' (i : Fin k) (x : Fin n → Bool) :
      val C (List.ofFn x) (w i) = setOr (orIn n C (w i)) x := heval i x
  obtain ⟨p, q, _, hpq, _⟩ := CriticalEdge.least_gate_critical_edge_of_least G C hL a haN
  obtain ⟨v, i, _, hclean, hcover⟩ := clean_monochrome_product_star_bool G s hs h4
    (fun i => orIn n C (w i)) t hmono
    (fun x hx => hbelow x (by rw [hprod]; exact hx))
    ⟨p, q, by rw [← hprod]; exact hpq⟩
  refine ⟨v, w i, (hraw i).1, ?_, ?_, ?_⟩
  · intro j hj hr
    exact (hraw i).2 j (reach_orReaches hr j rfl hj)
  · intro x hx hw
    apply hclean x
    simp only [Bool.and_eq_true]
    exact ⟨hx, (heval' i x) ▸ hw⟩
  · intro p q _ hpq
    have hpair : pairInput p q v = true ∧ setOr (orIn n C (w i)) (pairInput p q) = true := by
      simpa only [Bool.and_eq_true] using hcover p q (by rw [← hprod]; exact hpq)
    exact ⟨hpair.1, (heval' i _).symm ▸ hpair.2⟩

lemma top_available_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hN : orN G C \ lam G C = ∅)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) {a : ℕ} (ha : a ∈ tops G C) :
    ∃ v : Fin n, ∃ w : ℕ, w < n + a ∧ PureTopPatch.Pure n C w ∧
      (∀ x : Fin n → Bool, x v = true → val C (List.ofFn x) w = true → graphFun G ∅ x = true) ∧
      (∀ p q, G.Adj p q → gateVal n C a (pairInput p q) = true →
        pairInput p q v = true ∧ val C (List.ofFn (pairInput p q)) w = true) := by
  exact top_available_star_of_raw_monochrome G C hL hT
    (fun j hj k hk => junk_no_or_reader G C hL.1 hN hj hk) s hs h4
    (fun w hw _ => raw_factor_color G C hL.1 hN s hs w hw) ha

lemma no_junk_of_no_or_readers_and_raw_monochrome {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hR : NoJunkOrReaders G C) (hM : RawMonochrome C s) : junk G C = ∅ := by
  classical
  by_contra hn
  have hne : (junk G C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hn
  let h := (junk G C).max' hne
  have hh : h ∈ junk G C := Finset.max'_mem _ hne
  have hmax : ∀ j ∈ junk G C, j ≤ h := fun j hj => Finset.le_max' _ j hj
  have htop := maximal_junk_readers_top_of_no_or_readers G C hL.1 hR hh hmax
  apply PureTopPatch.star_reader_repair_impossible hL hh
    (fun j hj => (topData (htop j hj)).2.1)
  intro j hj
  exact top_available_star_of_raw_monochrome G C hL hT hR s hs h4 hM (htop j hj)

lemma no_junk_if_all_nonclean_or_in_lambda {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hN : orN G C \ lam G C = ∅) : junk G C = ∅ := by
  exact no_junk_of_no_or_readers_and_raw_monochrome G C s hs h4 hL hT
    (fun j hj k hk => junk_no_or_reader G C hL.1 hN hj hk)
    (fun w hw _ => raw_factor_color G C hL.1 hN s hs w hw)

lemma junk_requires_nonlambda_or {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : (junk G C).Nonempty) : (orN G C \ lam G C).Nonempty := by
  by_contra hn
  have hz := no_junk_if_all_nonclean_or_in_lambda G C s hs h4 hL hT
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  rw [hz] at hJ
  exact Finset.not_nonempty_empty hJ

end NoNonLambda



namespace OneException

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

lemma junk_or_reader_nonlambda {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {j k : ℕ}
    (hj : j ∈ junk G C) (hread : k ∈ readers n C j)
    (hkop : (gateAt C k).op = GateOp.or) : k ∈ orN G C \ lam G C := by
  classical
  obtain ⟨hk, hin⟩ := readData hread
  have hnb : ¬ BelowF G C k := by
    intro hbelow
    apply junkNotBelow hj
    intro x hx
    exact hbelow x ((val_or (n := n) (by simp) hk hkop).mpr
      ⟨n + j, hin, hAO.2.1 k hk _ hin, hx⟩)
  have hkor : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hk (And.intro hkop hnb)
  refine Finset.mem_sdiff.mpr ⟨hkor, ?_⟩
  intro hklam
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hk hin
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hklam
  have hraw : (orIn n C (opnd C k b)).Nonempty := by
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · exact h0
    · exact h1
  rw [← hb, andRawEmpty (junkData hj).2.1] at hraw
  exact Finset.not_nonempty_empty hraw

lemma sole_junk_or_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {j k m : ℕ}
    (hN : orN G C \ lam G C = {m})
    (hj : j ∈ junk G C) (hread : k ∈ readers n C j)
    (hkop : (gateAt C k).op = GateOp.or) : k = m := by
  have hm := junk_or_reader_nonlambda G C hAO hj hread hkop
  simpa only [hN, Finset.mem_singleton] using hm

lemma junk_orReach_or_after_exception {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {j m w : ℕ}
    (hN : orN G C \ lam G C = {m}) (hj : j ∈ junk G C)
    (hr : OrReaches n C w j) : w = n + j ∨ n + m ≤ w := by
  rcases lastOrBefore (orReaches_reach j w hr).1 with he | ⟨k, hk, hop, hin, _, hreach⟩
  · exact Or.inl he
  · have heq := sole_junk_or_reader G C hAO hN hj
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩) hop
    subst k
    exact Or.inr (orStep_le hreach)

lemma junk_orReach_before_exception {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {j m w : ℕ}
    (hN : orN G C \ lam G C = {m}) (hj : j ∈ junk G C)
    (hw : w < n + m) (hr : OrReaches n C w j) : w = n + j := by
  exact (junk_orReach_or_after_exception G C hAO hN hj hr).resolve_right (by omega)

end OneException

namespace NoNonLambda

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Budget

lemma no_or_readers_of_sole_exception_raw {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) {m : ℕ} (hN : orN G C \ lam G C = {m})
    (hraw : RawWire n C (n + m)) : NoJunkOrReaders G C := by
  intro j hj k hread hop
  have hkm := OneException.sole_junk_or_reader G C hAO hN hj hread hop
  subst k
  obtain ⟨hm, hin⟩ := readData hread
  have hr : OrReaches n C (n + m) j := (orReaches_iff n C m j).mpr
    ⟨hm, Or.inr ⟨hop, n + j, hin, hAO.2.1 m hm _ hin,
      (orReaches_iff n C j j).mpr ⟨(junkData hj).1, Or.inl rfl⟩⟩⟩
  have hjor := hraw j hr
  rw [(junkData hj).2.1] at hjor
  cases hjor

lemma raw_monochrome_of_sole_exception {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {m : ℕ} (hN : orN G C \ lam G C = {m})
    (hmono : ∀ u ∈ orIn n C (n + m), ∀ v ∈ orIn n C (n + m), s u = s v) :
    RawMonochrome C s := by
  intro w hw _
  apply raw_factor_color_of_nonlambda G C hAO s hs _ w hw
  intro k hk
  have hkm : k = m := by simpa only [hN, Finset.mem_singleton] using hk
  subst k
  exact hmono

lemma no_junk_if_sole_exception_raw_monochrome {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    {m : ℕ} (hN : orN G C \ lam G C = {m})
    (hraw : RawWire n C (n + m))
    (hmono : ∀ u ∈ orIn n C (n + m), ∀ v ∈ orIn n C (n + m), s u = s v) :
    junk G C = ∅ := by
  exact no_junk_of_no_or_readers_and_raw_monochrome G C s hs h4 hL hT
    (no_or_readers_of_sole_exception_raw G C hL.1 hN hraw)
    (raw_monochrome_of_sole_exception G C hL.1 s hs hN hmono)

lemma sole_exception_raw_or_color_obstruction {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    {m : ℕ} (hN : orN G C \ lam G C = {m}) (hJ : (junk G C).Nonempty) :
    ¬ RawWire n C (n + m) ∨
      ∃ u ∈ orIn n C (n + m), ∃ v ∈ orIn n C (n + m), s u ≠ s v := by
  classical
  by_cases hraw : RawWire n C (n + m)
  · right
    by_contra hnot
    have hmono : ∀ u ∈ orIn n C (n + m), ∀ v ∈ orIn n C (n + m), s u = s v := by
      intro u hu v hv
      by_contra hne
      exact hnot ⟨u, hu, v, hv, hne⟩
    have hz := no_junk_if_sole_exception_raw_monochrome G C s hs h4 hL hT hN hraw hmono
    rw [hz] at hJ
    exact Finset.not_nonempty_empty hJ
  · exact Or.inl hraw

end NoNonLambda

namespace FlagsSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma z019 {α:Type} [DecidableEq α] {A B:Finset α} (h:A ⊆ B):
  (B \ A).card = B.card - A.card:=by
 rw [Finset.card_sdiff,Finset.inter_eq_left.mpr h]
lemma z144 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (i:ℕ) (hi:i < n):
  wval C x i = x ⟨i,hi⟩:=by
 exact Budget.val_ofFn C x ⟨i, hi⟩
lemma z070 {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
  gateVal n C j x = wval C x (n + j):=rfl
lemma z143 {n:ℕ} (C:Circuit) (x:Fin n→ Bool) {w:ℕ} (hw:n + C.gates.length ≤ w):
  wval C x w = false:=by
 exact Budget.val_ge (n := n) (by simp) hw
def z068 := @Budget.gateAt_eq

def z069 := @Budget.gateAt_mem

lemma z071 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length):
  (gateAt C j).inputs = [opnd C j 0,opnd C j 1]:=by
 exact (CriticalEdge.gate2 hAO hj).2.1
def z105 := @Budget.opndMem

def z104 := @Budget.opndBound

lemma z141 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length):
  wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0),wval C x (opnd C j 1)]:=by
 have hc := CriticalEdge.gate2 hAO hj
 have hv := Budget.val_gate (n := n) (C := C) (x := List.ofFn x) (by simp) hj
 rw [hc.2.1] at hv
 simpa only [List.map_cons, List.map_nil, ite_eq_left hc.2.2.1, ite_eq_left hc.2.2.2.1,
   Budget.val, wval] using hv
lemma z140 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length) (hop:(gateAt C j).op = GateOp.and):
  wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)):=by
 rw [z141 hAO x hj,hop];simp [GateOp.eval]
lemma z142 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j:ℕ} (hj:j < C.gates.length) (hop:(gateAt C j).op = GateOp.or):
  wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)):=by
 rw [z141 hAO x hj,hop];simp [GateOp.eval]
lemma z138 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C):
  ∀ w < n + C.gates.length,wval C (fun _:Fin n=>true) w = true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw
  by_cases hwn:w < n
  ·rw [z144 C _ w hwn]
  ·have hj:w - n < C.gates.length:=by omega
   have q0f:w = n + (w - n):=by omega
   rw [q0f]
   have hop:=hAO.1 _ (z069 hj)
   have h0:opnd C (w - n) 0 < w:=by have:=z104 hAO hj 0;omega
   have h1:opnd C (w - n) 1 < w:=by have:=z104 hAO hj 1;omega
   have hv0:=ih _ h0 (by omega)
   have hv1:=ih _ h1 (by omega)
   rcases hop with q17 | hor
   ·rw [z140 hAO _ hj q17,hv0,hv1];rfl
   ·rw [z142 hAO _ hj hor,hv0,hv1];rfl
lemma z080 {n:ℕ} {C:Circuit} {i j:ℕ} (h:InCone n C i j):j < C.gates.length:=by
 exact ((Budget.inCone_iff n C i j).mp h).1
lemma z078 {n:ℕ} {C:Circuit} {i j:ℕ} (hj:j < C.gates.length):
  InCone n C i j↔ 
   ∃ w ∈ (gateAt C j).inputs,n ≤ w∧ w < n + j∧ (i = w - n∨ InCone n C i (w - n)):=by
 constructor
 · intro h
   obtain ⟨_, k, hkj, hkin, hcase⟩ := (Budget.inCone_iff n C i j).mp h
   refine ⟨n + k, hkin, by omega, by omega, ?_⟩
   simpa only [Nat.add_sub_cancel_left] using hcase
 · rintro ⟨w, hw, hnw, hwj, hcase⟩
   apply (Budget.inCone_iff n C i j).mpr
   refine ⟨hj, w - n, by omega, ?_, hcase⟩
   have heq : n + (w - n) = w := by omega
   rw [heq]
   exact hw
lemma z079 {n:ℕ} {C:Circuit} {i j:ℕ}:InCone n C i j→ i < j:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
  intro h
  have hj:=z080 h
  rw [z078 hj] at h
  rcases h with ⟨w,_,hnw,qfz,rfl | q0c⟩
  ·omega
  ·have:=ih (w - n) (by omega) q0c;omega
lemma z111 {n:ℕ} {C:Circuit} {j g:ℕ} (hj:j < C.gates.length):
  OrReaches n C (n + j) g↔ 
   g = j∨ ((gateAt C j).op = GateOp.or∧ 
    ∃ w ∈ (gateAt C j).inputs,n ≤ w∧ w < n + j∧ OrReaches n C w g):=by
 rw [Budget.orReaches_iff]
 constructor
 · intro h
   rcases h.2 with he | ⟨hop, w, hw, hlt, hr⟩
   · exact Or.inl he
   · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr⟩
 · intro h
   refine ⟨hj, ?_⟩
   rcases h with he | ⟨hop, w, hw, _, hlt, hr⟩
   · exact Or.inl he
   · exact Or.inr ⟨hop, w, hw, hlt, hr⟩
lemma z112 {n:ℕ} {C:Circuit} {w g:ℕ} (hw:w < n):¬ OrReaches n C w g:=
 fun h=>by have:=h.1;omega
lemma z113 {n:ℕ} {C:Circuit} {w g:ℕ} (h:OrReaches n C w g):g ≤ w - n:=by
 have hle := Budget.orStep_le (Budget.orReaches_reach g w h).1
 omega
lemma z115 {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
  OrReaches n C (n + j) j:=
 (z111 hj).mpr (Or.inl rfl)
lemma z116 {n:ℕ} {C:Circuit} {w j g:ℕ}
  (h1:OrReaches n C w j) (h2:OrReaches n C (n + j) g):OrReaches n C w g:=by
 exact Budget.reach_orReaches
   ((Budget.orReaches_reach j w h1).1.trans (Budget.orReaches_reach g (n + j) h2).1)
   g rfl (Budget.orReaches_reach g (n + j) h2).2
lemma z117 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {w g:ℕ} (h:OrReaches n C w g) (hg:gateVal n C g x = true):wval C x w = true:=by
 exact Budget.orStep_up (n := n) (by simp) (Budget.orReaches_reach g w h).1 hg
lemma z095 {n:ℕ} (C:Circuit) (u v:Fin n):
  u ∈ orIn n C v.val↔ u = v:=by
 unfold orIn
 simp only [Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 ·rintro (heq | ⟨k,_,q0q,_,_⟩)
  ·exact Fin.ext heq
  ·exact absurd q0q (z112 v.isLt)
 ·rintro rfl;exact Or.inl rfl
lemma z107 {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length)
  (q17:(gateAt C j).op = GateOp.and):orIn n C (n + j) = ∅:=by
 exact Budget.andRawEmpty q17
lemma z108 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j:ℕ} (hj:j < C.gates.length)
  (hor:(gateAt C j).op = GateOp.or):
  orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1):=by
 ext u
 simp only [Finset.mem_union,orIn,Finset.mem_filter,Finset.mem_univ,true_and]
 constructor
 ·rintro (hu | ⟨k,hk,q0q,q3d,huk⟩)
  ·omega
  ·rw [z111 hj] at q0q
   rcases q0q with rfl | ⟨_,w,hw,hnw,qfz,hwk⟩
   ·rw [z071 hAO hj] at huk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at huk
    rcases huk with h0 | h1
    ·exact Or.inl (Or.inl h0)
    ·exact Or.inr (Or.inl h1)
   ·rw [z071 hAO hj] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    ·exact Or.inl (Or.inr ⟨k,hk,hwk,q3d,huk⟩)
    ·exact Or.inr (Or.inr ⟨k,hk,hwk,q3d,huk⟩)
 ·rintro ((h0 | ⟨k,hk,hwk,q3d,huk⟩) | (h1 | ⟨k,hk,hwk,q3d,huk⟩))
  ·right
   refine ⟨j,hj,z115 hj,hor,?_⟩
   rw [z071 hAO hj,h0];simp
  ·right
   refine ⟨k,hk,(z111 hj).mpr (Or.inr ⟨hor,opnd C j 0,z105 hAO hj 0,hwk.1,
    z104 hAO hj 0,hwk⟩),q3d,huk⟩
  ·right
   refine ⟨j,hj,z115 hj,hor,?_⟩
   rw [z071 hAO hj,h1];simp
  ·right
   refine ⟨k,hk,(z111 hj).mpr (Or.inr ⟨hor,opnd C j 1,z105 hAO hj 1,hwk.1,
    z104 hAO hj 1,hwk⟩),q3d,huk⟩
lemma z110 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {w:ℕ} {u:Fin n} (hu:u ∈ orIn n C w) (hx:x u = true):wval C x w = true:=by
 exact Budget.reach_var_val x w u (Budget.mem_orIn_reach u hu) hx
lemma z109 {n:ℕ} {C:Circuit} {w k:ℕ} (h:OrReaches n C w k):
  orIn n C (n + k) ⊆ orIn n C w:=by
 intro u hu
 unfold orIn at hu ⊢
 simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
 rcases hu with hu | ⟨m,hm,hkm,qaw,hum⟩
 ·omega
 ·exact Or.inr ⟨m,hm,z116 h hkm,qaw,hum⟩
def z036 (n j r w:ℕ):ℕ:=
 if w = n + j then r else if n + j < w then w - 1 else w
def z026 (n:ℕ) (C:Circuit) (j r:ℕ):Circuit:=
 {gates:=(C.gates.eraseIdx j).map (fun g=>{ g with inputs:=g.inputs.map (z036 n j r)})
  output:=z036 n j r C.output}
lemma z030 (n:ℕ) (C:Circuit) {j:ℕ} (hj:j < C.gates.length) (r:ℕ):
  (z026 n C j r).gates.length = C.gates.length - 1:=by
 simp [z026,List.length_eraseIdx,hj]
lemma z028 {n:ℕ} {C:Circuit} {j r i:ℕ}
  (hj:j < C.gates.length) (hi:i < j):
  gateAt (z026 n C j r) i =
   {(gateAt C i) with inputs:=(gateAt C i).inputs.map (z036 n j r)}:=by
 have hi':i < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
 rw [z068 hi',z068 (by omega)]
 simp only [z026,List.getElem_map]
 rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx,if_pos hj];omega) hi]
lemma z027 {n:ℕ} {C:Circuit} {j r i:ℕ}
  (hj:j < C.gates.length) (hji:j ≤ i) (hi:i < C.gates.length - 1):
  gateAt (z026 n C j r) i =
   {(gateAt C (i + 1)) with inputs:=(gateAt C (i + 1)).inputs.map (z036 n j r)}:=by
 have hi':i < (z026 n C j r).gates.length:=by rw [z030 n C hj r];omega
 rw [z068 hi',z068 (by omega)]
 simp only [z026,List.getElem_map]
 rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx,if_pos hj];omega) hji]
lemma z029 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r:ℕ}
  (hj:j < C.gates.length) (hr:r < n + j):IsAO2 n (z026 n C j r):=by
 refine ⟨?_,?_,?_⟩
 ·intro g hg
  simp only [z026,List.mem_map] at hg
  rcases hg with ⟨g0,hg0,rfl⟩
  exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
 ·intro i hi w hw
  rw [z030 n C hj r] at hi
  by_cases hij:i < j
  ·rw [z028 hj hij] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u,hu,rfl⟩
   have qjq:u < n + i:=hAO.2.1 i (by omega) u hu
   unfold z036
   rw [if_neg (by omega),if_neg (by omega)]
   exact qjq
  ·rw [z027 hj (by omega) hi] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u,hu,rfl⟩
   have qjq:u < n + (i + 1):=hAO.2.1 (i + 1) (by omega) u hu
   unfold z036
   split_ifs <;> omega
 ·intro g hg
  simp only [z026,List.mem_map] at hg
  rcases hg with ⟨g0,hg0,rfl⟩
  simp only [List.length_map]
  exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)
lemma z032 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r i:ℕ}
  (hj:j < C.gates.length) (hi:i < j) (b:Fin 2):
  opnd (z026 n C j r) i b = z036 n j r (opnd C i b):=by
 unfold opnd
 rw [z028 hj hi,z071 hAO (by omega)]
 fin_cases b <;> rfl
lemma z031 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) {j r i:ℕ}
  (hj:j < C.gates.length) (hji:j ≤ i) (hi:i < C.gates.length - 1) (b:Fin 2):
  opnd (z026 n C j r) i b = z036 n j r (opnd C (i + 1) b):=by
 unfold opnd
 rw [z027 hj hji hi,z071 hAO (by omega)]
 fin_cases b <;> rfl
lemma mapped_gate_eval {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r k:ℕ} (hj:j < C.gates.length) (hr:r < n + j)
  (hk:k < C.gates.length) (hne:k ≠ j):
  wval (z026 n C j r) x (z036 n j r (n + k)) = (gateAt C k).op.eval
   [wval (z026 n C j r) x (z036 n j r (opnd C k 0)),
    wval (z026 n C j r) x (z036 n j r (opnd C k 1))]:=by
 have hD:=z029 hAO hj hr
 by_cases hkj:k < j
 · have he:z036 n j r (n + k) = n + k:=by
    unfold z036
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]
   rw [he,z141 hD x (by rw [z030 n C hj r];omega),
    z032 hAO hj hkj 0,z032 hAO hj hkj 1,z028 hj hkj]
 · have hkm:k - 1 < C.gates.length - 1:=by omega
   have hjk:j ≤ k - 1:=by omega
   have he:z036 n j r (n + k) = n + (k - 1):=by
    unfold z036
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    omega
   rw [he,z141 hD x (by rw [z030 n C hj r];omega),
    z031 hAO hj hjk hkm 0,z031 hAO hj hjk hkm 1,z027 hj hjk hkm,
    show k - 1 + 1 = k by omega]

lemma z033 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n + j)
  (heq:wval C x r = wval C x (n + j)):
  ∀ w < n + C.gates.length,wval (z026 n C j r) x (z036 n j r w) = wval C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw
  by_cases hwn:w < n
  · have he:z036 n j r w = w:=by
     unfold z036
     rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    rw [he,z144 _ x w hwn,z144 _ x w hwn]
  · by_cases hwj:w = n + j
    · subst w
      have he:z036 n j r r = r:=by
       unfold z036
       rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      have hv:=(ih r hr (by omega)).trans heq
      rw [he] at hv
      simpa [z036] using hv
    · have hk:w - n < C.gates.length:=by omega
      have he:w = n + (w - n):=by omega
      have h0:opnd C (w - n) 0 < w:=by have:=z104 hAO hk 0;omega
      have h1:opnd C (w - n) 1 < w:=by have:=z104 hAO hk 1;omega
      rw [he,mapped_gate_eval hAO x hj hr hk (by omega),z141 hAO x hk]
      rw [ih _ h0 (by omega),ih _ h1 (by omega)]

lemma z034 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n + j)
  (hle:wval C x (n + j) = true→ wval C x r = true):
  ∀ w < n + C.gates.length,wval C x w = true→ wval (z026 n C j r) x (z036 n j r w) = true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw hv
  by_cases hwn:w < n
  · have he:z036 n j r w = w:=by
     unfold z036
     rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    rw [he,z144 _ x w hwn]
    rwa [z144 _ x w hwn] at hv
  · by_cases hwj:w = n + j
    · subst w
      have he:z036 n j r r = r:=by
       unfold z036
       rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      have hv':=ih r hr (by omega) (hle hv)
      rw [he] at hv'
      simpa [z036] using hv'
    · have hk:w - n < C.gates.length:=by omega
      have he:w = n + (w - n):=by omega
      have h0:opnd C (w - n) 0 < w:=by have:=z104 hAO hk 0;omega
      have h1:opnd C (w - n) 1 < w:=by have:=z104 hAO hk 1;omega
      have h0':=ih _ h0 (by omega)
      have h1':=ih _ h1 (by omega)
      rw [he,z141 hAO x hk] at hv
      rw [he,mapped_gate_eval hAO x hj hr hk (by omega)]
      rcases hAO.1 _ (z069 hk) with ha | ho
      · have hv' : wval C x (opnd C (w - n) 0) = true ∧
          wval C x (opnd C (w - n) 1) = true:=by simpa [ha,GateOp.eval] using hv
        simpa [ha,GateOp.eval] using And.intro (h0' hv'.1) (h1' hv'.2)
      · have hv' : wval C x (opnd C (w - n) 0) = true ∨
          wval C x (opnd C (w - n) 1) = true:=by simpa [ho,GateOp.eval] using hv
        simpa [ho,GateOp.eval] using hv'.imp h0' h1'

lemma z035 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (x:Fin n→ Bool)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n + j):
  ∀ w < n + C.gates.length,w ≠ n + j→ (n ≤ w→ ¬ InCone n C j (w - n))→
   wval (z026 n C j r) x (z036 n j r w) = wval C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw hwj hnc
  by_cases hwn:w < n
  · have he:z036 n j r w = w:=by
     unfold z036
     rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    rw [he,z144 _ x w hwn,z144 _ x w hwn]
  · have hk:w - n < C.gates.length:=by omega
    have he:w = n + (w - n):=by omega
    have hnc':¬ InCone n C j (w - n):=hnc (by omega)
    have child:∀ b:Fin 2,opnd C (w - n) b ≠ n + j ∧
      (n ≤ opnd C (w - n) b→ ¬ InCone n C j (opnd C (w - n) b - n)):=by
     intro b
     have hmem:=z105 hAO hk b
     have hlt:=z104 hAO hk b
     constructor
     · intro heq
       apply hnc'
       rw [z078 hk]
       exact ⟨opnd C (w - n) b,hmem,by omega,hlt,Or.inl (by omega)⟩
     · intro hnu hin
       apply hnc'
       rw [z078 hk]
       exact ⟨opnd C (w - n) b,hmem,hnu,hlt,Or.inr hin⟩
    have h0:opnd C (w - n) 0 < w:=by have:=z104 hAO hk 0;omega
    have h1:opnd C (w - n) 1 < w:=by have:=z104 hAO hk 1;omega
    rw [he,mapped_gate_eval hAO x hj hr hk (by omega),z141 hAO x hk]
    rw [ih _ h0 (by omega) (child 0).1 (child 0).2,
     ih _ h1 (by omega) (child 1).1 (child 1).2]

def z073 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] := CriticalEdge.gf G

lemma z075 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (v:Fin n):
  graphFun G ∅ (fun w=>decide (w = v)) = false:=by
 rw [Bool.eq_false_iff,ne_eq,z073]
 rintro ⟨a,b,hab,ha,hb⟩
 simp only [decide_eq_true_eq] at ha hb
 subst ha;subst hb
 exact G.loopless.irrefl _ hab
def z074 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] := Budget.graphFun_pair G

lemma z120 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  n ≤ C.output∧ C.output < n + C.gates.length:=by
 obtain ⟨u,v,huv⟩:=hne
 have qmd:∀ x,wval C x C.output = graphFun G ∅ x:=fun x=>congrFun hL.2.1 x
 constructor
 ·by_contra hlt
  push Not at hlt
  have h1:=qmd (fun w=>decide (w = ⟨C.output,hlt⟩))
  rw [z144 C _ C.output hlt,z075] at h1
  simp at h1
 ·by_contra hge
  push Not at hge
  have h1:=qmd (pairInput u v)
  rw [z143 C _ hge,(z074 u v).mpr huv] at h1
  cases h1
lemma z088 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  ∀ j < C.gates.length,InOutputCone n C j:=by
 have ⟨u,_,_⟩:=hne
 have hn0:0 < n:=Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
 have q9b:=z120 hL hne
 intro j hj
 refine ⟨hj,?_⟩
 by_contra q8o
 push Not at q8o
 have hr:0 < n + j:=by omega
 let C':=z026 n C j 0
 have q4x:=z029 hL.1 hj hr
 have q6z:circuitFun n C' = graphFun G ∅:=by
  funext x
  change wval C' x C'.output = graphFun G ∅ x
  rw [← congrFun hL.2.1 x]
  exact z035 hL.1 x hj hr C.output q9b.2 q8o.1 (fun _=>q8o.2 q9b.1)
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C hj 0] at hsz
 omega
lemma z090 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {j r:ℕ} (hj:j < C.gates.length) (hr:r < n + j):
  ¬ ∀ x:Fin n→ Bool,wval C x r = wval C x (n + j):=by
 have q9b:=z120 hL hne
 intro heq
 let C':=z026 n C j r
 have q4x:=z029 hL.1 hj hr
 have q6z:circuitFun n C' = graphFun G ∅:=by
  funext x
  change wval C' x C'.output = graphFun G ∅ x
  rw [← congrFun hL.2.1 x]
  exact z033 hL.1 x hj hr (heq x) C.output q9b.2
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C hj r] at hsz
 omega
lemma z089 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a < C.gates.length) (q17:(gateAt C a).op = GateOp.and) (b:Fin 2):
  ¬ ∀ x:Fin n→ Bool,wval C x (opnd C a b) = true→ graphFun G ∅ x = true:=by
 have q9b:=z120 hL hne
 intro q9c
 set r:=opnd C a b
 have hr:r < n + a:=z104 hL.1 ha b
 let C':=z026 n C a r
 have q4x:=z029 hL.1 ha hr
 have q6z:circuitFun n C' = graphFun G ∅:=by
  funext x
  change wval C' x C'.output = graphFun G ∅ x
  cases hFx:graphFun G ∅ x
  ·have hrx:wval C x r = false:=by
    cases h:wval C x r
    ·rfl
    ·have:=q9c x h;rw [hFx] at this;cases this
   have hax:wval C x (n + a) = false:=by
    rw [z140 hL.1 x ha q17]
    fin_cases b
    ·change wval C x (opnd C a 0) = false at hrx;rw [hrx];rfl
    ·change wval C x (opnd C a 1) = false at hrx;rw [hrx,Bool.and_false]
   have hcx:wval C x C.output = false:=by
    change circuitFun n C x = false;rw [congrFun hL.2.1 x];exact hFx
   change wval (z026 n C a r) x (z036 n a r C.output) = false
   rw [z033 hL.1 x ha hr (by rw [hrx,hax]) C.output q9b.2,hcx]
  ·have hcx:wval C x C.output = true:=by
    change circuitFun n C x = true;rw [congrFun hL.2.1 x];exact hFx
   change wval (z026 n C a r) x (z036 n a r C.output) = true
   apply z034 hL.1 x ha hr _ C.output q9b.2 hcx
   intro hax
   rw [z140 hL.1 x ha q17,Bool.and_eq_true] at hax
   fin_cases b
   ·exact hax.1
   ·exact hax.2
 have hsz:=hL.2.2 C' q4x q6z
 simp only [Circuit.size,C',z030 n C ha r] at hsz
 omega
lemma z081 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {w:ℕ} (hw:w < n):
  ¬ ∀ x:Fin n→ Bool,wval C x w = true→ graphFun G ∅ x = true:=by
 intro h
 have:=h (fun i=>decide (i = ⟨w,hw⟩)) (by rw [z144 C _ w hw];simp)
 rw [z075] at this
 cases this
lemma z091 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {h:ℕ} (hh:h < C.gates.length) (hor:(gateAt C h).op = GateOp.or)
  (hnb:¬ BelowF G C h) (b:Fin 2):
  ¬ ∀ x:Fin n→ Bool,wval C x (opnd C h b) = true→ graphFun G ∅ x = true:=by
 intro q9c
 apply q01
 refine ⟨h,hh,b,z088 hL hne h hh,hor,hnb,q9c,?_⟩
 refine ⟨fun _=>true,z138 hL.1 (opnd C h b) (by have:=z104 hL.1 hh b;omega)⟩
lemma z119 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) {h:ℕ} (hh:h < C.gates.length)
  (hor:(gateAt C h).op = GateOp.or) (hb:BelowF G C h) (b:Fin 2):
  n ≤ opnd C h b∧ opnd C h b - n < C.gates.length∧ BelowF G C (opnd C h b - n):=by
 have hwb:∀ x,wval C x (opnd C h b) = true→ graphFun G ∅ x = true:=by
  intro x hwx
  apply hb x
  rw [z070,z142 hL.1 x hh hor,Bool.or_eq_true]
  fin_cases b
  ·exact Or.inl hwx
  ·exact Or.inr hwx
 have hge:n ≤ opnd C h b:=by
  by_contra hlt;push Not at hlt;exact z081 hlt hwb
 have hlt:opnd C h b < n + h:=z104 hL.1 hh b
 refine ⟨hge,by omega,?_⟩
 intro x hx
 apply hwb x
 rw [z070] at hx
 rwa [show n + (opnd C h b - n) = opnd C h b by omega] at hx
lemma z098 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k ∈ tops G C↔ k < C.gates.length∧ (gateAt C k).op = GateOp.and∧ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold tops gatesWhere;rw [Finset.mem_filter,Finset.mem_range]
lemma z097 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k ∈ orT G C↔ k < C.gates.length∧ (gateAt C k).op = GateOp.or∧ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold orT gatesWhere;rw [Finset.mem_filter,Finset.mem_range]
lemma z096 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k ∈ orN G C↔ k < C.gates.length∧ (gateAt C k).op = GateOp.or∧ ¬ BelowF G C k:=by
 letI:DecidableEq GateOp:=gateOpDecEq
 unfold orN gatesWhere;rw [Finset.mem_filter,Finset.mem_range]
lemma z094 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit} {k:ℕ}:
  k ∈ junk G C↔ k < C.gates.length∧ (gateAt C k).op = GateOp.and∧ ¬ BelowF G C k:=by
 unfold junk gatesWhere
 rw [Finset.mem_filter,Finset.mem_range]
 unfold IsDirtyAnd IsDirty BelowF
 constructor
 ·rintro ⟨hk,q17,_,x,hgx,hfx⟩
  refine ⟨hk,q17,fun hb=>?_⟩
  have:=hb x hgx;rw [hfx] at this;cases this
 ·rintro ⟨hk,q17,hnb⟩
  push Not at hnb
  rcases hnb with ⟨x,hgx,hfx⟩
  refine ⟨hk,q17,hk,x,hgx,?_⟩
  cases h:graphFun G ∅ x
  ·rfl
  ·exact absurd h hfx
lemma z013 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {k m:ℕ} (hk:k < C.gates.length) (hbk:BelowF G C k)
  (hm:m < C.gates.length) (q60:n + k ∈ (gateAt C m).inputs):
  m ∈ orT G C:=by
 have hwb:∀ x,wval C x (n + k) = true→ graphFun G ∅ x = true:=hbk
 rw [z071 hL.1 hm] at q60
 simp only [List.mem_cons,List.not_mem_nil,or_false] at q60
 obtain ⟨b,hb⟩:∃ b:Fin 2,opnd C m b = n + k:=by
  rcases q60 with h0 | h1
  ·exact ⟨0,h0.symm⟩
  ·exact ⟨1,h1.symm⟩
 rcases hL.1.1 _ (z069 hm) with q17 | hor
 ·exfalso
  exact z089 hL hne hm q17 b (by rw [hb];exact hwb)
 ·rw [z097]
  refine ⟨hm,hor,?_⟩
  by_contra hnb
  exact z091 hL q01 hne hm hor hnb b (by rw [hb];exact hwb)
lemma z121 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v):
  C.output - n ∈ tops G C ∪ orT G C:=by
 have q9b:=z120 hL hne
 have hk:C.output - n < C.gates.length:=by omega
 have hb:BelowF G C (C.output - n):=by
  intro x hx
  rw [z070,show n + (C.output - n) = C.output by omega] at hx
  rw [← congrFun hL.2.1 x];exact hx
 rw [Finset.mem_union,z098,z097]
 rcases hL.1.1 _ (z069 hk) with q17 | hor
 ·exact Or.inl ⟨hk,q17,hb⟩
 ·exact Or.inr ⟨hk,hor,hb⟩
lemma z038 {n:ℕ} {C:Circuit} {k j:ℕ} (h:InCone n C k j):
  ∃ m < C.gates.length,n + k ∈ (gateAt C m).inputs:=by
 induction j using Nat.strong_induction_on with
 | ind j ih=>
  have hj:=z080 h
  rw [z078 hj] at h
  rcases h with ⟨w,hw,hnw,qfz,rfl | q0c⟩
  ·exact ⟨j,hj,by rwa [show n + (w - n) = w by omega]⟩
  ·exact ih (w - n) (by omega) q0c
lemma z133 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v):
  (tops G C).card ≤ (orT G C).card + 1:=by
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 have q4y:Disjoint (tops G C) (orT G C):=by
  rw [Finset.disjoint_left]
  intro k hk1 hk2
  rw [z098] at hk1;rw [z097] at hk2
  rw [hk1.2.1] at hk2;cases hk2.2.1
 let S:=((tops G C ∪ orT G C).erase (C.output - n)).image (fun k=>n + k)
 let T:=(orT G C ×ˢ (Finset.univ:Finset (Fin 2))).image (fun p=>opnd C p.1 p.2)
 have q0c:S ⊆ T:=by
  intro w hw
  simp only [S,Finset.mem_image,Finset.mem_erase,Finset.mem_union] at hw
  rcases hw with ⟨k,⟨qd0,q3w⟩,rfl⟩
  have q0d:k < C.gates.length:=by
   rcases q3w with h | h
   ·exact (z098.mp h).1
   ·exact (z097.mp h).1
  have qjr:BelowF G C k:=by
   rcases q3w with h | h
   ·exact (z098.mp h).2.2
   ·exact (z097.mp h).2.2
  have qjs:=z088 hL hne k q0d
  have hin:InCone n C k (C.output - n):=by
   rcases qjs.2 with heq | ⟨_,hin⟩
   ·exfalso;apply qd0;omega
   ·exact hin
  obtain ⟨m,hm,q60⟩:=z038 hin
  have qc4:=z013 hL q01 hne q0d qjr hm q60
  rw [z071 hL.1 hm] at q60
  simp only [List.mem_cons,List.not_mem_nil,or_false] at q60
  simp only [T,Finset.mem_image,Finset.mem_product,Finset.mem_univ,and_true]
  rcases q60 with h0 | h1
  ·exact ⟨(m,0),qc4,h0.symm⟩
  ·exact ⟨(m,1),qc4,h1.symm⟩
 have qga:S.card = (tops G C).card + (orT G C).card - 1:=by
  rw [Finset.card_image_of_injective _ (fun a b h=>by omega),
   Finset.card_erase_of_mem q32,Finset.card_union_of_disjoint q4y]
 have qme:T.card ≤ 2 * (orT G C).card:=by
  calc T.card ≤ (orT G C ×ˢ (Finset.univ:Finset (Fin 2))).card:=Finset.card_image_le
   _ = (orT G C).card * 2:=by simp
   _ = 2 * (orT G C).card:=Nat.mul_comm _ _
 have hle:=Finset.card_le_card q0c
 rw [qga] at hle
 omega
lemma z024 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C):
  C.size = (tops G C).card + (orT G C).card + (junk G C).card + (orN G C).card:=by
 have hU:Finset.range C.gates.length = tops G C ∪ orT G C ∪ junk G C ∪ orN G C:=by
  ext k
  simp only [Finset.mem_union,Finset.mem_range,z098,z097,z094,z096]
  constructor
  ·intro hk
   rcases hL.1.1 _ (z069 hk) with q17 | hor
   ·by_cases hb:BelowF G C k
    ·exact Or.inl (Or.inl (Or.inl ⟨hk,q17,hb⟩))
    ·exact Or.inl (Or.inr ⟨hk,q17,hb⟩)
   ·by_cases hb:BelowF G C k
    ·exact Or.inl (Or.inl (Or.inr ⟨hk,hor,hb⟩))
    ·exact Or.inr ⟨hk,hor,hb⟩
  ·rintro (((⟨hk,_⟩ | ⟨hk,_⟩) | ⟨hk,_⟩) | ⟨hk,_⟩) <;> exact hk
 have hd1:Disjoint (tops G C) (orT G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z098] at h1;rw [z097] at h2;rw [h1.2.1] at h2;cases h2.2.1
 have hd2:Disjoint (tops G C ∪ orT G C) (junk G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z094] at h2;simp only [Finset.mem_union,z098,z097] at h1
  rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
 have hd3:Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C):=by
  rw [Finset.disjoint_left];intro k h1 h2
  rw [z096] at h2;simp only [Finset.mem_union,z098,z097,z094] at h1
  rcases h1 with (h1 | h1) | h1
  ·exact h2.2.2 h1.2.2
  ·exact h2.2.2 h1.2.2
  ·rw [h1.2.1] at h2;cases h2.2.1
 change C.gates.length = _
 rw [← Finset.card_range C.gates.length,hU,
  Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint hd2,
  Finset.card_union_of_disjoint hd1]
lemma z023 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v) (x:Fin n→ Bool):
  circuitFun n C x = true↔ ∃ a ∈ tops G C,gateVal n C a x = true:=by
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 constructor
 ·intro hcx
  have qnt:∀ k,k ∈ tops G C ∪ orT G C→ gateVal n C k x = true→ 
    ∃ a ∈ tops G C,gateVal n C a x = true:=by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih=>
    intro hk hvk
    rw [Finset.mem_union] at hk
    rcases hk with qnu | q93
    ·exact ⟨k,qnu,hvk⟩
    ·rw [z097] at q93
     rw [z070,z142 hL.1 x q93.1 q93.2.1,Bool.or_eq_true] at hvk
     rcases hvk with h0 | h1
     ·obtain ⟨hge,hlt,hbf⟩:=z119 hL q93.1 q93.2.1 q93.2.2 0
      have qd1:opnd C k 0 - n < k:=by have:=z104 hL.1 q93.1 0;omega
      have q23:opnd C k 0 - n ∈ tops G C ∪ orT G C:=by
       rw [Finset.mem_union,z098,z097]
       rcases hL.1.1 _ (z069 hlt) with q17 | hor
       ·exact Or.inl ⟨hlt,q17,hbf⟩
       ·exact Or.inr ⟨hlt,hor,hbf⟩
      exact ih _ qd1 q23 (by rw [z070,show n + (opnd C k 0 - n) = opnd C k 0 by omega];exact h0)
     ·obtain ⟨hge,hlt,hbf⟩:=z119 hL q93.1 q93.2.1 q93.2.2 1
      have qd1:opnd C k 1 - n < k:=by have:=z104 hL.1 q93.1 1;omega
      have q23:opnd C k 1 - n ∈ tops G C ∪ orT G C:=by
       rw [Finset.mem_union,z098,z097]
       rcases hL.1.1 _ (z069 hlt) with q17 | hor
       ·exact Or.inl ⟨hlt,q17,hbf⟩
       ·exact Or.inr ⟨hlt,hor,hbf⟩
      exact ih _ qd1 q23 (by rw [z070,show n + (opnd C k 1 - n) = opnd C k 1 by omega];exact h1)
  apply qnt (C.output - n) q32
  rw [z070,show n + (C.output - n) = C.output by omega]
  exact hcx
 ·rintro ⟨a,ha,hva⟩
  rw [z098] at ha
  rw [congrFun hL.2.1 x]
  exact ha.2.2 x hva
lemma nonbelow_or_path {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {w v:ℕ} (hp:Relation.ReflTransGen (Budget.OrStep n C) w v):
  (∀ k,w = n + k→ ¬ BelowF G C k)→ ∀ k,v = n + k→ ¬ BelowF G C k:=by
 induction hp using Relation.ReflTransGen.head_induction_on with
 | refl=>exact fun hnb=>hnb
 | head hstep _ ih=>
  intro hnb
  obtain ⟨a,ha,rfl,hor,hin,_⟩:=hstep
  obtain ⟨b,hb⟩:=Budget.inputsAsOpnd hL.1 ha hin
  apply ih
  intro k heq hbelow
  apply z091 hL q01 hne ha hor (hnb a rfl) b
  rw [← hb,heq]
  exact hbelow

lemma z103 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2):
  ∀ w < n + C.gates.length,
   (∀ k,w = n + k→ ¬ BelowF G C k)→
   ∀ x:Fin n→ Bool,
    wval C x w = true↔
     (∃ u ∈ orIn n C w,x u = true)∨
     (OrReaches n C w g1∧ gateVal n C g1 x = true)∨
     (OrReaches n C w g2∧ gateVal n C g2 x = true):=by
 intro w _ hnb x
 constructor
 · intro hv
   obtain ⟨v,hr,hv',hcase⟩:=Budget.or_trace (n:=n) (C:=C)
    (x:=List.ofFn x) (by simp) w hv
   rcases hcase with hvn | ⟨k,hk,rfl,hkop⟩
   · exact Or.inl ⟨⟨v,hvn⟩,Budget.reach_mem_orIn _ hr,
      (Budget.val_ofFn C x ⟨v,hvn⟩).symm.trans hv'⟩
   · have hand:=(hL.1.1 _ (z069 hk)).resolve_right hkop
     have hnb':=nonbelow_or_path hL q01 hne hr hnb k rfl
     have hj:k ∈ junk G C:=z094.mpr ⟨hk,hand,hnb'⟩
     have hreach:=Budget.reach_orReaches hr k rfl hk
     rcases (q00 k).mp hj with rfl | rfl
     · exact Or.inr (Or.inl ⟨hreach,hv'⟩)
     · exact Or.inr (Or.inr ⟨hreach,hv'⟩)
 · rintro (⟨u,hu,hxu⟩ | ⟨hr,hg⟩ | ⟨hr,hg⟩)
   · exact Budget.reach_var_val x w u (Budget.mem_orIn_reach u hu) hxu
   · exact Budget.orStep_up (n:=n) (by simp) (Budget.orReaches_reach _ _ hr).1 hg
   · exact Budget.orStep_up (n:=n) (by simp) (Budget.orReaches_reach _ _ hr).1 hg

lemma z102 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  (h4:NoFourCycle G) {a b w1 w2:Fin n} (hab:a ≠ b)
  (ha1:G.Adj a w1) (hb1:G.Adj b w1) (ha2:G.Adj a w2) (hb2:G.Adj b w2):w1 = w2:=by
 exact Geometry.common_neighbor_unique G h4 a b w1 w2 hab ha1 hb1 ha2 hb2
def z132 := @Budget.topAdj

lemma z129 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) {a:ℕ} (ha:a ∈ tops G C \ centreless G C):
  (side (n:=n) C a 0).Nonempty∧ (side (n:=n) C a 1).Nonempty∧ 
   ((side (n:=n) C a 0).card = 1∨ (side (n:=n) C a 1).card = 1):=by
 rw [Finset.mem_sdiff] at ha
 have qmf:(side (n:=n) C a 0).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro h0;exact ha.2 (Finset.mem_filter.mpr ⟨ha.1,Or.inl h0⟩)
 have qgb:(side (n:=n) C a 1).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro h1;exact ha.2 (Finset.mem_filter.mpr ⟨ha.1,Or.inr h1⟩)
 refine ⟨qmf,qgb,?_⟩
 by_contra qb1
 push Not at qb1
 have hc0:1 < (side (n:=n) C a 0).card:=by
  have:=Finset.Nonempty.card_pos qmf;omega
 have hc1:1 < (side (n:=n) C a 1).card:=by
  have:=Finset.Nonempty.card_pos qgb;omega
 obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp hc0
 obtain ⟨v1,hv1,v2,hv2,qnv⟩:=Finset.one_lt_card.mp hc1
 exact qnv (z102 h4 qd2
  (z132 hAO ha.1 hu1 hv1) (z132 hAO ha.1 hu2 hv1)
  (z132 hAO ha.1 hu1 hv2) (z132 hAO ha.1 hu2 hv2))
lemma z139 {n:ℕ} (gs1 gs2:List Gate) (o1 o2:ℕ) (x:Fin n→ Bool)
  {w:ℕ} (hw:w < n + gs1.length):
  wval ⟨gs1 ++ gs2,o2⟩ x w = wval ⟨gs1,o1⟩ x w:=by
 exact CriticalEdge.run_prefix gs1 gs2 (List.ofFn x) w (by simpa using hw)
def z008 (n:ℕ) (gs:List Gate):List ℕ→ List Gate × ℕ
 | []=>(gs,0)
 | [w]=>(gs,w)
 | w::w2::ws=>
  let res:=z008 n gs (w2::ws)
  (res.1 ++ [⟨GateOp.or,[w,res.2]⟩],n + res.1.length)
lemma z011 (n:ℕ) (gs:List Gate) (ws:List ℕ):
  ∃ extra:List Gate,(z008 n gs ws).1 = gs ++ extra:=by
 match ws with
 | []=>exact ⟨[],by simp [z008]⟩
 | [w]=>exact ⟨[],by simp [z008]⟩
 | w::w2::ws=>
  obtain ⟨extra,heq⟩:=z011 n gs (w2::ws)
  refine ⟨extra ++ [⟨GateOp.or,[w,(z008 n gs (w2::ws)).2]⟩],?_⟩
  simp only [z008,heq,List.append_assoc]
lemma z010 (n:ℕ) (gs:List Gate) (ws:List ℕ) (hne:ws ≠ []):
  (z008 n gs ws).1.length = gs.length + (ws.length - 1):=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>simp [z008]
 | w::w2::ws=>
  have ih:=z010 n gs (w2::ws) (by simp)
  simp only [z008,List.length_append,List.length_cons,List.length_nil] at ih ⊢
  omega
lemma z009 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (ws:List ℕ) (hne:ws ≠ []) (hws:∀ w ∈ ws,w < n + gs.length):
  IsAO2 n ⟨(z008 n gs ws).1,0⟩∧ 
   (z008 n gs ws).2 < n + (z008 n gs ws).1.length:=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>
  simp only [z008]
  exact ⟨hAO,hws w (by simp)⟩
 | w::w2::ws=>
  have ⟨q4x,qnw⟩:=z009 hAO (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have qju:gs.length ≤ (z008 n gs (w2::ws)).1.length:=by
   rw [z010 n gs (w2::ws) (by simp)];omega
  have qjv:w < n + (z008 n gs (w2::ws)).1.length:=by have:=hws w (by simp);omega
  simp only [z008]
  set gs':=(z008 n gs (w2::ws)).1
  set w':=(z008 n gs (w2::ws)).2
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  ·intro g hg
   simp only [List.mem_append,List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact q4x.1 g hg
   ·exact Or.inr rfl
  ·intro j hj u hu
   simp only [List.length_append,List.length_singleton] at hj
   by_cases hlt:j < gs'.length
   ·have q4a:gateAt ⟨gs' ++ [⟨GateOp.or,[w,w']⟩],0⟩ j = gateAt ⟨gs',0⟩ j:=by
     rw [z068 (by simp;omega),z068 hlt]
     simp [List.getElem_append_left hlt]
    rw [q4a] at hu
    exact q4x.2.1 j hlt u hu
   ·have qjw:j = gs'.length:=by omega
    subst qjw
    have q4a:gateAt ⟨gs' ++ [⟨GateOp.or,[w,w']⟩],0⟩ gs'.length = ⟨GateOp.or,[w,w']⟩:=by
     rw [z068 (by simp)]
     simp
    rw [q4a] at hu
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    ·exact qjv
    ·exact qnw
  ·intro g hg
   simp only [List.mem_append,List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact q4x.2.2 g hg
   ·rfl
  ·simp only [List.length_append,List.length_singleton];omega
lemma z012 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩) (x:Fin n→ Bool)
  (ws:List ℕ) (hne:ws ≠ []) (hws:∀ w ∈ ws,w < n + gs.length):
  wval ⟨(z008 n gs ws).1,0⟩ x (z008 n gs ws).2 =
   decide (∃ w ∈ ws,wval ⟨gs,0⟩ x w = true):=by
 match ws with
 | []=>exact absurd rfl hne
 | [w]=>
  simp only [z008,List.mem_singleton,exists_eq_left]
  cases wval ⟨gs,0⟩ x w <;> rfl
 | w::w2::ws=>
  have qd3:=z009 hAO (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have ih:=z012 hAO x (w2::ws) (by simp) (fun u hu=>hws u (by simp [hu]))
  have q4z:=z009 hAO (w::w2::ws) (by simp) hws
  obtain ⟨extra,qc6⟩:=z011 n gs (w2::ws)
  simp only [z008] at q4z ⊢
  set gs':=(z008 n gs (w2::ws)).1
  set w':=(z008 n gs (w2::ws)).2
  have qju:gs.length ≤ gs'.length:=by rw [qc6,List.length_append];omega
  have qjv:w < n + gs.length:=hws w (by simp)
  have q4a:gateAt ⟨gs' ++ [⟨GateOp.or,[w,w']⟩],0⟩ gs'.length = ⟨GateOp.or,[w,w']⟩:=by
   rw [z068 (by simp)];simp
  have qd4:opnd ⟨gs' ++ [⟨GateOp.or,[w,w']⟩],0⟩ gs'.length 0 = w:=by
   unfold opnd;rw [q4a];rfl
  have qd5:opnd ⟨gs' ++ [⟨GateOp.or,[w,w']⟩],0⟩ gs'.length 1 = w':=by
   unfold opnd;rw [q4a];rfl
  have qd6:gs'.length < (gs' ++ [({ op:=GateOp.or,inputs:=[w,w']}:Gate)]).length:=by simp
  rw [z142 q4z.1 x qd6 (by rw [q4a]),qd4,qd5]
  rw [z139 gs' [({ op:=GateOp.or,inputs:=[w,w']}:Gate)] 0 0 x (by omega),
   z139 gs' [({ op:=GateOp.or,inputs:=[w,w']}:Gate)] 0 0 x qd3.2]
  have hvw:wval ⟨gs',0⟩ x w = wval ⟨gs,0⟩ x w:=by
   rw [qc6];exact z139 gs extra 0 0 x qjv
  rw [hvw,ih]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,exists_eq_or_imp]
lemma z007 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  {op:GateOp} (hop:op = GateOp.and∨ op = GateOp.or)
  {w0 w1:ℕ} (h0:w0 < n + gs.length) (h1:w1 < n + gs.length):
  IsAO2 n ⟨gs ++ [⟨op,[w0,w1]⟩],0⟩:=by
 apply CriticalEdge.ok_ao
 apply CriticalEdge.ok_snoc ?_ hop h0 h1
 intro j hj
 have h := CriticalEdge.gate2 hAO hj
 refine ⟨(gateAt ⟨gs, 0⟩ j).op, opnd ⟨gs, 0⟩ j 0, opnd ⟨gs, 0⟩ j 1,
   ?_, h.2.2.2.2, h.2.2.1, h.2.2.2.1⟩
 rw [h.1]
 exact congrArg (Gate.mk (gateAt ⟨gs, 0⟩ j).op) h.2.1
def z016 (n:ℕ) (C:Circuit) (lamList:List ℕ):ℕ→ ℕ
 | w=>
  if hw:w < n then w
  else
   let k:=w - n
   if hk:k < C.gates.length then
    if k ∈ lamList then n + lamList.idxOf k
    else if (orIn n C (opnd C k 0)).Nonempty then
     if hlt:opnd C k 0 < w then z016 n C lamList (opnd C k 0) else 0
    else
     if hlt:opnd C k 1 < w then z016 n C lamList (opnd C k 1) else 0
   else 0
termination_by w=>w
def z082 (n:ℕ) (C:Circuit) (lamList:List ℕ):List Gate:=
 lamList.map fun k=>⟨GateOp.or,[z016 n C lamList (opnd C k 0),z016 n C lamList (opnd C k 1)]⟩
lemma z017 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (lamList:List ℕ)
  (q1m:lamList.Pairwise (· < ·)):
  ∀ w < n + C.gates.length,z016 n C lamList w < n∨ 
   (n ≤ w∧ ∃ k ∈ lamList,k ≤ w - n∧ z016 n C lamList w = n + lamList.idxOf k):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro qnx
  unfold z016
  dsimp only
  split_ifs with hw hk q23 h0 q80 h1
  ·exact Or.inl hw
  ·exact Or.inr ⟨by omega,w - n,q23,le_refl _,rfl⟩
  ·rcases ih (opnd C (w - n) 0) q80 (by omega) with hlt | ⟨qmg,k,qd7,qny,heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega,k,qd7,by omega,heq⟩
  ·exfalso;have:=z104 hAO hk 0;omega
  ·rcases ih (opnd C (w - n) 1) h1 (by omega) with hlt | ⟨qmg,k,qd7,qny,heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega,k,qd7,by omega,heq⟩
  ·exfalso;have:=z104 hAO hk 1;omega
  ·exfalso;omega
lemma z077 {l:List ℕ} (q1m:l.Pairwise (· < ·))
  {a b:ℕ} (ha:a ∈ l) (hb:b ∈ l) (hab:a < b):l.idxOf a < l.idxOf b:=by
 induction l with
 | nil=>cases ha
 | cons x xs ih=>
  rw [List.pairwise_cons] at q1m
  simp only [List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  ·omega
  ·rw [List.idxOf_cons_self]
   have hne:a ≠ b:=Nat.ne_of_lt hab
   rw [List.idxOf_cons_ne _ (by simp [hne])]
   exact Nat.succ_pos _
  ·have:=q1m.1 a ha;omega
  ·have qnz:x ≠ a:=by have:=q1m.1 a ha;omega
   have qax:x ≠ b:=by have:=q1m.1 b hb;omega
   rw [List.idxOf_cons_ne _ (by simp [qnz]),List.idxOf_cons_ne _ (by simp [qax])]
   exact Nat.succ_lt_succ (ih q1m.2 ha hb)
lemma z076 {l:List ℕ} (q61:l.Nodup) (j:ℕ) (hj:j < l.length):
  l.idxOf l[j] = j:=by
 induction l generalizing j with
 | nil=>cases hj
 | cons x xs ih=>
  rw [List.nodup_cons] at q61
  cases j with
  | zero=>simp
  | succ j'=>
   simp only [List.getElem_cons_succ]
   have hj':j' < xs.length:=by simp only [List.length_cons] at hj;omega
   have hne:x ≠ xs[j']:=fun h=>q61.1 (h ▸ List.getElem_mem hj')
   rw [List.idxOf_cons_ne _ (by simp [hne]),ih q61.2 j' hj']
lemma z083 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
  (lamList:List ℕ) (q1m:lamList.Pairwise (· < ·))
  (q4b:∀ k ∈ lamList,k < C.gates.length):
  IsAO2 n ⟨z082 n C lamList,0⟩:=by
 refine ⟨?_,?_,?_⟩
 ·intro g hg
  simp only [z082,List.mem_map] at hg
  rcases hg with ⟨k,_,rfl⟩
  exact Or.inr rfl
 ·intro j hj u hu
  simp only [z082,List.length_map] at hj
  rw [z068 (by simp [z082,hj])] at hu
  simp only [z082,List.getElem_map,List.mem_cons,List.not_mem_nil,or_false] at hu
  set k:=lamList[j]
  have q3w:k ∈ lamList:=List.getElem_mem hj
  have q0d:k < C.gates.length:=q4b k q3w
  have q92:lamList.idxOf k = j:=by
   have q61:lamList.Nodup:=q1m.imp (fun {a b} h=>Nat.ne_of_lt h)
   exact z076 q61 j hj
  have check_b:∀ b:Fin 2,z016 n C lamList (opnd C k b) < n + j:=by
   intro b
   have qph:opnd C k b < n + k:=z104 hAO q0d b
   rcases z017 hAO lamList q1m (opnd C k b) (by omega) with hlt | ⟨qmg,k',qo0,qo1,heq⟩
   ·omega
   ·rw [heq]
    have qjx:k' < k:=by omega
    have qd8:=z077 q1m qo0 q3w qjx
    rw [q92] at qd8
    omega
  rcases hu with rfl | rfl
  ·exact check_b 0
  ·exact check_b 1
 ·intro g hg
  simp only [z082,List.mem_map] at hg
  rcases hg with ⟨k,_,rfl⟩
  rfl
def z001 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (w:ℕ):Prop:=
 w < n + C.gates.length∧ (orIn n C w).Nonempty∧ 
  (∀ k,w = n + k→ ¬ BelowF G C k)∧ 
  (∀ k,OrReaches n C w k→ k ∈ orN G C→ 
   (orIn n C (opnd C k 0)).Nonempty→ (orIn n C (opnd C k 1)).Nonempty→ k ∈ lam G C)
lemma z087 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {k:ℕ} (hk:k ∈ orN G C) (hlw:z001 G C (n + k))
  (b:Fin 2) (qax:(orIn n C (opnd C k b)).Nonempty):
  z001 G C (opnd C k b):=by
 have hk':=z096.mp hk
 have hlt:opnd C k b < n + k:=z104 hL.1 hk'.1 b
 refine ⟨by omega,qax,?_,?_⟩
 ·intro m hm hbm
  exact z091 hL q01 hne hk'.1 hk'.2.1 hk'.2.2 b (by rw [hm];exact hbm)
 ·intro m hrm q9d h0 h1
  apply hlw.2.2.2 m _ q9d h0 h1
  exact (z111 hk'.1).mpr
   (Or.inr ⟨hk'.2.1,opnd C k b,z105 hL.1 hk'.1 b,hrm.1,hlt,hrm⟩)
lemma z086 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a ∈ tops G C) (b:Fin 2)
  (qax:(side (n:=n) C a b).Nonempty) (q18:(side (n:=n) C a (1 - b)).card = 1):
  z001 G C (opnd C a b):=by
 have ha':=z098.mp ha
 have hlt:opnd C a b < n + a:=z104 hL.1 ha'.1 b
 refine ⟨by omega,qax,?_,?_⟩
 ·intro m hm hbm
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 ·intro m hrm q9d h0 h1
  unfold lam
  exact Finset.mem_filter.mpr ⟨q9d,h0,h1,a,ha,b,q18,hrm⟩
lemma z018 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  (lamList:List ℕ) (q1m:lamList.Pairwise (· < ·))
  (q0s:∀ k,k ∈ lamList↔ k ∈ lam G C)
  (x:Fin n→ Bool):
  ∀ w,z001 G C w→ 
   z016 n C lamList w < n + lamList.length∧ 
   wval ⟨z082 n C lamList,0⟩ x (z016 n C lamList w) =
    decide (∃ u ∈ orIn n C w,x u = true):=by
 have q4b:∀ k ∈ lamList,k < C.gates.length:=fun k hk=>by
  have:=(q0s k).mp hk;exact (z096.mp (Finset.mem_filter.mp this).1).1
 have qd9:=z083 hL.1 lamList q1m q4b
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hlw
  by_cases hwn:w < n
  ·have hbp:z016 n C lamList w = w:=by unfold z016;rw [dif_pos hwn]
   rw [hbp]
   refine ⟨by omega,?_⟩
   rw [z144 _ x w hwn]
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq]
   constructor
   ·intro h;exact ⟨⟨w,hwn⟩,(z095 C _ _).mpr rfl,h⟩
   ·rintro ⟨u,hu,hxu⟩
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    subst heq;exact hxu
  ·have q0d:w - n < C.gates.length:=by have:=hlw.1;omega
   have q0f:w = n + (w - n):=by omega
   set k:=w - n
   have q5w:¬ BelowF G C k:=hlw.2.2.1 k q0f
   have q3d:(gateAt C k).op = GateOp.or:=by
    rcases hL.1.1 _ (z069 q0d) with q17 | hor
    ·exfalso
     have q0g:=z107 (n:=n) q0d q17
     rw [← q0f] at q0g
     exact hlw.2.1.ne_empty q0g
    ·exact hor
   have q04:k ∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
   have q9e:z001 G C (n + k):=by rwa [← q0f]
   have q0o:orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1):=by
    rw [q0f];exact z108 hL.1 q0d q3d
   have q80:opnd C k 0 < w:=by have:=z104 hL.1 q0d 0;omega
   have q58:opnd C k 1 < w:=by have:=z104 hL.1 q0d 1;omega
   by_cases q23:k ∈ lamList
   ·have hbp:z016 n C lamList w = n + lamList.idxOf k:=by
     unfold z016;rw [dif_neg hwn,dif_pos q0d,if_pos q23]
    have q9f:lamList.idxOf k < lamList.length:=List.idxOf_lt_length_iff.mpr q23
    have hkl:k ∈ lam G C:=(q0s k).mp q23
    have q6w:(orIn n C (opnd C k 0)).Nonempty:=(Finset.mem_filter.mp hkl).2.1
    have q62:(orIn n C (opnd C k 1)).Nonempty:=(Finset.mem_filter.mp hkl).2.2.1
    have ih0:=ih (opnd C k 0) q80 (z087 hL q01 hne q04 q9e 0 q6w)
    have ih1:=ih (opnd C k 1) q58 (z087 hL q01 hne q04 q9e 1 q62)
    rw [hbp]
    refine ⟨by omega,?_⟩
    have hj':lamList.idxOf k < (z082 n C lamList).length:=by simp [z082,q9f]
    have qo2:lamList[lamList.idxOf k] = k:=List.getElem_idxOf q9f
    have q4a:gateAt ⟨z082 n C lamList,0⟩ (lamList.idxOf k) =
      ⟨GateOp.or,[z016 n C lamList (opnd C k 0),z016 n C lamList (opnd C k 1)]⟩:=by
     rw [z068 hj'];simp [z082,qo2]
    rw [z142 qd9 x hj' (by rw [q4a])]
    have qd4:opnd ⟨z082 n C lamList,0⟩ (lamList.idxOf k) 0 =
      z016 n C lamList (opnd C k 0):=by unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨z082 n C lamList,0⟩ (lamList.idxOf k) 1 =
      z016 n C lamList (opnd C k 1):=by unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,ih0.2,ih1.2,q0o]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq,Finset.mem_union]
    constructor
    ·rintro (⟨u,hu,hxu⟩ | ⟨u,hu,hxu⟩)
     ·exact ⟨u,Or.inl hu,hxu⟩
     ·exact ⟨u,Or.inr hu,hxu⟩
    ·rintro ⟨u,hu | hu,hxu⟩
     ·exact Or.inl ⟨u,hu,hxu⟩
     ·exact Or.inr ⟨u,hu,hxu⟩
   ·have q5b:¬ ((orIn n C (opnd C k 0)).Nonempty∧ (orIn n C (opnd C k 1)).Nonempty):=by
     rintro ⟨h0,h1⟩
     apply q23
     rw [q0s]
     exact q9e.2.2.2 k (z115 q0d) q04 h0 h1
    by_cases q6w:(orIn n C (opnd C k 0)).Nonempty
    ·have q5c:orIn n C (opnd C k 1) = ∅:=by
      by_contra qgb;exact q5b ⟨q6w,Finset.nonempty_iff_ne_empty.mpr qgb⟩
     have hbp:z016 n C lamList w = z016 n C lamList (opnd C k 0):=by
      conv_lhs=>unfold z016
      dsimp only
      rw [dif_neg hwn,dif_pos q0d,if_neg q23,if_pos q6w,dif_pos q80]
     rw [hbp,q0o,q5c,Finset.union_empty]
     exact ih (opnd C k 0) q80 (z087 hL q01 hne q04 q9e 0 q6w)
    ·have q50:orIn n C (opnd C k 0) = ∅:=Finset.not_nonempty_iff_eq_empty.mp q6w
     have q62:(orIn n C (opnd C k 1)).Nonempty:=by
      have qay:=hlw.2.1
      rw [q0o,q50,Finset.empty_union] at qay
      exact qay
     have hbp:z016 n C lamList w = z016 n C lamList (opnd C k 1):=by
      conv_lhs=>unfold z016
      dsimp only
      rw [dif_neg hwn,dif_pos q0d,if_neg q23,if_neg q6w,dif_pos q58]
     rw [hbp,q0o,q50,Finset.empty_union]
     exact ih (opnd C k 1) q58 (z087 hL q01 hne q04 q9e 1 q62)
def z003 (n:ℕ) (gs:List Gate) (v:Fin n) (base:Option ℕ) (extra:List (Fin n)):
  List Gate × ℕ:=
 match base,extra with
 | some bw,[]=>
  (gs ++ [⟨GateOp.and,[v.val,bw]⟩],n + gs.length)
 | some bw,e::es=>
  let r1:=z008 n gs ((e::es).map Fin.val)
  let gs2:=r1.1 ++ [⟨GateOp.or,[bw,r1.2]⟩]
  (gs2 ++ [⟨GateOp.and,[v.val,n + r1.1.length]⟩],n + gs2.length)
 | none,e::es=>
  let r1:=z008 n gs ((e::es).map Fin.val)
  (r1.1 ++ [⟨GateOp.and,[v.val,r1.2]⟩],n + r1.1.length)
 | none,[]=>(gs,0)
def z005 (n:ℕ) (gs:List Gate):
  List (Fin n × Option ℕ × List (Fin n))→ List Gate × List ℕ
 | []=>(gs,[])
 | (v,base,extra)::rest=>
  let r:=z003 n gs v base extra
  let r2:=z005 n r.1 rest
  (r2.1,r.2::r2.2)
lemma z004 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (v:Fin n) (base:Option ℕ) (extra:List (Fin n))
  (qgc:∀ bw,base = some bw→ bw < n + gs.length)
  (hne:base.isSome∨ extra ≠ []):
  (∃ ex:List Gate,(z003 n gs v base extra).1 = gs ++ ex)∧ 
  (z003 n gs v base extra).1.length =
   gs.length + extra.length + (if base.isSome then 1 else 0)∧ 
  IsAO2 n ⟨(z003 n gs v base extra).1,0⟩∧ 
  (z003 n gs v base extra).2 < n + (z003 n gs v base extra).1.length∧ 
  ∀ x:Fin n→ Bool,
   wval ⟨(z003 n gs v base extra).1,0⟩ x (z003 n gs v base extra).2 =
    (x v && (decide (∃ bw,base = some bw∧ wval ⟨gs,0⟩ x bw = true) ||
     decide (∃ u ∈ extra,x u = true))):=by
 cases base with
 | none=>
  cases extra with
  | nil=>simp at hne
  | cons e es=>
   have hws:∀ w ∈ (e::es).map Fin.val,w < n + gs.length:=by
    intro w hw;simp only [List.mem_map] at hw;rcases hw with ⟨u,_,rfl⟩;omega
   obtain ⟨ex1,q94⟩:=z011 n gs ((e::es).map Fin.val)
   have q9g:=z010 n gs ((e::es).map Fin.val) (by simp)
   have ⟨qda,q58⟩:=z009 hAO ((e::es).map Fin.val) (by simp) hws
   dsimp only [z003]
   set gs1:=(z008 n gs ((e::es).map Fin.val)).1
   set w1:=(z008 n gs ((e::es).map Fin.val)).2
   have q8p:=z007 qda (Or.inl rfl) (by omega:v.val < n + gs1.length) q58
   refine ⟨⟨ex1 ++ [⟨GateOp.and,[v.val,w1]⟩],by rw [q94,List.append_assoc]⟩,
    ?_,q8p,by simp,?_⟩
   ·simp only [List.length_append,List.length_cons,List.length_nil,q9g,List.length_map,
     Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    omega
   ·intro x
    have q4a:gateAt ⟨gs1 ++ [⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length =
      ⟨GateOp.and,[v.val,w1]⟩:=by rw [z068 (by simp)];simp
    rw [z140 q8p x (by simp) (by rw [q4a])]
    have qd4:opnd ⟨gs1 ++ [⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length 0 = v.val:=by
     unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨gs1 ++ [⟨GateOp.and,[v.val,w1]⟩],0⟩ gs1.length 1 = w1:=by
     unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,z144 _ x v.val v.isLt,
     z139 gs1 [⟨GateOp.and,[v.val,w1]⟩] 0 0 x q58,
     z012 hAO x ((e::es).map Fin.val) (by simp) hws]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.mem_map,false_or,reduceCtorEq,false_and,exists_false]
    constructor
    ·rintro ⟨_,⟨u,hu,rfl⟩,hxu⟩
     rw [z144 _ x u.val u.isLt] at hxu;exact ⟨u,hu,hxu⟩
    ·rintro ⟨u,hu,hxu⟩
     exact ⟨u.val,⟨u,hu,rfl⟩,by rw [z144 _ x u.val u.isLt];exact hxu⟩
 | some bw=>
  have hbw:bw < n + gs.length:=qgc bw rfl
  cases extra with
  | nil=>
   have q8p:=z007 hAO (Or.inl rfl) (by omega:v.val < n + gs.length) hbw
   refine ⟨⟨[⟨GateOp.and,[v.val,bw]⟩],rfl⟩,?_,q8p,by simp [z003],?_⟩
   ·simp [z003]
   ·intro x
    simp only [z003]
    have q4a:gateAt ⟨gs ++ [⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length =
      ⟨GateOp.and,[v.val,bw]⟩:=by rw [z068 (by simp)];simp
    rw [z140 q8p x (by simp) (by rw [q4a])]
    have qd4:opnd ⟨gs ++ [⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length 0 = v.val:=by
     unfold opnd;rw [q4a];rfl
    have qd5:opnd ⟨gs ++ [⟨GateOp.and,[v.val,bw]⟩],0⟩ gs.length 1 = bw:=by
     unfold opnd;rw [q4a];rfl
    rw [qd4,qd5,z144 _ x v.val v.isLt,
     z139 gs [⟨GateOp.and,[v.val,bw]⟩] 0 0 x hbw]
    congr 1
    cases h:wval ⟨gs,0⟩ x bw <;> simp [h]
  | cons e es=>
   have hws:∀ w ∈ (e::es).map Fin.val,w < n + gs.length:=by
    intro w hw;simp only [List.mem_map] at hw;rcases hw with ⟨u,_,rfl⟩;omega
   obtain ⟨ex1,q94⟩:=z011 n gs ((e::es).map Fin.val)
   have q9g:=z010 n gs ((e::es).map Fin.val) (by simp)
   have ⟨qda,q58⟩:=z009 hAO ((e::es).map Fin.val) (by simp) hws
   dsimp only [z003]
   set gs1:=(z008 n gs ((e::es).map Fin.val)).1
   set w1:=(z008 n gs ((e::es).map Fin.val)).2
   have qmh:bw < n + gs1.length:=by rw [q94,List.length_append];omega
   have q8p:=z007 qda (Or.inr rfl) qmh q58
   set gs2:=gs1 ++ [⟨GateOp.or,[bw,w1]⟩]
   have qj2:=z007 q8p (Or.inl rfl)
    (by simp [gs2];omega:v.val < n + gs2.length) (by simp [gs2]:n + gs1.length < n + gs2.length)
   refine ⟨⟨ex1 ++ [⟨GateOp.or,[bw,w1]⟩,⟨GateOp.and,[v.val,n + gs1.length]⟩],
     by simp only [gs2,q94,List.append_assoc];rfl⟩,
    ?_,qj2,by simp [gs2],?_⟩
   ·simp only [gs2,List.length_append,List.length_cons,List.length_nil,q9g,
     List.length_map,Option.isSome_some,↓reduceIte]
    omega
   ·intro x
    have qdb:gateAt ⟨gs2 ++ [⟨GateOp.and,[v.val,n + gs1.length]⟩],0⟩ gs2.length =
      ⟨GateOp.and,[v.val,n + gs1.length]⟩:=by rw [z068 (by simp)];simp
    rw [z140 qj2 x (by simp) (by rw [qdb])]
    have qjy:opnd ⟨gs2 ++ [⟨GateOp.and,[v.val,n + gs1.length]⟩],0⟩ gs2.length 0 = v.val:=by
     unfold opnd;rw [qdb];rfl
    have qjz:opnd ⟨gs2 ++ [⟨GateOp.and,[v.val,n + gs1.length]⟩],0⟩ gs2.length 1 =
      n + gs1.length:=by unfold opnd;rw [qdb];rfl
    rw [qjy,qjz,z144 _ x v.val v.isLt,
     z139 gs2 [⟨GateOp.and,[v.val,n + gs1.length]⟩] 0 0 x (by simp [gs2])]
    have qdc:gateAt ⟨gs2,0⟩ gs1.length = ⟨GateOp.or,[bw,w1]⟩:=by
     rw [z068 (by simp [gs2])];simp [gs2]
    rw [z142 q8p x (by simp [gs2]) (by rw [qdc])]
    have qk0:opnd ⟨gs2,0⟩ gs1.length 0 = bw:=by unfold opnd;rw [qdc];rfl
    have qk1:opnd ⟨gs2,0⟩ gs1.length 1 = w1:=by unfold opnd;rw [qdc];rfl
    rw [qk0,qk1,z139 gs1 [⟨GateOp.or,[bw,w1]⟩] 0 0 x qmh,
     z139 gs1 [⟨GateOp.or,[bw,w1]⟩] 0 0 x q58]
    have qo3:wval ⟨gs1,0⟩ x bw = wval ⟨gs,0⟩ x bw:=by
     rw [q94];exact z139 gs ex1 0 0 x hbw
    rw [qo3,z012 hAO x ((e::es).map Fin.val) (by simp) hws]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.mem_map,Option.some.injEq,exists_eq_left']
    constructor
    ·rintro (h | ⟨_,⟨u,hu,rfl⟩,hxu⟩)
     ·exact Or.inl h
     ·rw [z144 _ x u.val u.isLt] at hxu;exact Or.inr ⟨u,hu,hxu⟩
    ·rintro (h | ⟨u,hu,hxu⟩)
     ·exact Or.inl h
     ·exact Or.inr ⟨u.val,⟨u,hu,rfl⟩,by rw [z144 _ x u.val u.isLt];exact hxu⟩
lemma z006 {n:ℕ} {gs:List Gate} (hAO:IsAO2 n ⟨gs,0⟩)
  (items:List (Fin n × Option ℕ × List (Fin n)))
  (q9h:∀ it ∈ items,(∀ bw,it.2.1 = some bw→ bw < n + gs.length)∧ 
   (it.2.1.isSome∨ it.2.2 ≠ [])):
  (∃ ex:List Gate,(z005 n gs items).1 = gs ++ ex)∧ 
  (z005 n gs items).1.length =
   gs.length + (items.map fun it=>it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum∧ 
  (z005 n gs items).2.length = items.length∧ 
  IsAO2 n ⟨(z005 n gs items).1,0⟩∧ 
  (∀ w ∈ (z005 n gs items).2,w < n + (z005 n gs items).1.length)∧ 
  ∀ x:Fin n→ Bool,
   (∃ w ∈ (z005 n gs items).2,wval ⟨(z005 n gs items).1,0⟩ x w = true)↔ 
    ∃ it ∈ items,x it.1 = true∧ 
     ((∃ bw,it.2.1 = some bw∧ wval ⟨gs,0⟩ x bw = true)∨ 
      ∃ u ∈ it.2.2,x u = true):=by
 induction items generalizing gs with
 | nil=>
  refine ⟨⟨[],by simp [z005]⟩,by simp [z005],rfl,hAO,by simp [z005],?_⟩
  intro x;simp [z005]
 | cons it rest ih=>
  rcases it with ⟨v,base,extra⟩
  have hit:=q9h (v,base,extra) (by simp)
  obtain ⟨⟨ex1,q94⟩,q9g,qda,q58,qk2⟩:=z004 hAO v base extra hit.1 hit.2
  dsimp only [z005]
  set r:=z003 n gs v base extra
  have qd3:∀ it' ∈ rest,(∀ bw,it'.2.1 = some bw→ bw < n + r.1.length)∧ 
    (it'.2.1.isSome∨ it'.2.2 ≠ []):=by
   intro it' qk3
   have h0:=q9h it' (by simp [qk3])
   exact ⟨fun bw hbw=>by have:=h0.1 bw hbw;rw [q94,List.length_append];omega,h0.2⟩
  obtain ⟨⟨ex2,qb2⟩,qdd,q63,q8p,qj3,qde⟩:=ih qda qd3
  refine ⟨⟨ex1 ++ ex2,by rw [qb2,q94,List.append_assoc]⟩,?_,?_,q8p,?_,?_⟩
  ·simp only [qdd,q9g,List.map_cons,List.sum_cons];omega
  ·simp only [List.length_cons,q63]
  ·intro w hw
   simp only [List.mem_cons] at hw
   rcases hw with rfl | hw
   ·rw [qb2,List.length_append];omega
   ·exact qj3 w hw
  ·intro x
   simp only [List.mem_cons,exists_eq_or_imp]
   have hvw:wval ⟨(z005 n r.1 rest).1,0⟩ x r.2 =
     (x v && (decide (∃ bw,base = some bw∧ wval ⟨gs,0⟩ x bw = true) ||
      decide (∃ u ∈ extra,x u = true))):=by
    rw [qb2,z139 r.1 ex2 0 0 x q58,qk2 x]
   have q9i:(∃ w ∈ (z005 n r.1 rest).2,wval ⟨(z005 n r.1 rest).1,0⟩ x w = true)↔ 
     ∃ it' ∈ rest,x it'.1 = true∧ 
      ((∃ bw,it'.2.1 = some bw∧ wval ⟨gs,0⟩ x bw = true)∨ 
       ∃ u ∈ it'.2.2,x u = true):=by
    rw [qde x]
    apply exists_congr;intro it'
    apply and_congr_right;intro qk3
    apply and_congr_right;intro _
    apply or_congr_left
    apply exists_congr;intro bw
    apply and_congr_right;intro hbw
    have qgd:=(q9h it' (by simp [qk3])).1 bw hbw
    rw [q94,z139 gs ex1 0 0 x qgd]
   rw [hvw,q9i]
   simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
lemma z093 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  {g1 g2:ℕ} (qdf:g1 ≠ g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  (hne:∃ u v:Fin n,G.Adj u v)
  (Zact Zhas:Finset (Fin n)) (L:Fin n→ Finset (Fin n)) (topOf:Fin n→ ℕ)
  (q5d:Zhas ⊆ Zact)
  (q8q:∀ v ∈ Zact,(L v).Nonempty)
  (qge:∀ v ∈ Zact,∀ u ∈ L v,G.Adj v u)
  (qgf:∀ e ∈ Ustar G C,∃ v ∈ Zact,∃ u ∈ L v,e = s(v,u))
  (q41:∀ v ∈ Zhas,topOf v ∈ tops G C \ centreless G C)
  (q64:∀ v ∈ Zhas,side (n:=n) C (topOf v) 0 = {v}∨ side (n:=n) C (topOf v) 1 = {v})
  (q5e:∀ v1 ∈ Zhas,∀ v2 ∈ Zhas,topOf v1 = topOf v2→ v1 = v2):
  2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
   (∑ v ∈ Zact,(L v).card) + (Zact \ Zhas).card:=by
 classical
 set S_tops:=tops G C \ centreless G C
 set lamList:=(lam G C).sort (· ≤ ·)
 have q1m:lamList.Pairwise (· < ·):=
  ((Finset.pairwise_sort (lam G C) (· ≤ ·)).and (Finset.sort_nodup (lam G C) (· ≤ ·))).imp
   (fun ⟨h1,h2⟩=>Nat.lt_of_le_of_ne h1 h2)
 have q0s:∀ k,k ∈ lamList↔ k ∈ lam G C:=fun k=>Finset.mem_sort (· ≤ ·)
 have q42:lamList.length = (lam G C).card:=Finset.length_sort (· ≤ ·)
 have q4b:∀ k ∈ lamList,k < C.gates.length:=fun k hk=>
  (z096.mp (Finset.mem_filter.mp ((q0s k).mp hk)).1).1
 set gs1:=z082 n C lamList
 have qda:IsAO2 n ⟨gs1,0⟩:=z083 hL.1 lamList q1m q4b
 have q43:gs1.length = (lam G C).card:=by simp [gs1,z082,q42]
 let mkTopItem:ℕ→ Fin n × Option ℕ × List (Fin n):=fun a=>
  if h:∃ v ∈ Zhas,topOf v = a then
   let v:=Classical.choose h
   have hv:=Classical.choose_spec h
   have hs:side (n:=n) C a 0 = {v}∨ side (n:=n) C a 1 = {v}:=by
    rw [← hv.2];exact q64 v hv.1
   let b:Fin 2:=if side (n:=n) C a 0 = {v} then 1 else 0
   (v,some (z016 n C lamList (opnd C a b)),(L v).toList)
  else
   if ha:a ∈ S_tops then
    have hst:=z129 hL.1 h4 ha
    if h0:(side (n:=n) C a 0).card = 1 then
     let v:=Classical.choose (Finset.card_eq_one.mp h0)
     (v,some (z016 n C lamList (opnd C a 1)),[])
    else
     have h1:(side (n:=n) C a 1).card = 1:=hst.2.2.resolve_left h0
     let v:=Classical.choose (Finset.card_eq_one.mp h1)
     (v,some (z016 n C lamList (opnd C a 0)),[])
   else
    (Classical.choose hne,none,[])
 let topItems:=S_tops.toList.map mkTopItem
 let newItems:=(Zact \ Zhas).toList.map fun v=>(v,(none:Option ℕ),(L v).toList)
 let allItems:=topItems ++ newItems
 have q19:∀ a ∈ S_tops,
   let it:=mkTopItem a
   (∀ bw,it.2.1 = some bw→ bw < n + gs1.length)∧ 
   it.2.1.isSome∧ 
   (∀ x:Fin n→ Bool,
    (x it.1 = true∧ ((∃ bw,it.2.1 = some bw∧ wval ⟨gs1,0⟩ x bw = true)∨ 
     ∃ u ∈ it.2.2,x u = true))↔ 
    ((∃ u ∈ side (n:=n) C a 0,x u = true)∧ (∃ v ∈ side (n:=n) C a 1,x v = true))∨ 
     ∃ v ∈ Zhas,topOf v = a∧ x v = true∧ ∃ u ∈ L v,x u = true):=by
  intro a ha
  have q25:a ∈ tops G C:=(Finset.mem_sdiff.mp ha).1
  have hst:=z129 hL.1 h4 ha
  by_cases h:∃ v ∈ Zhas,topOf v = a
  ·simp only [mkTopItem,dif_pos h]
   set v:=Classical.choose h
   have hv:=Classical.choose_spec h
   have hs:side (n:=n) C a 0 = {v}∨ side (n:=n) C a 1 = {v}:=by
    rw [← hv.2];exact q64 v hv.1
   set b:Fin 2:=if side (n:=n) C a 0 = {v} then 1 else 0
   have q51:side (n:=n) C a (1 - b) = {v}:=by
    by_cases h0:side (n:=n) C a 0 = {v}
    ·simp [b,h0]
    ·simp [b,h0];exact hs.resolve_left h0
   have q18:(side (n:=n) C a (1 - b)).card = 1:=by rw [q51];simp
   have qax:(side (n:=n) C a b).Nonempty:=by
    by_cases h0:side (n:=n) C a 0 = {v}
    ·simp [b,h0];exact hst.2.1
    ·simp [b,h0];exact hst.1
   have hlw:=z086 hL hne q25 b qax q18
   refine ⟨?_,rfl,?_⟩
   ·intro bw hbw
    injection hbw with hbw;subst hbw
    have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
    rw [q43,← q42];exact this
   ·intro x
    have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a b)) =
      decide (∃ u ∈ orIn n C (opnd C a b),x u = true):=
     (z018 hL q01 hne lamList q1m q0s x _ hlw).2
    simp only [Option.some.injEq,exists_eq_left',hbp,decide_eq_true_eq,Finset.mem_toList]
    have qk4:∀ v' ∈ Zhas,topOf v' = a→ v' = v:=fun v' hv' heq=>
     q5e v' hv' v hv.1 (heq.trans hv.2.symm)
    constructor
    ·rintro ⟨hxv,qb3 | ⟨u,hu,hxu⟩⟩
     ·left
      by_cases h0:side (n:=n) C a 0 = {v}
      ·simp only [b,if_pos h0] at qb3
       exact ⟨⟨v,by rw [h0];simp,hxv⟩,qb3⟩
      ·simp only [b,if_neg h0] at qb3
       have h1:side (n:=n) C a 1 = {v}:=hs.resolve_left h0
       exact ⟨qb3,⟨v,by rw [h1];simp,hxv⟩⟩
     ·right;exact ⟨v,hv.1,hv.2,hxv,u,hu,hxu⟩
    ·rintro (⟨h0,h1⟩ | ⟨v',hv',heq,qk5,u,hu,hxu⟩)
     ·by_cases hs0:side (n:=n) C a 0 = {v}
      ·simp only [b,if_pos hs0]
       rcases h0 with ⟨u0,hu0,qk6⟩
       rw [hs0,Finset.mem_singleton] at hu0;subst hu0
       exact ⟨qk6,Or.inl h1⟩
      ·simp only [b,if_neg hs0]
       have hs1:side (n:=n) C a 1 = {v}:=hs.resolve_left hs0
       rcases h1 with ⟨u1,hu1,qk7⟩
       rw [hs1,Finset.mem_singleton] at hu1;subst hu1
       exact ⟨qk7,Or.inl h0⟩
     ·have qk8:=qk4 v' hv' heq;subst qk8
      exact ⟨qk5,Or.inr ⟨u,hu,hxu⟩⟩
  ·simp only [mkTopItem,dif_neg h,dif_pos ha]
   by_cases h0:(side (n:=n) C a 0).card = 1
   ·simp only [dif_pos h0]
    set v:=Classical.choose (Finset.card_eq_one.mp h0)
    have hv:side (n:=n) C a 0 = {v}:=Classical.choose_spec (Finset.card_eq_one.mp h0)
    have hlw:=z086 hL hne q25 1 hst.2.1 (by simpa using h0)
    refine ⟨?_,rfl,?_⟩
    ·intro bw hbw
     injection hbw with hbw;subst hbw
     have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
     rw [q43,← q42];exact this
    ·intro x
     have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a 1)) =
       decide (∃ u ∈ orIn n C (opnd C a 1),x u = true):=
      (z018 hL q01 hne lamList q1m q0s x _ hlw).2
     simp only [Option.some.injEq,exists_eq_left',hbp,decide_eq_true_eq,
      List.not_mem_nil,false_and,exists_false,or_false]
     have hno:¬ ∃ v' ∈ Zhas,topOf v' = a∧ x v' = true∧ ∃ u ∈ L v',x u = true:=by
      rintro ⟨v',hv',heq,_⟩;exact h ⟨v',hv',heq⟩
     rw [or_iff_left hno,hv]
     simp only [Finset.mem_singleton,exists_eq_left]
     rfl
   ·simp only [dif_neg h0]
    have h1:(side (n:=n) C a 1).card = 1:=hst.2.2.resolve_left h0
    set v:=Classical.choose (Finset.card_eq_one.mp h1)
    have hv:side (n:=n) C a 1 = {v}:=Classical.choose_spec (Finset.card_eq_one.mp h1)
    have hlw:=z086 hL hne q25 0 hst.1 (by simpa using h1)
    refine ⟨?_,rfl,?_⟩
    ·intro bw hbw
     injection hbw with hbw;subst hbw
     have:=(z018 hL q01 hne lamList q1m q0s (fun _=>false) _ hlw).1
     rw [q43,← q42];exact this
    ·intro x
     have hbp:wval ⟨gs1,0⟩ x (z016 n C lamList (opnd C a 0)) =
       decide (∃ u ∈ orIn n C (opnd C a 0),x u = true):=
      (z018 hL q01 hne lamList q1m q0s x _ hlw).2
     simp only [Option.some.injEq,exists_eq_left',hbp,decide_eq_true_eq,
      List.not_mem_nil,false_and,exists_false,or_false]
     have hno:¬ ∃ v' ∈ Zhas,topOf v' = a∧ x v' = true∧ ∃ u ∈ L v',x u = true:=by
      rintro ⟨v',hv',heq,_⟩;exact h ⟨v',hv',heq⟩
     rw [or_iff_left hno,hv]
     simp only [Finset.mem_singleton,exists_eq_left]
     exact and_comm
 have qdg:∀ it ∈ allItems,
   (∀ bw,it.2.1 = some bw→ bw < n + gs1.length)∧ (it.2.1.isSome∨ it.2.2 ≠ []):=by
  intro it hit
  simp only [allItems,topItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList] at hit
  rcases hit with ⟨a,ha,rfl⟩ | ⟨v,hv,rfl⟩
  ·have h:=q19 a ha
   exact ⟨h.1,Or.inl h.2.1⟩
  ·refine ⟨fun bw hbw=>(by cases hbw),Or.inr ?_⟩
   intro q0g
   simp only [List.map_eq_nil_iff] at q0g
   obtain ⟨u,hu⟩:=q8q v (Finset.mem_sdiff.mp hv).1
   have:u ∈ (L v).toList:=Finset.mem_toList.mpr hu
   rw [q0g] at this;cases this
 obtain ⟨⟨ex2,qb2⟩,qdd,q63,q8p,qj3,qde⟩:=z006 qda allItems qdg
 set gs2:=(z005 n gs1 allItems).1
 set topWires:=(z005 n gs1 allItems).2
 have q9j:allItems ≠ []:=by
  intro q0g
  have qgg:S_tops = ∅:=by
   have h1:topItems = []:=(List.append_eq_nil_iff.mp q0g).1
   simp only [topItems,List.map_eq_nil_iff] at h1
   ext a;simp only [Finset.notMem_empty,iff_false]
   intro ha;have:=Finset.mem_toList.mpr ha;rw [h1] at this;cases this
  have qgh:Zact \ Zhas = ∅:=by
   have h2:newItems = []:=(List.append_eq_nil_iff.mp q0g).2
   simp only [newItems,List.map_eq_nil_iff] at h2
   ext v;simp only [Finset.notMem_empty,iff_false]
   intro hv;have:=Finset.mem_toList.mpr hv;rw [h2] at this;cases this
  have q9k:Zhas = ∅:=by
   ext v;simp only [Finset.notMem_empty,iff_false]
   intro hv;have:=q41 v hv;rw [qgg] at this;exact Finset.notMem_empty _ this
  have q9l:Zact = ∅:=by
   rw [q9k,Finset.sdiff_empty] at qgh;exact qgh
  obtain ⟨u,v,huv⟩:=hne
  have qgi:s(u,v) ∈ G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr huv
  have qdh:starEdges G C = ∅:=by
   ext e;simp only [Finset.notMem_empty,iff_false,starEdges,Finset.mem_biUnion,
    Finset.mem_image,Finset.mem_product]
   rintro ⟨a,ha,⟨p,⟨hp0,hp1⟩,_⟩⟩
   have haS:a ∈ S_tops:=by
    rw [Finset.mem_sdiff];refine ⟨ha,fun hc=>?_⟩
    rw [centreless,Finset.mem_filter] at hc
    rcases hc.2 with h0 | h1
    ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
    ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
   rw [qgg] at haS;exact Finset.notMem_empty _ haS
  have q26:s(u,v) ∈ Ustar G C:=by unfold Ustar;rw [qdh,Finset.sdiff_empty];exact qgi
  obtain ⟨w,hw,_⟩:=qgf _ q26
  rw [q9l] at hw;exact Finset.notMem_empty _ hw
 have q9m:topWires ≠ []:=by
  intro h;rw [h] at q63;exact q9j (List.eq_nil_of_length_eq_zero q63.symm)
 obtain ⟨qj2,qpi⟩:=z009 q8p topWires q9m qj3
 let C':Circuit:=⟨(z008 n gs2 topWires).1,(z008 n gs2 topWires).2⟩
 have q4x:IsAO2 n C':=qj2
 have q6z:circuitFun n C' = graphFun G ∅:=by
  funext x
  change wval ⟨(z008 n gs2 topWires).1,0⟩ x (z008 n gs2 topWires).2 = graphFun G ∅ x
  rw [z012 q8p x topWires q9m qj3]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,qde x,z073]
  constructor
  ·rintro ⟨it,hit,hxv,qgj⟩
   simp only [allItems,topItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList] at hit
   rcases hit with ⟨a,ha,rfl⟩ | ⟨v,hv,rfl⟩
   ·have qdi:=(q19 a ha).2.2 x
    rcases qdi.mp ⟨hxv,qgj⟩ with ⟨⟨u0,hu0,qk6⟩,⟨u1,hu1,qk7⟩⟩ | ⟨v,hv,_,qk5,u,hu,hxu⟩
    ·exact ⟨u0,u1,z132 hL.1 (Finset.mem_sdiff.mp ha).1 hu0 hu1,qk6,qk7⟩
    ·exact ⟨v,u,qge v (q5d hv) u hu,qk5,hxu⟩
   ·rcases qgj with ⟨bw,hbw,_⟩ | ⟨u,hu,hxu⟩
    ·cases hbw
    ·rw [Finset.mem_toList] at hu
     exact ⟨v,u,qge v (Finset.mem_sdiff.mp hv).1 u hu,hxv,hxu⟩
  ·rintro ⟨u,v,huv,hxu,hxv⟩
   have he:s(u,v) ∈ G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr huv
   by_cases hst:s(u,v) ∈ starEdges G C
   ·simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product] at hst
    rcases hst with ⟨a,ha,⟨p0,p1⟩,⟨hp0,hp1⟩,qg0⟩
    have haS:a ∈ S_tops:=by
     rw [Finset.mem_sdiff];refine ⟨ha,fun hc=>?_⟩
     rw [centreless,Finset.mem_filter] at hc
     rcases hc.2 with h0 | h1
     ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
     ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
    refine ⟨mkTopItem a,?_,?_⟩
    ·simp only [allItems,topItems,List.mem_append,List.mem_map,Finset.mem_toList]
     exact Or.inl ⟨a,haS,rfl⟩
    ·apply ((q19 a haS).2.2 x).mpr
     left
     rw [Sym2.eq_iff] at qg0
     rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
     ·exact ⟨⟨p0,hp0,hxu⟩,⟨p1,hp1,hxv⟩⟩
     ·exact ⟨⟨p0,hp0,hxv⟩,⟨p1,hp1,hxu⟩⟩
   ·have q26:s(u,v) ∈ Ustar G C:=Finset.mem_sdiff.mpr ⟨he,hst⟩
    obtain ⟨w,hw,z,hz,heq⟩:=qgf _ q26
    rw [Sym2.eq_iff] at heq
    have hxw:x w = true:=by rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    have hxz:x z = true:=by rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
    by_cases hwh:w ∈ Zhas
    ·refine ⟨mkTopItem (topOf w),?_,?_⟩
     ·simp only [allItems,topItems,List.mem_append,List.mem_map,Finset.mem_toList]
      exact Or.inl ⟨topOf w,q41 w hwh,rfl⟩
     ·apply ((q19 (topOf w) (q41 w hwh)).2.2 x).mpr
      right
      exact ⟨w,hwh,rfl,hxw,z,hz,hxz⟩
    ·refine ⟨(w,none,(L w).toList),?_,hxw,Or.inr ⟨z,Finset.mem_toList.mpr hz,hxz⟩⟩
     simp only [allItems,newItems,List.mem_append,List.mem_map,Finset.mem_toList]
     exact Or.inr ⟨w,Finset.mem_sdiff.mpr ⟨hw,hwh⟩,rfl⟩
 have qb4:(topItems.map fun it=>it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
   (∑ v ∈ Zhas,(L v).card) + S_tops.card:=by
  have qo4:(topItems.map fun it=>it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
    ∑ a ∈ S_tops,((mkTopItem a).2.2.length + 1):=by
   simp only [topItems,List.map_map]
   rw [← Finset.sum_map_toList]
   congr 1
   apply List.map_congr_left
   intro a ha
   rw [Finset.mem_toList] at ha
   simp only [Function.comp_apply,(q19 a ha).2.1,↓reduceIte]
  rw [qo4,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one]
  congr 1
  have qc7:∑ a ∈ S_tops,(mkTopItem a).2.2.length =
    ∑ a ∈ S_tops,if h:∃ v ∈ Zhas,topOf v = a then (L (Classical.choose h)).card else 0:=by
   apply Finset.sum_congr rfl
   intro a ha
   by_cases h:∃ v ∈ Zhas,topOf v = a
   ·simp only [mkTopItem,dif_pos h,Finset.length_toList]
   ·simp only [mkTopItem,dif_neg h,dif_pos ha]
    split_ifs <;> rfl
  rw [qc7]
  have qb5:Zhas.image topOf ⊆ S_tops:=by
   intro a ha;simp only [Finset.mem_image] at ha;rcases ha with ⟨v,hv,rfl⟩;exact q41 v hv
  rw [← Finset.sum_subset qb5]
  ·rw [Finset.sum_image (fun v1 hv1 v2 hv2 heq=>q5e v1 hv1 v2 hv2 heq)]
   apply Finset.sum_congr rfl
   intro v hv
   have hex:∃ v' ∈ Zhas,topOf v' = topOf v:=⟨v,hv,rfl⟩
   rw [dif_pos hex]
   have hch:=Classical.choose_spec hex
   rw [q5e _ hch.1 v hv hch.2]
  ·intro a _ q8o
   rw [dif_neg]
   rintro ⟨v,hv,rfl⟩
   exact q8o (Finset.mem_image_of_mem topOf hv)
 have qb6:(newItems.map fun it=>it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
   ∑ v ∈ Zact \ Zhas,(L v).card:=by
  simp only [newItems,List.map_map]
  rw [← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro v _
  simp [Finset.length_toList]
 have qb7:(allItems.map fun it=>it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
   (∑ v ∈ Zact,(L v).card) + S_tops.card:=by
  simp only [allItems,List.map_append,List.sum_append,qb4,qb6]
  have qmi:∑ v ∈ Zact,(L v).card = (∑ v ∈ Zhas,(L v).card) + (∑ v ∈ Zact \ Zhas,(L v).card):=by
   rw [← Finset.sum_union Finset.disjoint_sdiff,Finset.union_sdiff_of_subset q5d]
  omega
 have q81:allItems.length = S_tops.card + (Zact \ Zhas).card:=by
  simp [allItems,topItems,newItems]
 have qj4:C'.size =
   (lam G C).card + (∑ v ∈ Zact,(L v).card) + 2 * S_tops.card + (Zact \ Zhas).card - 1:=by
  change (z008 n gs2 topWires).1.length = _
  rw [z010 n gs2 topWires q9m,q63,q81,qdd,q43,qb7]
  have qj5:0 < S_tops.card + (Zact \ Zhas).card:=by
   rw [← q81];exact List.length_pos_of_ne_nil q9j
  omega
 have qmj:C.size ≤ C'.size:=hL.2.2 C' q4x q6z
 have qo5:=z024 hL
 have q93:=z133 hL q01 hne
 have qg1:(junk G C).card = 2:=by
  have:junk G C = {g1,g2}:=by ext k;simp [q00]
  rw [this,Finset.card_pair qdf]
 have q65:centreless G C ⊆ tops G C:=Finset.filter_subset _ _
 have qdj:(tops G C).card = S_tops.card + (centreless G C).card:=by
  rw [z019 q65];have:=Finset.card_le_card q65;omega
 have q82:lam G C ⊆ orN G C:=Finset.filter_subset _ _
 have q8r:(orN G C).card = (lam G C).card + (orN G C \ lam G C).card:=by
  rw [z019 q82];have:=Finset.card_le_card q82;omega
 omega
lemma z106 {α:Type} [DecidableEq α] {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
  (Items:Finset α) (H:Finset ℕ) (hH:∀ k ∈ H,k < C.gates.length)
  (R:ℕ→ Finset α)
  (q83:∀ w < n + C.gates.length,(∀ k ∈ H,w ≠ n + k)→ (R w).card ≤ 1)
  (qdk:∀ k ∈ H,R (n + k) ⊆ R (opnd C k 0) ∪ R (opnd C k 1)):
  ∃ comp:α→ ℕ,
   Items.card ≤ (Items.image comp).card + H.card∧ 
   ∀ w < n + C.gates.length,∃ c:ℕ,∀ a ∈ R w,comp a = c:=by
 have qo6:∀ m ≤ C.gates.length,
   ∃ comp:α→ ℕ,
    Items.card ≤ (Items.image comp).card + (H.filter (· < m)).card∧ 
    ∀ w < n + m,∃ c:ℕ,∀ a ∈ R w,comp a = c:=by
  intro m
  induction m with
  | zero=>
   intro _
   refine ⟨fun a=>Items.toList.idxOf a,?_,?_⟩
   ·have qo7:Set.InjOn (fun a=>Items.toList.idxOf a) (Items:Set α):=by
     intro a ha b hb heq
     have ha':a ∈ Items.toList:=Finset.mem_toList.mpr ha
     have hb':b ∈ Items.toList:=Finset.mem_toList.mpr hb
     have hla:Items.toList.idxOf a < Items.toList.length:=List.idxOf_lt_length_iff.mpr ha'
     have hlb:Items.toList.idxOf b < Items.toList.length:=List.idxOf_lt_length_iff.mpr hb'
     have h1:=List.getElem_idxOf hla
     have h2:=List.getElem_idxOf hlb
     rw [← h1,← h2]
     simp [heq]
    rw [Finset.card_image_of_injOn qo7]
    simp
   ·intro w hw
    have hsm:(R w).card ≤ 1:=q83 w (by omega) (fun k _=>by omega)
    by_cases hne:(R w).Nonempty
    ·obtain ⟨a,ha⟩:=hne
     refine ⟨Items.toList.idxOf a,fun b hb=>?_⟩
     have hba:b = a:=by
      by_contra qay
      have hle:=Finset.card_le_card (show ({b,a}:Finset α) ⊆ R w by
       intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
       rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair qay] at hle;omega
     subst hba;rfl
    ·refine ⟨0,fun b hb=>absurd ⟨b,hb⟩ hne⟩
  | succ m ih=>
   intro hm
   obtain ⟨comp,q18,q2w⟩:=ih (by omega)
   by_cases hmH:m ∈ H
   ·have q9n:H.filter (· < m + 1) = insert m (H.filter (· < m)):=by
     ext k;simp only [Finset.mem_filter,Finset.mem_insert]
     constructor
     ·rintro ⟨hk,hlt⟩
      by_cases hkm:k = m
      ·exact Or.inl hkm
      ·exact Or.inr ⟨hk,by omega⟩
     ·rintro (rfl | ⟨hk,hlt⟩)
      ·exact ⟨hmH,by omega⟩
      ·exact ⟨hk,by omega⟩
    have qdl:m ∉ H.filter (· < m):=by simp
    obtain ⟨c0,hc0⟩:=q2w (opnd C m 0) (z104 hAO (by omega) 0)
    obtain ⟨c1,hc1⟩:=q2w (opnd C m 1) (z104 hAO (by omega) 1)
    let comp':α→ ℕ:=fun a=>if comp a = c1 then c0 else comp a
    refine ⟨comp',?_,?_⟩
    ·have qgk:Items.image comp ⊆ insert c1 (Items.image comp'):=by
      intro c hc
      simp only [Finset.mem_image] at hc
      rcases hc with ⟨a,ha,rfl⟩
      simp only [Finset.mem_insert,Finset.mem_image]
      by_cases h:comp a = c1
      ·exact Or.inl h
      ·exact Or.inr ⟨a,ha,by simp [comp',h]⟩
     have hle:=Finset.card_le_card qgk
     have qo8:=Finset.card_insert_le c1 (Items.image comp')
     rw [q9n,Finset.card_insert_of_notMem qdl]
     omega
    ·intro w hw
     by_cases hlt:w < n + m
     ·obtain ⟨c,hc⟩:=q2w w hlt
      refine ⟨if c = c1 then c0 else c,fun a ha=>?_⟩
      simp only [comp',hc a ha]
     ·have q8s:w = n + m:=by omega
      subst q8s
      refine ⟨c0,fun a ha=>?_⟩
      have q23:=qdk m hmH ha
      rw [Finset.mem_union] at q23
      rcases q23 with h0 | h1
      ·by_cases h:c0 = c1 <;> simp [comp',hc0 a h0,h]
      ·simp only [comp',hc1 a h1,↓reduceIte]
   ·have q9n:H.filter (· < m + 1) = H.filter (· < m):=by
     ext k;simp only [Finset.mem_filter]
     constructor
     ·rintro ⟨hk,hlt⟩;exact ⟨hk,by have:k ≠ m:=fun h=>hmH (h ▸ hk);omega⟩
     ·rintro ⟨hk,hlt⟩;exact ⟨hk,by omega⟩
    refine ⟨comp,by rw [q9n];exact q18,?_⟩
    intro w hw
    by_cases hlt:w < n + m
    ·exact q2w w hlt
    ·have q8s:w = n + m:=by omega
     subst q8s
     have hsm:(R (n + m)).card ≤ 1:=q83 (n + m) (by omega)
      (fun k hk heq=>hmH ((show m = k by omega) ▸ hk))
     by_cases hne:(R (n + m)).Nonempty
     ·obtain ⟨a,ha⟩:=hne
      refine ⟨comp a,fun b hb=>?_⟩
      have hba:b = a:=by
       by_contra qay
       have hle:=Finset.card_le_card (show ({b,a}:Finset α) ⊆ R (n + m) by
        intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
       rw [Finset.card_pair qay] at hle;omega
      subst hba;rfl
     ·refine ⟨0,fun b hb=>absurd ⟨b,hb⟩ hne⟩
 obtain ⟨comp,q18,q2w⟩:=qo6 C.gates.length (le_refl _)
 have q9n:H.filter (· < C.gates.length) = H:=
  Finset.filter_true_of_mem (fun k hk=>hH k hk)
 rw [q9n] at q18
 exact ⟨comp,q18,q2w⟩
lemma z101 {α:Type} [DecidableEq α] {Items S:Finset α} {comp:α→ ℕ} {Hcard:ℕ}
  (q18:Items.card ≤ (Items.image comp).card + Hcard)
  (q9o:S ⊆ Items) (qpj:S.Nonempty) (q2w:∃ c,∀ a ∈ S,comp a = c):
  S.card ≤ Hcard + 1:=by
 obtain ⟨c,hc⟩:=q2w
 have qgk:Items.image comp ⊆ insert c ((Items \ S).image comp):=by
  intro y hy
  simp only [Finset.mem_image] at hy
  rcases hy with ⟨a,ha,rfl⟩
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_sdiff]
  by_cases haS:a ∈ S
  ·exact Or.inl (hc a haS)
  ·exact Or.inr ⟨a,⟨ha,haS⟩,rfl⟩
 have h1:=Finset.card_le_card qgk
 have h2:=Finset.card_insert_le c ((Items \ S).image comp)
 have h3:((Items \ S).image comp).card ≤ (Items \ S).card:=Finset.card_image_le
 have h4:=z019 q9o
 have h5:=Finset.card_le_card q9o
 omega
lemma z134 {α:Type} [DecidableEq α] {Items S1 S2:Finset α} {comp:α→ ℕ}
  {Hcard:ℕ} (q18:Items.card ≤ (Items.image comp).card + Hcard)
  (q9o:S1 ∪ S2 ⊆ Items)
  (hm1:∃ c1,∀ a ∈ S1,comp a = c1) (hm2:∃ c2,∀ a ∈ S2,comp a = c2):
  (S1 ∪ S2).card ≤ Hcard + 2:=by
 obtain ⟨c1,hc1⟩:=hm1
 obtain ⟨c2,hc2⟩:=hm2
 have qgk:Items.image comp ⊆ insert c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp)):=by
  intro y hy
  simp only [Finset.mem_image] at hy
  rcases hy with ⟨a,ha,rfl⟩
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_sdiff,Finset.mem_union]
  by_cases ha1:a ∈ S1
  ·exact Or.inl (hc1 a ha1)
  ·by_cases ha2:a ∈ S2
   ·exact Or.inr (Or.inl (hc2 a ha2))
   ·exact Or.inr (Or.inr ⟨a,⟨ha,fun h=>h.elim ha1 ha2⟩,rfl⟩)
 have h1:=Finset.card_le_card qgk
 have h2:=Finset.card_insert_le c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp))
 have h3:=Finset.card_insert_le c2 ((Items \ (S1 ∪ S2)).image comp)
 have h4:((Items \ (S1 ∪ S2)).image comp).card ≤ (Items \ (S1 ∪ S2)).card:=Finset.card_image_le
 have h5:=z019 q9o
 have h6:=Finset.card_le_card q9o
 omega
def z000 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit)
  (g:ℕ) (Ci Di:Finset (Fin n)) (z zp:Fin n):Prop:=
 G.Adj z zp∧ z ∈ Ci∧ zp ∈ Di∧ (∀ c ∈ Ci,G.Adj c zp)∧ (∀ d ∈ Di,G.Adj d z)∧ 
  2 ≤ Ci.card∧ 2 ≤ Di.card∧ 
  ∀ x:Fin n→ Bool,gateVal n C g x = (decide (∃ c ∈ Ci,x c = true) && decide (∃ d ∈ Di,x d = true))
def z045 {n:ℕ} (Ci Di:Finset (Fin n)) (z zp:Fin n):Finset (Sym2 (Fin n)):=
 (Di.image fun d=>s(z,d)) ∪ (Ci.image fun c=>s(c,zp))
lemma z043 (b:Fin 2):b = 0∨ b = 1:=by
 fin_cases b <;> simp
lemma z044 {a b:Fin 2} (h:a ≠ b):1 - a = b:=by
 fin_cases a <;> fin_cases b <;> simp_all
lemma z015 {a b c:Bool} (h1:a ≠ c) (h2:b ≠ c):a = b:=by
 cases a <;> cases b <;> cases c <;> simp_all
lemma z046 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c:Fin n} (hc:c ∈ Ci):s c = s z:=by
 have h1:=q03 z zp hf.1
 have h2:=q03 c zp (hf.2.2.2.1 c hc)
 cases hz:s z <;> cases hzp:s zp <;> cases hsc:s c <;> simp_all
lemma z047 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {d:Fin n} (hd:d ∈ Di):s d = s zp:=by
 have h1:=q03 z zp hf.1
 have h2:=q03 d z (hf.2.2.2.2.1 d hd)
 cases hz:s z <;> cases hzp:s zp <;> cases hsd:s d <;> simp_all
lemma z048 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  Disjoint Ci Di:=by
 rw [Finset.disjoint_left]
 intro u huC huD
 have h1:=z046 q03 hf huC
 have h2:=z047 q03 hf huD
 exact q03 z zp hf.1 (h1.symm.trans h2)
lemma z051 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c d:Fin n} (hc:c ∈ Ci) (hcz:c ≠ z) (hd:d ∈ Di) (q1e:d ≠ zp):
  ¬ G.Adj c d:=by
 intro qk9
 exact q1e (z102 h4 hcz qk9 (hf.2.2.2.2.1 d hd).symm
  (hf.2.2.2.1 c hc) hf.1)
lemma z049 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  ∃ c ∈ Ci,c ≠ z:=by
 have hlt:1 < Ci.card:=by have:=hf.2.2.2.2.2.1;omega
 obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp hlt
 by_cases haz:a = z
 ·exact ⟨b,hb,fun hbz=>hab (haz.trans hbz.symm)⟩
 ·exact ⟨a,ha,haz⟩
lemma z050 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp):
  ∃ d ∈ Di,d ≠ zp:=by
 have hlt:1 < Di.card:=by have:=hf.2.2.2.2.2.2.1;omega
 obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp hlt
 by_cases haz:a = zp
 ·exact ⟨b,hb,fun hbz=>hab (haz.trans hbz.symm)⟩
 ·exact ⟨a,ha,haz⟩
lemma z052 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {u v:Fin n} (huv:G.Adj u v):
  gateVal n C g (pairInput u v) = true↔ s(u,v) ∈ z045 Ci Di z zp:=by
 have q4y:=z048 q03 hf
 rw [hf.2.2.2.2.2.2.2 (pairInput u v),Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
 simp only [pairInput,decide_eq_true_eq,z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff]
 constructor
 ·rintro ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
  ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q4y hd)
  ·subst hdv
   by_cases hcz:c = z
   ·subst hcz;exact Or.inl ⟨d,hd,Or.inl ⟨rfl,rfl⟩⟩
   ·by_cases q1e:d = zp
    ·subst q1e;exact Or.inr ⟨c,hc,Or.inl ⟨rfl,rfl⟩⟩
    ·exact absurd huv (z051 h4 hf hc hcz hd q1e)
  ·subst hdu
   by_cases hcz:c = z
   ·subst hcz;exact Or.inl ⟨d,hd,Or.inr ⟨rfl,rfl⟩⟩
   ·by_cases q1e:d = zp
    ·subst q1e;exact Or.inr ⟨c,hc,Or.inr ⟨rfl,rfl⟩⟩
    ·exact absurd huv.symm (z051 h4 hf hc hcz hd q1e)
  ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q4y hd)
 ·rintro (⟨d,hd,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
  ·exact ⟨⟨z,hf.2.1,Or.inl rfl⟩,⟨d,hd,Or.inr rfl⟩⟩
  ·exact ⟨⟨z,hf.2.1,Or.inr rfl⟩,⟨d,hd,Or.inl rfl⟩⟩
  ·exact ⟨⟨c,hc,Or.inl rfl⟩,⟨zp,hf.2.2.1,Or.inr rfl⟩⟩
  ·exact ⟨⟨c,hc,Or.inr rfl⟩,⟨zp,hf.2.2.1,Or.inl rfl⟩⟩
lemma z055 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {c:Fin n} (hc:c ∈ Ci) (hcz:c ≠ z):
  ¬ (∀ x:Fin n→ Bool,gateVal n C g x = true→ x c = true→ graphFun G ∅ x = true):=by
 intro hw
 obtain ⟨d,hd,q1e⟩:=z050 hf
 have q10:gateVal n C g (pairInput c d) = true:=by
  rw [hf.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
 have hF:=hw (pairInput c d) q10 (by simp [pairInput])
 exact z051 h4 hf hc hcz hd q1e ((z074 c d).mp hF)
lemma z056 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {d:Fin n} (hd:d ∈ Di) (q1e:d ≠ zp):
  ¬ (∀ x:Fin n→ Bool,gateVal n C g x = true→ x d = true→ graphFun G ∅ x = true):=by
 intro hw
 obtain ⟨c,hc,hcz⟩:=z049 hf
 have q10:gateVal n C g (pairInput c d) = true:=by
  rw [hf.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
 have hF:=hw (pairInput c d) q10 (by simp [pairInput])
 exact z051 h4 hf hc hcz hd q1e ((z074 c d).mp hF)
lemma z054 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {w:Fin n} (hw:∀ x:Fin n→ Bool,gateVal n C g x = true→ x w = true→ graphFun G ∅ x = true)
  (hsw:s w = s z) {d:Fin n} (hd:d ∈ Di) (q1e:d ≠ zp):G.Adj w d:=by
 obtain ⟨c,hc,hcz⟩:=z049 hf
 let x:Fin n→ Bool:=fun v=>decide (v = c∨ v = d∨ v = w)
 have hg:gateVal n C g x = true:=by
  rw [hf.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  exact ⟨⟨c,hc,by simp [x]⟩,⟨d,hd,by simp [x]⟩⟩
 have hF:=(z073 x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a,b,hab,ha,hb⟩
 simp only [x,decide_eq_true_eq] at ha hb
 have hsc:s c = s z:=z046 q03 hf hc
 have hsd:s d = s zp:=z047 q03 hf hd
 have qgl:¬ G.Adj c d:=z051 h4 hf hc hcz hd q1e
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab qgl
 ·exact absurd (hsc.trans hsw.symm) (q03 _ _ hab)
 ·exact absurd hab.symm qgl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact hab.symm
 ·exact absurd (hsw.trans hsc.symm) (q03 _ _ hab)
 ·exact hab
 ·exact absurd hab (G.loopless.irrefl _)
lemma z053 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  {g:ℕ} {Ci Di:Finset (Fin n)} {z zp:Fin n} (hf:z000 G C g Ci Di z zp)
  {w:Fin n} (hw:∀ x:Fin n→ Bool,gateVal n C g x = true→ x w = true→ graphFun G ∅ x = true)
  (hsw:s w = s zp) {c:Fin n} (hc:c ∈ Ci) (hcz:c ≠ z):G.Adj w c:=by
 obtain ⟨d,hd,q1e⟩:=z050 hf
 let x:Fin n→ Bool:=fun v=>decide (v = c∨ v = d∨ v = w)
 have hg:gateVal n C g x = true:=by
  rw [hf.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  exact ⟨⟨c,hc,by simp [x]⟩,⟨d,hd,by simp [x]⟩⟩
 have hF:=(z073 x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a,b,hab,ha,hb⟩
 simp only [x,decide_eq_true_eq] at ha hb
 have hsc:s c = s z:=z046 q03 hf hc
 have hsd:s d = s zp:=z047 q03 hf hd
 have qgl:¬ G.Adj c d:=z051 h4 hf hc hcz hd q1e
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab qgl
 ·exact hab.symm
 ·exact absurd hab.symm qgl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd (hsd.trans hsw.symm) (q03 _ _ hab)
 ·exact hab
 ·exact absurd (hsw.trans hsd.symm) (q03 _ _ hab)
 ·exact absurd hab (G.loopless.irrefl _)
lemma z130 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (hne:∃ u v:Fin n,G.Adj u v)
  {a:ℕ} (ha:a ∈ tops G C) (b:Fin 2):
  ∀ k,opnd C a b = n + k→ ¬ BelowF G C k:=by
 have ha':=z098.mp ha
 intro k hk hbk
 exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hk];exact hbk)
lemma z135 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2):
  Ustar G C ⊆ z045 C1 D1 z1 zp1 ∪ z045 C2 D2 z2 zp2:=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 intro e he
 rw [Ustar,Finset.mem_sdiff] at he
 rcases he with ⟨heG,q9p⟩
 induction e using Sym2.ind with
 | _ u v=>
  have huv:G.Adj u v:=SimpleGraph.mem_edgeFinset.mp heG
  have hcx:circuitFun n C (pairInput u v) = true:=by
   rw [congrFun hL.2.1 (pairInput u v)];exact (z074 u v).mpr huv
  obtain ⟨a,ha,hva⟩:=(z023 hL hne _).mp hcx
  have ha':=z098.mp ha
  rw [z070,z140 hL.1 _ ha'.1 ha'.2.1,Bool.and_eq_true] at hva
  have hw0:=(z103 hL q01 hne q00 (opnd C a 0)
   (by have:=z104 hL.1 ha'.1 0;omega) (z130 hL hne ha 0) (pairInput u v)).mp hva.1
  have hw1:=(z103 hL q01 hne q00 (opnd C a 1)
   (by have:=z104 hL.1 ha'.1 1;omega) (z130 hL hne ha 1) (pairInput u v)).mp hva.2
  have q5b:¬ ((∃ w ∈ side (n:=n) C a 0,pairInput u v w = true)∧ 
    (∃ w ∈ side (n:=n) C a 1,pairInput u v w = true)):=by
   rintro ⟨⟨w0,q95,qgm⟩,⟨w1,qgn,qgo⟩⟩
   apply q9p
   simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
   simp only [pairInput,decide_eq_true_eq] at qgm qgo
   have q52:w0 ≠ w1:=fun h=>by subst h;exact G.loopless.irrefl w0 (z132 hL.1 ha q95 qgn)
   refine ⟨a,ha,(w0,w1),⟨q95,qgn⟩,?_⟩
   rw [Sym2.eq_iff]
   rcases qgm with rfl | rfl <;> rcases qgo with rfl | rfl
   ·exact absurd rfl q52
   ·exact Or.inl ⟨rfl,rfl⟩
   ·exact Or.inr ⟨rfl,rfl⟩
   ·exact absurd rfl q52
  rw [Finset.mem_union,← z052 q03 h4 hf1 huv,← z052 q03 h4 hf2 huv]
  rcases hw0 with h0 | ⟨_,hg1⟩ | ⟨_,hg2⟩
  ·rcases hw1 with h1 | ⟨_,hg1⟩ | ⟨_,hg2⟩
   ·exact absurd ⟨h0,h1⟩ q5b
   ·exact Or.inl hg1
   ·exact Or.inr hg2
  ·exact Or.inl hg1
  ·exact Or.inr hg2
lemma z123 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {k:ℕ} (hk:k ∈ orN G C)
  (hn1:¬ OrReaches n C (n + k) g1) (hn2:¬ OrReaches n C (n + k) g2):
  2 ≤ (orIn n C (n + k)).card:=by
 have hk':=z096.mp hk
 have q10:∀ x,wval C x (n + k) = true↔ ∃ u ∈ orIn n C (n + k),x u = true:=by
  intro x
  have h:=z103 hL q01 hne q00 (n + k) (by omega)
   (fun m hm=>by have:m = k:=(by omega);subst this;exact hk'.2.2) x
  simpa [hn1,hn2] using h
 have qb8:(orIn n C (n + k)).Nonempty:=by
  have qaz:=(q10 (fun _=>true)).mp (z138 hL.1 (n + k) (by omega))
  rcases qaz with ⟨u,hu,_⟩;exact ⟨u,hu⟩
 by_contra hlt
 push Not at hlt
 have q0t:(orIn n C (n + k)).card = 1:=by
  have:=Finset.Nonempty.card_pos qb8;omega
 obtain ⟨u,hu⟩:=Finset.card_eq_one.mp q0t
 apply z090 hL hne hk'.1 (by omega:u.val < n + k)
 intro x
 apply Bool.eq_iff_iff.mpr
 rw [z144 C x u.val u.isLt,q10 x,hu]
 simp
lemma z084 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {k:ℕ} (hk:k ∈ lam G C) (qo9:k < g2):
  2 ≤ (orIn n C (n + k)).card:=by
 have q4c:=Finset.mem_filter.mp hk
 have q04:=z096.mp q4c.1
 have q6w:(orIn n C (opnd C k 0)).Nonempty:=q4c.2.1
 have q62:(orIn n C (opnd C k 1)).Nonempty:=q4c.2.2.1
 have q0o:=z108 hL.1 q04.1 q04.2.1
 have qka:(orIn n C (n + k)).Nonempty:=by
  rw [q0o];exact q6w.mono Finset.subset_union_left
 by_contra hlt
 push Not at hlt
 have q0t:(orIn n C (n + k)).card = 1:=by
  have:=Finset.Nonempty.card_pos qka;omega
 obtain ⟨u,hu⟩:=Finset.card_eq_one.mp q0t
 have qgp:orIn n C (opnd C k 0) ⊆ {u}:=by rw [← hu,q0o];exact Finset.subset_union_left
 have q3e:orIn n C (opnd C k 1) ⊆ {u}:=by rw [← hu,q0o];exact Finset.subset_union_right
 have qoa:orIn n C (opnd C k 0) = {u}:=by
  ext v;constructor
  ·exact fun h=>qgp h
  ·intro hv;rw [Finset.mem_singleton] at hv;subst hv
   obtain ⟨w,hw⟩:=q6w
   have:=Finset.mem_singleton.mp (qgp hw);subst this;exact hw
 have qob:orIn n C (opnd C k 1) = {u}:=by
  ext v;constructor
  ·exact fun h=>q3e h
  ·intro hv;rw [Finset.mem_singleton] at hv;subst hv
   obtain ⟨w,hw⟩:=q62
   have:=Finset.mem_singleton.mp (q3e hw);subst this;exact hw
 have qkb:¬ OrReaches n C (opnd C k 0) g2:=fun h=>by
  have h1:=z113 h;have h2:=z104 hL.1 q04.1 0;omega
 have qkc:¬ OrReaches n C (opnd C k 1) g2:=fun h=>by
  have h1:=z113 h;have h2:=z104 hL.1 q04.1 1;omega
 have hnb:∀ b:Fin 2,∀ m,opnd C k b = n + m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z091 hL q01 hne q04.1 q04.2.1 q04.2.2 b (by rw [hm];exact hbm)
 have hv0:∀ x,wval C x (opnd C k 0) = true↔ 
   x u = true∨ (OrReaches n C (opnd C k 0) g1∧ gateVal n C g1 x = true):=by
  intro x
  have h:=z103 hL q01 hne q00 (opnd C k 0)
   (by have:=z104 hL.1 q04.1 0;omega) (hnb 0) x
  simpa [qoa,qkb] using h
 have hv1:∀ x,wval C x (opnd C k 1) = true↔ 
   x u = true∨ (OrReaches n C (opnd C k 1) g1∧ gateVal n C g1 x = true):=by
  intro x
  have h:=z103 hL q01 hne q00 (opnd C k 1)
   (by have:=z104 hL.1 q04.1 1;omega) (hnb 1) x
  simpa [qob,qkc] using h
 by_cases hr0:OrReaches n C (opnd C k 0) g1
 ·apply z090 hL hne q04.1 (z104 hL.1 q04.1 0)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [z142 hL.1 x q04.1 q04.2.1,Bool.or_eq_true,hv0 x,hv1 x]
  simp [hr0]
  tauto
 ·apply z090 hL hne q04.1 (z104 hL.1 q04.1 1)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [z142 hL.1 x q04.1 q04.2.1,Bool.or_eq_true,hv0 x,hv1 x]
  simp [hr0]
lemma z085 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G)
  {v:Fin n} {k:ℕ} (hk:k ∈ lam G C)
  (q0c:∀ u ∈ orIn n C (n + k),G.Adj v u)
  (q18:2 ≤ (orIn n C (n + k)).card):
  ∀ u ∈ orIn n C (n + k),s(v,u) ∈ starEdges G C:=by
 have q4c:=Finset.mem_filter.mp hk
 rcases q4c.2.2.2 with ⟨a,ha,b,q0t,q0q⟩
 obtain ⟨v',hv'⟩:=Finset.card_eq_one.mp q0t
 have q66:orIn n C (n + k) ⊆ side (n:=n) C a b:=z109 q0q
 obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by omega:1 < (orIn n C (n + k)).card)
 have q9q:∀ u ∈ orIn n C (n + k),G.Adj v' u:=by
  intro u hu
  have qgq:v' ∈ side (n:=n) C a (1 - b):=by rw [hv'];simp
  have hum:u ∈ side (n:=n) C a b:=q66 hu
  fin_cases b
  ·exact (z132 hAO ha hum qgq).symm
  ·exact z132 hAO ha qgq hum
 have qoc:v = v':=z102 h4 qd2
  (q0c u1 hu1).symm (q0c u2 hu2).symm (q9q u1 hu1).symm (q9q u2 hu2).symm
 subst qoc
 intro u hu
 simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
 have qgq:v ∈ side (n:=n) C a (1 - b):=by rw [hv'];simp
 have hum:u ∈ side (n:=n) C a b:=q66 hu
 fin_cases b
 ·exact ⟨a,ha,(u,v),⟨hum,qgq⟩,Sym2.eq_swap⟩
 ·exact ⟨a,ha,(v,u),⟨qgq,hum⟩,rfl⟩
lemma z066 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1:Finset (Fin n)} {z1 zp1:Fin n} (hf1:z000 G C g1 C1 D1 z1 zp1):
  (¬ OrReaches n C (opnd C g1 0) g1∧ ¬ OrReaches n C (opnd C g1 0) g2∧ 
  ¬ OrReaches n C (opnd C g1 1) g1∧ ¬ OrReaches n C (opnd C g1 1) g2)∧ 
  ∃ b1:Fin 2,side (n:=n) C g1 b1 = C1∧ side (n:=n) C g1 (1 - b1) = D1:=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have q8t:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q80:=z104 hL.1 q8t.1 0
 have q58:=z104 hL.1 q8t.1 1
 have qmk:¬ OrReaches n C (opnd C g1 0) g1:=fun h=>by have:=h.1;have:=z113 h;omega
 have qgr:¬ OrReaches n C (opnd C g1 0) g2:=fun h=>by have:=h.1;have:=z113 h;omega
 have qml:¬ OrReaches n C (opnd C g1 1) g1:=fun h=>by have:=h.1;have:=z113 h;omega
 have qgs:¬ OrReaches n C (opnd C g1 1) g2:=fun h=>by have:=h.1;have:=z113 h;omega
 refine ⟨⟨qmk,qgr,qml,qgs⟩,?_⟩
 have hnb:∀ b:Fin 2,∀ m,opnd C g1 b = n + m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z089 hL hne q8t.1 q8t.2.1 b (by rw [hm];exact hbm)
 have q10:∀ x:Fin n→ Bool,
   ((∃ u ∈ side (n:=n) C g1 0,x u = true)∧ (∃ v ∈ side (n:=n) C g1 1,x v = true))↔ 
   ((∃ c ∈ C1,x c = true)∧ (∃ d ∈ D1,x d = true)):=by
  intro x
  have h0:=z103 hL q01 hne q00 (opnd C g1 0) (by omega) (hnb 0) x
  have h1:=z103 hL q01 hne q00 (opnd C g1 1) (by omega) (hnb 1) x
  have hg:=hf1.2.2.2.2.2.2.2 x
  rw [z070,z140 hL.1 x q8t.1 q8t.2.1] at hg
  have qdi:=congrArg (· = true) hg
  simp only [Bool.and_eq_true,decide_eq_true_eq] at qdi
  rw [← qdi,h0,h1]
  simp [qmk,qgr,qml,qgs,side]
 have q1a:=z048 q03 hf1
 have q27:Disjoint (side (n:=n) C g1 0) (side (n:=n) C g1 1):=by
  rw [Finset.disjoint_left];intro v hv0 hv1
  have h:=(q10 (fun w=>decide (w = v))).mp ⟨⟨v,hv0,by simp⟩,⟨v,hv1,by simp⟩⟩
  rcases h with ⟨⟨c,hc,hvc⟩,⟨d,hd,hvd⟩⟩
  simp only [decide_eq_true_eq] at hvc hvd
  subst hvc;subst hvd
  exact Finset.disjoint_left.mp q1a hc hd
 have q0u:∀ u v:Fin n,u ≠ v→ 
   (((u ∈ side (n:=n) C g1 0∧ v ∈ side (n:=n) C g1 1)∨ 
   (v ∈ side (n:=n) C g1 0∧ u ∈ side (n:=n) C g1 1))↔ 
   ((u ∈ C1∧ v ∈ D1)∨ (v ∈ C1∧ u ∈ D1))):=by
  intro u v huv
  have h:=q10 (pairInput u v)
  simp only [pairInput,decide_eq_true_eq] at h
  constructor
  ·intro hs
   have hcd:(∃ c ∈ C1,c = u∨ c = v)∧ (∃ d ∈ D1,d = u∨ d = v):=by
    apply h.mp
    rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩
    ·exact ⟨⟨u,hu,Or.inl rfl⟩,⟨v,hv,Or.inr rfl⟩⟩
    ·exact ⟨⟨v,hv,Or.inr rfl⟩,⟨u,hu,Or.inl rfl⟩⟩
   rcases hcd with ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
   ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q1a hd)
   ·subst hdv;exact Or.inl ⟨hc,hd⟩
   ·subst hdu;exact Or.inr ⟨hc,hd⟩
   ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q1a hd)
  ·intro hcd
   have hs:(∃ a ∈ side (n:=n) C g1 0,a = u∨ a = v)∧ 
     (∃ b ∈ side (n:=n) C g1 1,b = u∨ b = v):=by
    apply h.mpr
    rcases hcd with ⟨hu,hv⟩ | ⟨hv,hu⟩
    ·exact ⟨⟨u,hu,Or.inl rfl⟩,⟨v,hv,Or.inr rfl⟩⟩
    ·exact ⟨⟨v,hv,Or.inr rfl⟩,⟨u,hu,Or.inl rfl⟩⟩
   rcases hs with ⟨⟨a,ha,rfl | rfl⟩,⟨b,hb,hbu | hbv⟩⟩
   ·subst hbu;exact absurd ha (Finset.disjoint_right.mp q27 hb)
   ·subst hbv;exact Or.inl ⟨ha,hb⟩
   ·subst hbu;exact Or.inr ⟨ha,hb⟩
   ·subst hbv;exact absurd ha (Finset.disjoint_right.mp q27 hb)
 have qkd:z1 ≠ zp1:=G.ne_of_adj hf1.1
 have hzz:=(q0u z1 zp1 qkd).mpr (Or.inl ⟨hf1.2.1,hf1.2.2.1⟩)
 rcases hzz with ⟨hz0,qgt⟩ | ⟨qgu,hz1⟩
 ·refine ⟨0,?_,?_⟩
  ·ext u
   constructor
   ·intro hu
    have q70:u ≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hu qgt
    rcases (q0u u zp1 q70).mp (Or.inl ⟨hu,qgt⟩) with ⟨huC,_⟩ | ⟨qke,_⟩
    ·exact huC
    ·exact absurd qke (Finset.disjoint_right.mp q1a hf1.2.2.1)
   ·intro hu
    have q70:u ≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hu hf1.2.2.1
    rcases (q0u u zp1 q70).mpr (Or.inl ⟨hu,hf1.2.2.1⟩) with ⟨hu0,_⟩ | ⟨qgu,_⟩
    ·exact hu0
    ·exact absurd qgu (Finset.disjoint_right.mp q27 qgt)
  ·ext v
   simp only [sub_zero]
   constructor
   ·intro hv
    have q71:z1 ≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hz0 hv
    rcases (q0u z1 v q71).mp (Or.inl ⟨hz0,hv⟩) with ⟨_,hvD⟩ | ⟨_,hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp q1a hf1.2.1)
   ·intro hv
    have q71:z1 ≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hf1.2.1 hv
    rcases (q0u z1 v q71).mpr (Or.inl ⟨hf1.2.1,hv⟩) with ⟨_,hv1⟩ | ⟨_,hz1⟩
    ·exact hv1
    ·exact absurd hz1 (Finset.disjoint_left.mp q27 hz0)
 ·refine ⟨1,?_,?_⟩
  ·ext u
   constructor
   ·intro hu
    have q70:u ≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 qgu hu
    rcases (q0u u zp1 q70).mp (Or.inr ⟨qgu,hu⟩) with ⟨huC,_⟩ | ⟨qke,_⟩
    ·exact huC
    ·exact absurd qke (Finset.disjoint_right.mp q1a hf1.2.2.1)
   ·intro hu
    have q70:u ≠ zp1:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hu hf1.2.2.1
    rcases (q0u u zp1 q70).mpr (Or.inl ⟨hu,hf1.2.2.1⟩) with ⟨_,qgt⟩ | ⟨_,hu1⟩
    ·exact absurd qgt (Finset.disjoint_left.mp q27 qgu)
    ·exact hu1
  ·ext v
   have h11:(1:Fin 2) - 1 = 0:=rfl
   rw [h11]
   constructor
   ·intro hv
    have q71:z1 ≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q27 hv hz1
    rcases (q0u z1 v q71).mp (Or.inr ⟨hv,hz1⟩) with ⟨_,hvD⟩ | ⟨_,hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp q1a hf1.2.1)
   ·intro hv
    have q71:z1 ≠ v:=fun h=>by subst h;exact Finset.disjoint_left.mp q1a hf1.2.1 hv
    rcases (q0u z1 v q71).mpr (Or.inl ⟨hf1.2.1,hv⟩) with ⟨hz0,_⟩ | ⟨hv0,_⟩
    ·exact absurd hz0 (Finset.disjoint_right.mp q27 hz1)
    ·exact hv0
lemma z067 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2)
  (hsz:s z1 = s z2) (q1l:s zp1 = s zp2):
  ¬ OrReaches n C (opnd C g2 0) g2∧ ¬ OrReaches n C (opnd C g2 1) g2∧ 
  ∃ b2:Fin 2,
   side (n:=n) C g2 b2 ⊆ C2∧ side (n:=n) C g2 (1 - b2) ⊆ D2∧ 
   (OrReaches n C (opnd C g2 b2) g1→ C1 ⊆ C2∧ zp1 = zp2∧ C2 = C1 ∪ side (n:=n) C g2 b2)∧ 
   (¬ OrReaches n C (opnd C g2 b2) g1→ side (n:=n) C g2 b2 = C2)∧ 
   (OrReaches n C (opnd C g2 (1 - b2)) g1→ D1 ⊆ D2∧ z1 = z2∧ D2 = D1 ∪ side (n:=n) C g2 (1 - b2))∧ 
   (¬ OrReaches n C (opnd C g2 (1 - b2)) g1→ side (n:=n) C g2 (1 - b2) = D2):=by
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have q72:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q80:=z104 hL.1 q72.1 0
 have q58:=z104 hL.1 q72.1 1
 have qgr:¬ OrReaches n C (opnd C g2 0) g2:=fun h=>by have:=z113 h;omega
 have qgs:¬ OrReaches n C (opnd C g2 1) g2:=fun h=>by have:=z113 h;omega
 refine ⟨qgr,qgs,?_⟩
 have hnb:∀ b:Fin 2,∀ m,opnd C g2 b = n + m→ ¬ BelowF G C m:=fun b m hm hbm=>
  z089 hL hne q72.1 q72.2.1 b (by rw [hm];exact hbm)
 have q10:∀ x,
   (((∃ u ∈ side (n:=n) C g2 0,x u = true)∨ (OrReaches n C (opnd C g2 0) g1∧ gateVal n C g1 x = true))∧ 
   ((∃ v ∈ side (n:=n) C g2 1,x v = true)∨ (OrReaches n C (opnd C g2 1) g1∧ gateVal n C g1 x = true)))↔ 
   ((∃ c ∈ C2,x c = true)∧ (∃ d ∈ D2,x d = true)):=by
  intro x
  have h0:=z103 hL q01 hne q00 (opnd C g2 0) (by omega) (hnb 0) x
  have h1:=z103 hL q01 hne q00 (opnd C g2 1) (by omega) (hnb 1) x
  have hg:=hf2.2.2.2.2.2.2.2 x
  rw [z070,z140 hL.1 x q72.1 q72.2.1] at hg
  have qdi:=congrArg (· = true) hg
  simp only [Bool.and_eq_true,decide_eq_true_eq] at qdi
  rw [← qdi,h0,h1]
  simp [qgr,qgs,side]
 have q1n:=z048 q03 hf2
 have qc8:=z048 q03 hf1
 have q02:s z2 ≠ s zp2:=q03 z2 zp2 hf2.1
 have qgv:∀ b:Fin 2,OrReaches n C (opnd C g2 b) g1→ 
   (∃ d ∈ D2,d ∈ side (n:=n) C g2 (1 - b))→ C1 ⊆ C2:=by
  intro b hrb ⟨d2,hd2,qod⟩ c1 hc1
  let x:Fin n→ Bool:=fun v=>decide (v = c1∨ v = zp1∨ v = d2)
  have q1o:gateVal n C g1 x = true:=by
   rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
   exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
  have q1b:∃ v ∈ side (n:=n) C g2 (1 - b),x v = true:=⟨d2,qod,by simp [x]⟩
  have h2:(∃ c ∈ C2,x c = true)∧ (∃ d ∈ D2,x d = true):=by
   apply (q10 x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inl q1b⟩
   ·exact ⟨Or.inl q1b,Or.inr ⟨hrb,q1o⟩⟩
  rcases h2.1 with ⟨c,q4d,hxc⟩
  simp only [x,decide_eq_true_eq] at hxc
  have hsc:s c = s z2:=z046 q03 hf2 q4d
  rcases hxc with rfl | rfl | rfl
  ·exact q4d
  ·exact absurd (hsc.symm.trans q1l) q02
  ·exact absurd (hsc.symm.trans (z047 q03 hf2 hd2)) q02
 have qgw:∀ b:Fin 2,OrReaches n C (opnd C g2 b) g1→ 
   (∃ c ∈ C2,c ∈ side (n:=n) C g2 (1 - b))→ D1 ⊆ D2:=by
  intro b hrb ⟨c2,hc2,qoe⟩ d1 hd1
  let x:Fin n→ Bool:=fun v=>decide (v = z1∨ v = d1∨ v = c2)
  have q1o:gateVal n C g1 x = true:=by
   rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
   exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
  have q1b:∃ v ∈ side (n:=n) C g2 (1 - b),x v = true:=⟨c2,qoe,by simp [x]⟩
  have h2:(∃ c ∈ C2,x c = true)∧ (∃ d ∈ D2,x d = true):=by
   apply (q10 x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inl q1b⟩
   ·exact ⟨Or.inl q1b,Or.inr ⟨hrb,q1o⟩⟩
  rcases h2.2 with ⟨d,q4e,hxd⟩
  simp only [x,decide_eq_true_eq] at hxd
  have hsd:s d = s zp2:=z047 q03 hf2 q4e
  rcases hxd with rfl | rfl | rfl
  ·exact absurd (hsz.symm.trans hsd) q02
  ·exact q4e
  ·exact absurd ((z046 q03 hf2 hc2).symm.trans hsd) q02
 have qb9:C1 ⊆ C2→ zp1 = zp2:=by
  intro q0c
  obtain ⟨c,hc,hcz⟩:=z049 hf1
  exact z102 h4 hcz (hf1.2.2.2.1 c hc) hf1.1
   (hf2.2.2.2.1 c (q0c hc)) (hf2.2.2.2.1 z1 (q0c hf1.2.1))
 have qdm:D1 ⊆ D2→ z1 = z2:=by
  intro q0c
  obtain ⟨d,hd,q1e⟩:=z050 hf1
  exact z102 h4 q1e (hf1.2.2.2.2.1 d hd) hf1.1.symm
   (hf2.2.2.2.2.1 d (q0c hd)) (hf2.2.2.2.2.1 zp1 (q0c hf1.2.2.1))
 have q33:∀ b:Fin 2,side (n:=n) C g2 b = ∅→ OrReaches n C (opnd C g2 b) g1:=by
  intro b q0g
  by_contra hnr
  have h:=(q10 (fun _=>true)).mpr ⟨⟨z2,hf2.2.1,rfl⟩,⟨zp2,hf2.2.2.1,rfl⟩⟩
  fin_cases b
  ·dsimp at q0g hnr
   rcases h.1 with ⟨u,hu,_⟩ | ⟨hr,_⟩
   ·rw [q0g] at hu;exact Finset.notMem_empty _ hu
   ·exact hnr hr
  ·dsimp at q0g hnr
   rcases h.2 with ⟨u,hu,_⟩ | ⟨hr,_⟩
   ·rw [q0g] at hu;exact Finset.notMem_empty _ hu
   ·exact hnr hr
 have q27:Disjoint (side (n:=n) C g2 0) (side (n:=n) C g2 1):=by
  rw [Finset.disjoint_left];intro v hv0 hv1
  have h:=(q10 (fun w=>decide (w = v))).mp ⟨Or.inl ⟨v,hv0,by simp⟩,Or.inl ⟨v,hv1,by simp⟩⟩
  rcases h with ⟨⟨c,hc,hvc⟩,⟨d,hd,hvd⟩⟩
  simp only [decide_eq_true_eq] at hvc hvd;subst hvc;subst hvd
  exact Finset.disjoint_left.mp q1n hc hd
 have q67:∀ u ∈ side (n:=n) C g2 0,∀ v ∈ side (n:=n) C g2 1,
   (u ∈ C2∧ v ∈ D2)∨ (u ∈ D2∧ v ∈ C2):=by
  intro u hu v hv
  have h:=(q10 (pairInput u v)).mp
   ⟨Or.inl ⟨u,hu,by simp [pairInput]⟩,Or.inl ⟨v,hv,by simp [pairInput]⟩⟩
  simp only [pairInput,decide_eq_true_eq] at h
  rcases h with ⟨⟨c,hc,rfl | rfl⟩,⟨d,hd,hdu | hdv⟩⟩
  ·subst hdu;exact absurd hc (Finset.disjoint_right.mp q1n hd)
  ·subst hdv;exact Or.inl ⟨hc,hd⟩
  ·subst hdu;exact Or.inr ⟨hd,hc⟩
  ·subst hdv;exact absurd hc (Finset.disjoint_right.mp q1n hd)
 have q0i:∃ x,gateVal n C g1 x ≠ gateVal n C g2 x:=by
  by_contra qaz;push Not at qaz
  exact z090 hL hne q72.1 (by omega:n + g1 < n + g2) qaz
 have q8u:∃ b2:Fin 2,side (n:=n) C g2 b2 ⊆ C2∧ side (n:=n) C g2 (1 - b2) ⊆ D2:=by
  by_cases q6w:(side (n:=n) C g2 0).Nonempty
  ·by_cases q62:(side (n:=n) C g2 1).Nonempty
   ·obtain ⟨u0,hu0⟩:=q6w
    obtain ⟨v0,hv0⟩:=q62
    rcases q67 u0 hu0 v0 hv0 with ⟨qgx,qkf⟩ | ⟨qgy,qkg⟩
    ·refine ⟨0,?_,?_⟩
     ·intro u hu
      rcases q67 u hu v0 hv0 with ⟨huC,_⟩ | ⟨_,qkg⟩
      ·exact huC
      ·exact absurd qkg (Finset.disjoint_right.mp q1n qkf)
     ·intro v hv
      simp only [sub_zero] at hv
      rcases q67 u0 hu0 v hv with ⟨_,hvD⟩ | ⟨qgy,_⟩
      ·exact hvD
      ·exact absurd qgy (Finset.disjoint_left.mp q1n qgx)
    ·refine ⟨1,?_,?_⟩
     ·intro v hv
      rcases q67 u0 hu0 v hv with ⟨qgx,_⟩ | ⟨_,hvC⟩
      ·exact absurd qgx (Finset.disjoint_right.mp q1n qgy)
      ·exact hvC
     ·intro u hu
      have h11:(1:Fin 2) - 1 = 0:=rfl;rw [h11] at hu
      rcases q67 u hu v0 hv0 with ⟨_,qkf⟩ | ⟨huD,_⟩
      ·exact absurd qkf (Finset.disjoint_left.mp q1n qkg)
      ·exact huD
   ·have q5c:side (n:=n) C g2 1 = ∅:=Finset.not_nonempty_iff_eq_empty.mp q62
    have hr1:OrReaches n C (opnd C g2 1) g1:=q33 1 q5c
    have qdn:∀ x,gateVal n C g2 x = true→ gateVal n C g1 x = true:=by
     intro x hx
     have h:=(q10 x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx;simpa [Bool.and_eq_true,decide_eq_true_eq] using hx)
     rcases h.2 with ⟨v,hv,_⟩ | ⟨_,hg1⟩
     ·rw [q5c] at hv;exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have q1t:C2 ⊆ C1:=by
     intro c hc
     have h1:=qdn (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
     rcases h1.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,decide_eq_true_eq] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
    have q1u:D2 ⊆ D1:=by
     intro d hd
     have h1:=qdn (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,decide_eq_true_eq] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
    have q26:∀ u ∈ side (n:=n) C g2 0,(u ∈ C2∧ D1 ⊆ D2)∨ (u ∈ D2∧ C1 ⊆ C2):=by
     intro u hu
     by_cases hsu:s u = s z2
     ·left
      have hD:D1 ⊆ D2:=by
       intro d1 hd1
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = z1∨ w = d1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,decide_eq_true_eq] at hxd
       have hsd:=z047 q03 hf2 q4e
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) q02
       ·exact absurd (hsz.symm.trans hsd) q02
       ·exact q4e
      have qkh:u ∈ C2:=by
       have qdo:D1 = D2:=Finset.Subset.antisymm hD q1u
       have qdp:C1 ≠ C2:=by
        intro heq
        rcases q0i with ⟨x,hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,heq,qdo]
       have qdq:∃ c1 ∈ C1,c1 ∉ C2:=by
        by_contra hno;push Not at hno
        exact qdp (Finset.Subset.antisymm hno q1t)
       obtain ⟨c1,hc1,qki⟩:=qdq
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = c1∨ w = zp1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,decide_eq_true_eq] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact q4d
       ·exact absurd q4d qki
       ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
      exact ⟨qkh,hD⟩
     ·right
      have q24:s u = s zp2:=by cases hu':s u <;> cases hz':s z2 <;> cases qof:s zp2 <;> simp_all
      have hC:C1 ⊆ C2:=by
       intro c1 hc1
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = c1∨ w = zp1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,decide_eq_true_eq] at hxc
       have hsc:=z046 q03 hf2 q4d
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (q24.symm.trans hsc).symm q02
       ·exact q4d
       ·exact absurd (q1l.symm.trans hsc).symm q02
      have qkj:u ∈ D2:=by
       have qdr:C1 = C2:=Finset.Subset.antisymm hC q1t
       have qds:D1 ≠ D2:=by
        intro heq
        rcases q0i with ⟨x,hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,qdr,heq]
       have qdt:∃ d1 ∈ D1,d1 ∉ D2:=by
        by_contra hno;push Not at hno
        exact qds (Finset.Subset.antisymm hno q1u)
       obtain ⟨d1,hd1,qkk⟩:=qdt
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = z1∨ w = d1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inl ⟨u,hu,by simp [x]⟩,Or.inr ⟨hr1,q1o⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,decide_eq_true_eq] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact q4e
       ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
       ·exact absurd q4e qkk
      exact ⟨qkj,hC⟩
    obtain ⟨u0,hu0⟩:=q6w
    rcases q26 u0 hu0 with ⟨qgx,q73⟩ | ⟨qgy,q74⟩
    ·refine ⟨0,?_,by simp [q5c]⟩
     intro u hu
     rcases q26 u hu with ⟨huC,_⟩ | ⟨_,q74⟩
     ·exact huC
     ·exfalso
      have q75:C1 = C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1 = D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
    ·refine ⟨1,by simp [q5c],?_⟩
     have h11:(1:Fin 2) - 1 = 0:=rfl;rw [h11]
     intro u hu
     rcases q26 u hu with ⟨_,q73⟩ | ⟨huD,_⟩
     ·exfalso
      have q75:C1 = C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1 = D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
     ·exact huD
  ·have q50:side (n:=n) C g2 0 = ∅:=Finset.not_nonempty_iff_eq_empty.mp q6w
   have hr0:OrReaches n C (opnd C g2 0) g1:=q33 0 q50
   by_cases q62:(side (n:=n) C g2 1).Nonempty
   ·
    have qdn:∀ x,gateVal n C g2 x = true→ gateVal n C g1 x = true:=by
     intro x hx
     have h:=(q10 x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx;simpa [Bool.and_eq_true,decide_eq_true_eq] using hx)
     rcases h.1 with ⟨v,hv,_⟩ | ⟨_,hg1⟩
     ·rw [q50] at hv;exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have q1t:C2 ⊆ C1:=by
     intro c hc
     have h1:=qdn (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
     rcases h1.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,decide_eq_true_eq] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
    have q1u:D2 ⊆ D1:=by
     intro d hd
     have h1:=qdn (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,decide_eq_true_eq] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
    have q26:∀ u ∈ side (n:=n) C g2 1,(u ∈ C2∧ D1 ⊆ D2)∨ (u ∈ D2∧ C1 ⊆ C2):=by
     intro u hu
     by_cases hsu:s u = s z2
     ·left
      have hD:D1 ⊆ D2:=by
       intro d1 hd1
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = z1∨ w = d1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,decide_eq_true_eq] at hxd
       have hsd:=z047 q03 hf2 q4e
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) q02
       ·exact absurd (hsz.symm.trans hsd) q02
       ·exact q4e
      have qkh:u ∈ C2:=by
       have qdo:D1 = D2:=Finset.Subset.antisymm hD q1u
       have qdp:C1 ≠ C2:=by
        intro heq;rcases q0i with ⟨x,hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,heq,qdo])
       have qdq:∃ c1 ∈ C1,c1 ∉ C2:=by
        by_contra hno;push Not at hno;exact qdp (Finset.Subset.antisymm hno q1t)
       obtain ⟨c1,hc1,qki⟩:=qdq
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = c1∨ w = zp1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,decide_eq_true_eq] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact q4d
       ·exact absurd q4d qki
       ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
      exact ⟨qkh,hD⟩
     ·right
      have q24:s u = s zp2:=by cases hu':s u <;> cases hz':s z2 <;> cases qof:s zp2 <;> simp_all
      have hC:C1 ⊆ C2:=by
       intro c1 hc1
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = c1∨ w = zp1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨c1,hc1,by simp [x]⟩,⟨zp1,hf1.2.2.1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.1 with ⟨c,q4d,hxc⟩
       simp only [x,decide_eq_true_eq] at hxc
       have hsc:=z046 q03 hf2 q4d
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (q24.symm.trans hsc).symm q02
       ·exact q4d
       ·exact absurd (q1l.symm.trans hsc).symm q02
      have qkj:u ∈ D2:=by
       have qdr:C1 = C2:=Finset.Subset.antisymm hC q1t
       have qds:D1 ≠ D2:=by
        intro heq;rcases q0i with ⟨x,hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,qdr,heq])
       have qdt:∃ d1 ∈ D1,d1 ∉ D2:=by
        by_contra hno;push Not at hno;exact qds (Finset.Subset.antisymm hno q1u)
       obtain ⟨d1,hd1,qkk⟩:=qdt
       let x:Fin n→ Bool:=fun w=>decide (w = u∨ w = z1∨ w = d1)
       have q1o:gateVal n C g1 x = true:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
        exact ⟨⟨z1,hf1.2.1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
       have h2:=(q10 x).mp ⟨Or.inr ⟨hr0,q1o⟩,Or.inl ⟨u,hu,by simp [x]⟩⟩
       rcases h2.2 with ⟨d,q4e,hxd⟩
       simp only [x,decide_eq_true_eq] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact q4e
       ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
       ·exact absurd q4e qkk
      exact ⟨qkj,hC⟩
    obtain ⟨u0,hu0⟩:=q62
    rcases q26 u0 hu0 with ⟨qgx,q73⟩ | ⟨qgy,q74⟩
    ·refine ⟨1,?_,by simp [q50]⟩
     intro u hu
     rcases q26 u hu with ⟨huC,_⟩ | ⟨_,q74⟩
     ·exact huC
     ·exfalso
      have q75:C1 = C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1 = D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
    ·refine ⟨0,by simp [q50],?_⟩
     simp only [sub_zero]
     intro u hu
     rcases q26 u hu with ⟨_,q73⟩ | ⟨huD,_⟩
     ·exfalso
      have q75:C1 = C2:=Finset.Subset.antisymm q74 q1t
      have qba:D1 = D2:=Finset.Subset.antisymm q73 q1u
      rcases q0i with ⟨x,hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2,hf2.2.2.2.2.2.2.2,q75,qba])
     ·exact huD
   ·
    exfalso
    have q5c:side (n:=n) C g2 1 = ∅:=Finset.not_nonempty_iff_eq_empty.mp q62
    have hr1:OrReaches n C (opnd C g2 1) g1:=q33 1 q5c
    rcases q0i with ⟨x,hx⟩
    apply hx
    apply Bool.eq_iff_iff.mpr
    rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq,← q10 x]
    simp [q50,q5c,hr0,hr1]
 obtain ⟨b2,q68,q69⟩:=q8u
 refine ⟨b2,q68,q69,?_,?_,?_,?_⟩
 ·intro hrb
  have qkl:C1 ⊆ C2:=by
   by_cases qmm:(side (n:=n) C g2 (1 - b2)).Nonempty
   ·obtain ⟨d,hd⟩:=qmm
    exact qgv b2 hrb ⟨d,q69 hd,hd⟩
   ·have qkm:side (n:=n) C g2 (1 - b2) = ∅:=Finset.not_nonempty_iff_eq_empty.mp qmm
    have qg2:=q33 (1 - b2) qkm
    intro c1 hc1
    have h2:=(q10 (pairInput c1 zp1)).mp (by
     have q1o:gateVal n C g1 (pairInput c1 zp1) = true:=by
      rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨c1,hc1,by simp [pairInput]⟩,⟨zp1,hf1.2.2.1,by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inr ⟨qg2,q1o⟩⟩
     ·exact ⟨Or.inr ⟨qg2,q1o⟩,Or.inr ⟨hrb,q1o⟩⟩)
    rcases h2.1 with ⟨c,q4d,hxc⟩
    simp only [pairInput,decide_eq_true_eq] at hxc
    rcases hxc with rfl | rfl
    ·exact q4d
    ·exact absurd ((z046 q03 hf2 q4d).symm.trans q1l) q02
  refine ⟨qkl,qb9 qkl,?_⟩
  apply Finset.Subset.antisymm
  ·intro c hc
   rw [Finset.mem_union]
   by_cases hcS:c ∈ side (n:=n) C g2 b2
   ·exact Or.inr hcS
   ·left
    have h:=(q10 (pairInput c zp2)).mpr
     ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩
    have q3f:(∃ u ∈ side (n:=n) C g2 b2,pairInput c zp2 u = true)∨ 
      (OrReaches n C (opnd C g2 b2) g1∧ gateVal n C g1 (pairInput c zp2) = true):=by
     fin_cases b2
     ·exact h.1
     ·exact h.2
    rcases q3f with ⟨u,hu,hxu⟩ | ⟨_,q1o⟩
    ·simp only [pairInput,decide_eq_true_eq] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd hu hcS
     ·exact absurd (q68 hu) (Finset.disjoint_right.mp q1n hf2.2.2.1)
    ·rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at q1o
     rcases q1o.1 with ⟨c',hc',qc9⟩
     simp only [pairInput,decide_eq_true_eq] at qc9
     rcases qc9 with rfl | rfl
     ·exact hc'
     ·exact absurd ((z046 q03 hf1 hc').trans hsz).symm q02
  ·exact Finset.union_subset qkl q68
 ·intro qog
  apply Finset.Subset.antisymm q68
  intro c hc
  have h:=(q10 (pairInput c zp2)).mpr
   ⟨⟨c,hc,by simp [pairInput]⟩,⟨zp2,hf2.2.2.1,by simp [pairInput]⟩⟩
  have q3f:(∃ u ∈ side (n:=n) C g2 b2,pairInput c zp2 u = true)∨ 
    (OrReaches n C (opnd C g2 b2) g1∧ gateVal n C g1 (pairInput c zp2) = true):=by
   fin_cases b2
   ·exact h.1
   ·exact h.2
  rcases q3f with ⟨u,hu,hxu⟩ | ⟨hr,_⟩
  ·simp only [pairInput,decide_eq_true_eq] at hxu
   rcases hxu with rfl | rfl
   ·exact hu
   ·exact absurd (q68 hu) (Finset.disjoint_right.mp q1n hf2.2.2.1)
  ·exact absurd hr qog
 ·intro qg2
  have qkn:D1 ⊆ D2:=by
   by_cases qmn:(side (n:=n) C g2 b2).Nonempty
   ·obtain ⟨c,hc⟩:=qmn
    have q51:1 - (1 - b2) = b2:=by fin_cases b2 <;> rfl
    exact qgw (1 - b2) qg2 ⟨c,q68 hc,by rw [q51];exact hc⟩
   ·have qko:side (n:=n) C g2 b2 = ∅:=Finset.not_nonempty_iff_eq_empty.mp qmn
    have hrb:=q33 b2 qko
    intro d1 hd1
    have h2:=(q10 (pairInput z1 d1)).mp (by
     have q1o:gateVal n C g1 (pairInput z1 d1) = true:=by
      rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
      exact ⟨⟨z1,hf1.2.1,by simp [pairInput]⟩,⟨d1,hd1,by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb,q1o⟩,Or.inr ⟨qg2,q1o⟩⟩
     ·exact ⟨Or.inr ⟨qg2,q1o⟩,Or.inr ⟨hrb,q1o⟩⟩)
    rcases h2.2 with ⟨d,q4e,hxd⟩
    simp only [pairInput,decide_eq_true_eq] at hxd
    rcases hxd with rfl | rfl
    ·exact absurd (hsz.symm.trans (z047 q03 hf2 q4e)) q02
    ·exact q4e
  refine ⟨qkn,qdm qkn,?_⟩
  apply Finset.Subset.antisymm
  ·intro d hd
   rw [Finset.mem_union]
   by_cases hdS:d ∈ side (n:=n) C g2 (1 - b2)
   ·exact Or.inr hdS
   ·left
    have h:=(q10 (pairInput z2 d)).mpr
     ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
    have q3f:(∃ u ∈ side (n:=n) C g2 (1 - b2),pairInput z2 d u = true)∨ 
      (OrReaches n C (opnd C g2 (1 - b2)) g1∧ gateVal n C g1 (pairInput z2 d) = true):=by
     fin_cases b2
     ·exact h.2
     ·exact h.1
    rcases q3f with ⟨u,hu,hxu⟩ | ⟨_,q1o⟩
    ·simp only [pairInput,decide_eq_true_eq] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd (q69 hu) (Finset.disjoint_left.mp q1n hf2.2.1)
     ·exact absurd hu hdS
    ·rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at q1o
     rcases q1o.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,decide_eq_true_eq] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd ((z047 q03 hf1 hd').trans q1l) (hsz.symm ▸ q02)
     ·exact hd'
  ·exact Finset.union_subset qkn q69
 ·intro qkp
  apply Finset.Subset.antisymm q69
  intro d hd
  have h:=(q10 (pairInput z2 d)).mpr
   ⟨⟨z2,hf2.2.1,by simp [pairInput]⟩,⟨d,hd,by simp [pairInput]⟩⟩
  have q3f:(∃ u ∈ side (n:=n) C g2 (1 - b2),pairInput z2 d u = true)∨ 
    (OrReaches n C (opnd C g2 (1 - b2)) g1∧ gateVal n C g1 (pairInput z2 d) = true):=by
   fin_cases b2
   ·exact h.2
   ·exact h.1
  rcases q3f with ⟨u,hu,hxu⟩ | ⟨hr,_⟩
  ·simp only [pairInput,decide_eq_true_eq] at hxu
   rcases hxu with rfl | rfl
   ·exact absurd (q69 hu) (Finset.disjoint_left.mp q1n hf2.2.1)
   ·exact hu
  ·exact absurd hr qkp
def z039 {n:ℕ} (C:Circuit) (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n)):ℕ→ Finset (Option (Fin n))
 | w=>
  if hw:w < n then
   let u:Fin n:=⟨w,hw⟩
   if u ∈ M then {some u} else if u ∈ S then {none} else ∅
  else
   let k:=w - n
   if hk:k < C.gates.length then
    if k = g1 then {zItem}
    else if k ∈ lamSet then {none}
    else if k ∈ H then
     if h0:opnd C k 0 < w then
      if h1:opnd C k 1 < w then
       z039 C H lamSet g1 zItem M S (opnd C k 0) ∪ z039 C H lamSet g1 zItem M S (opnd C k 1)
      else ∅
     else ∅
    else ∅
   else ∅
termination_by w=>w
lemma z041 {n:ℕ} {C:Circuit} (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n))
  {w:ℕ} (q8o:∀ k ∈ H,w ≠ n + k):
  (z039 C H lamSet g1 zItem M S w).card ≤ 1:=by
 by_cases hw:w < n
 ·unfold z039;simp only [dif_pos hw];split_ifs <;> simp
 ·by_cases hkH:w - n ∈ H
  ·exact absurd (by omega:w = n + (w - n)) (q8o (w - n) hkH)
  ·unfold z039;simp only [dif_neg hw,hkH,↓reduceIte];split_ifs <;> simp
lemma z042 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (H lamSet:Finset ℕ) (g1:ℕ)
  (zItem:Option (Fin n)) (M S:Finset (Fin n))
  (q3g:∀ k ∈ H,k < C.gates.length)
  (q34:g1 ∉ H) (q1v:Disjoint H lamSet)
  {k:ℕ} (hk:k ∈ H):
  z039 C H lamSet g1 zItem M S (n + k) ⊆
   z039 C H lamSet g1 zItem M S (opnd C k 0) ∪ z039 C H lamSet g1 zItem M S (opnd C k 1):=by
 have q0d:=q3g k hk
 have q80:=z104 hAO q0d 0
 have q58:=z104 hAO q0d 1
 have qoh:k ≠ g1:=fun h=>q34 (h ▸ hk)
 have qkq:k ∉ lamSet:=Finset.disjoint_left.mp q1v hk
 conv_lhs=>unfold z039
 rw [dif_neg (by omega),Nat.add_sub_cancel_left,dif_pos q0d,if_neg qoh,if_neg qkq,
  if_pos hk,dif_pos q80,dif_pos q58]
lemma z040 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  (H:Finset ℕ) (v:Fin n) (zItem:Option (Fin n)) (M S:Finset (Fin n))
  (q8v:∀ u ∈ S,G.Adj v u)
  (qg3:∀ u ∈ M,s(v,u) ∈ Ustar G C)
  (q3g:∀ k ∈ H,k < C.gates.length)
  (q34:g1 ∉ H) (q1v:Disjoint H (lam G C)):
  ∀ w < n + g2,
   (∀ k,OrReaches n C w k→ k < C.gates.length∧ k ∈ orN G C ∪ {g1})→ 
   (∀ k,OrReaches n C w k→ k ∈ orN G C \ lam G C→ k ∈ H)→ 
   orIn n C w ⊆ S→ 
   (∀ u ∈ orIn n C w,u ∈ M→ some u ∈ z039 C H (lam G C) g1 zItem M S w)∧ 
   (∀ u ∈ orIn n C w,u ∉ M→ none ∈ z039 C H (lam G C) g1 zItem M S w)∧ 
   (OrReaches n C w g1→ zItem ∈ z039 C H (lam G C) g1 zItem M S w∨ 
    none ∈ z039 C H (lam G C) g1 zItem M S w):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro q53 q28 q5f q35
  by_cases hwn:w < n
  ·refine ⟨?_,?_,fun hr=>absurd hr (z112 hwn)⟩
   ·intro u hu huM
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    subst heq;unfold z039;rw [dif_pos hwn,if_pos huM];simp
   ·intro u hu huM
    have heq:=(z095 C u ⟨w,hwn⟩).mp hu
    have huS:=q35 hu
    subst heq;unfold z039;rw [dif_pos hwn,if_neg huM,if_pos huS];simp
  ·have q0d:w - n < C.gates.length:=by
    have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl));omega
   have q0f:w = n + (w - n):=by omega
   set k:=w - n
   have qgz:OrReaches n C w k:=by rw [q0f];exact z115 q0d
   have q3w:=(q28 k qgz).2
   rw [Finset.mem_union,Finset.mem_singleton] at q3w
   rcases q3w with q04 | rfl
   ·have qkr:k ≠ g1:=by
     intro h;subst h
     have h1:=(z096.mp q04).2.1
     have h2:=(z094.mp ((q00 k).mpr (Or.inl rfl))).2.1
     rw [h1] at h2;cases h2
    by_cases q6a:k ∈ lam G C
    ·have qh0:2 ≤ (orIn n C (n + k)).card:=
      z084 hL q01 hne q00 q6a (by omega)
     have q5g:=z085 hL.1 h4 q6a
      (fun u hu=>q8v u (q35 (by rwa [q0f]))) qh0
     have q4f:z039 C H (lam G C) g1 zItem M S w = {none}:=by
      unfold z039;rw [dif_neg hwn,dif_pos q0d,if_neg qkr,if_pos q6a]
     rw [q4f]
     refine ⟨?_,fun _ _ _=>Finset.mem_singleton_self none,fun _=>Or.inr (Finset.mem_singleton_self none)⟩
     intro u hu huM
     exfalso
     have h1:=q5g u (by rwa [← q0f])
     have h2:=(Finset.mem_sdiff.mp (qg3 u huM)).2
     exact h2 h1
    ·have qoi:k ∈ H:=q5f k qgz (Finset.mem_sdiff.mpr ⟨q04,q6a⟩)
     have hk':=z096.mp q04
     have q80:opnd C k 0 < w:=by have:=z104 hL.1 hk'.1 0;omega
     have q58:opnd C k 1 < w:=by have:=z104 hL.1 hk'.1 1;omega
     have q4f:z039 C H (lam G C) g1 zItem M S w =
       z039 C H (lam G C) g1 zItem M S (opnd C k 0) ∪
       z039 C H (lam G C) g1 zItem M S (opnd C k 1):=by
      conv_lhs=>unfold z039
      rw [dif_neg hwn,dif_pos q0d,if_neg qkr,if_neg q6a,if_pos qoi,
       dif_pos q80,dif_pos q58]
     have q2m:∀ b:Fin 2,∀ m,OrReaches n C (opnd C k b) m→ OrReaches n C w m:=by
      intro b m hrm
      rw [q0f,z111 hk'.1]
      exact Or.inr ⟨hk'.2.1,opnd C k b,z105 hL.1 hk'.1 b,hrm.1,z104 hL.1 hk'.1 b,hrm⟩
     have q0o:orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1):=by
      rw [q0f];exact z108 hL.1 hk'.1 hk'.2.1
     have ih0:=ih (opnd C k 0) q80 (by omega)
      (fun m hm=>q28 m (q2m 0 m hm))
      (fun m hm=>q5f m (q2m 0 m hm))
      (fun u hu=>q35 (by rw [q0o];exact Finset.mem_union_left _ hu))
     have ih1:=ih (opnd C k 1) q58 (by omega)
      (fun m hm=>q28 m (q2m 1 m hm))
      (fun m hm=>q5f m (q2m 1 m hm))
      (fun u hu=>q35 (by rw [q0o];exact Finset.mem_union_right _ hu))
     rw [q4f]
     refine ⟨?_,?_,?_⟩
     ·intro u hu huM
      rw [q0o,Finset.mem_union] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.1 u h1 huM)
     ·intro u hu huM
      rw [q0o,Finset.mem_union] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.2.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.2.1 u h1 huM)
     ·intro hr
      rw [q0f,z111 hk'.1] at hr
      rcases hr with heq | ⟨_,u,hu,_,_,qmo⟩
      ·exact absurd heq.symm qkr
      ·rw [z071 hL.1 hk'.1] at hu
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
       rcases hu with rfl | rfl
       ·exact (ih0.2.2 qmo).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
       ·exact (ih1.2.2 qmo).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
   ·have q4f:z039 C H (lam G C) k zItem M S w = {zItem}:=by
     unfold z039;rw [dif_neg hwn,dif_pos q0d,if_pos rfl]
    have q5x:=z094.mp ((q00 k).mpr (Or.inl rfl))
    have q0g:orIn n C w = ∅:=by rw [q0f];exact z107 (n:=n) q0d q5x.2.1
    rw [q4f,q0g]
    exact ⟨by simp,by simp,fun _=>Or.inl (Finset.mem_singleton_self zItem)⟩
lemma z125 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {w:ℕ} (q53:w < n + g2)
  (q76:∀ k,w = n + k→ ¬ BelowF G C k)
  (hn1:¬ OrReaches n C w g1)
  {v:Fin n} {S:Finset (Fin n)} (hS:orIn n C w = S) (q8v:∀ u ∈ S,G.Adj v u):
  let M:=S.filter (fun u=>s(v,u) ∈ Ustar G C)
  let H:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w k)
  (M.Nonempty→ M.card ≤ H.card + 1)∧ 
  ((∃ r ∈ S,r ∉ M)→ M.card ≤ H.card):=by
 intro M H
 have q3g:∀ k ∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have q34:g1 ∉ H:=fun hg=>by
  have h1:=(z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).1).2.1
  have h2:=(z094.mp ((q00 g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2;cases h2
 have q1v:Disjoint H (lam G C):=by
  rw [Finset.disjoint_left];intro k hk hkl
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 hkl
 have q28:∀ k,OrReaches n C w k→ k < C.gates.length∧ k ∈ orN G C ∪ {g1}:=by
  intro k hk
  have qks:k ≤ w - n:=z113 hk
  have q0d:k < C.gates.length:=by
   have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl));omega
  refine ⟨q0d,?_⟩
  have q5w:¬ BelowF G C k:=by
   intro hbk
   by_cases hwn:w < n
   ·exact z112 hwn hk
   ·have q0f:w = n + (w - n):=by omega
    have q10:=z117 hL.1
    have q9r:∀ u < n + C.gates.length,(∀ m,u = n + m→ ¬ BelowF G C m)→ 
      OrReaches n C u k→ False:=by
     intro u
     induction u using Nat.strong_induction_on with
     | ind u ihu=>
      intro qkt q77 qdu
      by_cases hun:u < n
      ·exact z112 hun qdu
      ·have q36:u - n < C.gates.length:=by omega
       have q1d:u = n + (u - n):=by omega
       rw [q1d,z111 q36] at qdu
       rcases qdu with rfl | ⟨qaw,x,hx,hnx,qoj,qku⟩
       ·exact q77 (u - n) q1d hbk
       ·rw [z071 hL.1 q36] at hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        have qkv:∀ m,x = n + m→ ¬ BelowF G C m:=by
         intro m hm hbm
         rcases hx with rfl | rfl
         ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 0 (by rw [hm];exact hbm)
         ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 1 (by rw [hm];exact hbm)
        exact ihu x (by omega) (by omega) qkv qku
    have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
    exact q9r w (by omega) q76 hk
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·have hkj:k ∈ junk G C:=z094.mpr ⟨q0d,q17,q5w⟩
   rw [q00] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have:=hk.1;omega
  ·exact Finset.mem_union_left _ (z096.mpr ⟨q0d,hor,q5w⟩)
 have qg3:∀ u ∈ M,s(v,u) ∈ Ustar G C:=fun u hu=>(Finset.mem_filter.mp hu).2
 have qca:=z040 hL q01 h4 hne q00 H v none M S q8v qg3 q3g q34 q1v
  w q53 q28 (fun k hk hkd=>Finset.mem_filter.mpr ⟨hkd,hk⟩) (by rw [hS])
 let Items:Finset (Option (Fin n)):=insert none (M.image some)
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 Items H q3g
  (z039 C H (lam G C) g1 none M S)
  (fun u _ q8o=>z041 H (lam G C) g1 none M S q8o)
  (fun k hk=>z042 hL.1 H (lam G C) g1 none M S q3g q34 q1v hk)
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 obtain ⟨c,hc⟩:=q2w w (by omega)
 have q84:M.image some ⊆ z039 C H (lam G C) g1 none M S w:=by
  intro y hy;simp only [Finset.mem_image] at hy;rcases hy with ⟨u,hu,rfl⟩
  exact qca.1 u (by rw [hS];exact (Finset.mem_filter.mp hu).1) hu
 have q78:(M.image some).card = M.card:=Finset.card_image_of_injective M (Option.some_injective (Fin n))
 constructor
 ·intro qkw
  have hle:=z101 q18 (Finset.subset_insert none (M.image some))
   (qkw.image some) ⟨c,fun a ha=>hc a (q84 ha)⟩
  omega
 ·rintro ⟨r,hrS,qj6⟩
  have qdv:none ∈ z039 C H (lam G C) g1 none M S w:=qca.2.1 r (by rw [hS];exact hrS) qj6
  have q1p:Items ⊆ z039 C H (lam G C) g1 none M S w:=by
   intro a ha;simp only [Items,Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact qdv
   ·exact q84 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c,fun a ha=>hc a (q1p ha)⟩
  have q3h:none ∉ M.image some:=by simp
  have q79:Items.card = M.card + 1:=by
   simp only [Items,Finset.card_insert_of_notMem q3h,q78]
  omega
lemma z099 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (h4:NoFourCycle G)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {w1 w2:ℕ} (qcb:w1 < n + g2) (qcc:w2 < n + g2)
  (qh1:∀ k,w1 = n + k→ ¬ BelowF G C k) (qh2:∀ k,w2 = n + k→ ¬ BelowF G C k)
  {v:Fin n} {S1 S2:Finset (Fin n)}
  (hS1:orIn n C w1 = S1) (qdw:orIn n C w2 ⊆ S2)
  (qcd:S1 ∪ S2 = S1 ∪ orIn n C w2)
  (q8v:∀ u ∈ S1 ∪ S2,G.Adj v u)
  {z0:Fin n} (qh3:z0 ∈ S1)
  (qh4:z0 ∈ orIn n C w2∨ OrReaches n C w2 g1):
  let S:=S1 ∪ S2
  let M:=S.filter (fun u=>s(v,u) ∈ Ustar G C)
  let H:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1 k∨ OrReaches n C w2 k)
  (M.Nonempty→ M.card ≤ H.card + 1)∧ 
  (z0 ∉ M→ M.card ≤ H.card)∧ 
  (¬ OrReaches n C w2 g1→ (∃ r ∈ S,r ∉ M)→ M.card ≤ H.card):=by
 intro S M H
 have q3g:∀ k ∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have q34:g1 ∉ H:=fun hg=>by
  have h1:=(z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).1).2.1
  have h2:=(z094.mp ((q00 g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2;cases h2
 have q1v:Disjoint H (lam G C):=by
  rw [Finset.disjoint_left];intro k hk hkl
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 hkl
 have q37:∀ w < n + g2,(∀ k,w = n + k→ ¬ BelowF G C k)→ 
   ∀ k,OrReaches n C w k→ k < C.gates.length∧ k ∈ orN G C ∪ {g1}:=by
  intro w q53 q76 k hk
  have qks:k ≤ w - n:=z113 hk
  have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
  have q0d:k < C.gates.length:=by omega
  refine ⟨q0d,?_⟩
  have q5w:¬ BelowF G C k:=by
   intro hbk
   have q9r:∀ u < n + C.gates.length,(∀ m,u = n + m→ ¬ BelowF G C m)→ 
     OrReaches n C u k→ False:=by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ihu=>
     intro qkt q77 qdu
     by_cases hun:u < n
     ·exact z112 hun qdu
     ·have q36:u - n < C.gates.length:=by omega
      have q1d:u = n + (u - n):=by omega
      rw [q1d,z111 q36] at qdu
      rcases qdu with rfl | ⟨qaw,x,hx,hnx,qoj,qku⟩
      ·exact q77 (u - n) q1d hbk
      ·rw [z071 hL.1 q36] at hx
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
       have qkv:∀ m,x = n + m→ ¬ BelowF G C m:=by
        intro m hm hbm
        rcases hx with rfl | rfl
        ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 0 (by rw [hm];exact hbm)
        ·exact z091 hL q01 hne q36 qaw (q77 _ q1d) 1 (by rw [hm];exact hbm)
       exact ihu x (by omega) (by omega) qkv qku
   exact q9r w (by omega) q76 hk
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·have hkj:k ∈ junk G C:=z094.mpr ⟨q0d,q17,q5w⟩
   rw [q00] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have:=hk.1;omega
  ·exact Finset.mem_union_left _ (z096.mpr ⟨q0d,hor,q5w⟩)
 let zItem:Option (Fin n):=if z0 ∈ M then some z0 else none
 have qg3:∀ u ∈ M,s(v,u) ∈ Ustar G C:=fun u hu=>(Finset.mem_filter.mp hu).2
 have hp1:=z040 hL q01 h4 hne q00 H v zItem M S q8v qg3 q3g q34 q1v
  w1 qcb (q37 w1 qcb qh1) (fun k hk hkd=>Finset.mem_filter.mpr ⟨hkd,Or.inl hk⟩)
  (by rw [hS1];exact Finset.subset_union_left)
 have hp2:=z040 hL q01 h4 hne q00 H v zItem M S q8v qg3 q3g q34 q1v
  w2 qcc (q37 w2 qcc qh2) (fun k hk hkd=>Finset.mem_filter.mpr ⟨hkd,Or.inr hk⟩)
  (Finset.Subset.trans qdw Finset.subset_union_right)
 let Items:Finset (Option (Fin n)):=insert none (M.image some)
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 Items H q3g
  (z039 C H (lam G C) g1 zItem M S)
  (fun u _ q8o=>z041 H (lam G C) g1 zItem M S q8o)
  (fun k hk=>z042 hL.1 H (lam G C) g1 zItem M S q3g q34 q1v hk)
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 obtain ⟨c1,hc1⟩:=q2w w1 (by omega)
 obtain ⟨c2,hc2⟩:=q2w w2 (by omega)
 set R1:=z039 C H (lam G C) g1 zItem M S w1
 set R2:=z039 C H (lam G C) g1 zItem M S w2
 have q85:M.image some ⊆ R1 ∪ R2:=by
  intro y hy;simp only [Finset.mem_image] at hy;rcases hy with ⟨u,hu,rfl⟩
  have huS:u ∈ S1 ∪ orIn n C w2:=by rw [← qcd];exact (Finset.mem_filter.mp hu).1
  rw [Finset.mem_union] at huS
  rcases huS with h1 | h2
  ·exact Finset.mem_union_left _ (hp1.1 u (by rw [hS1];exact h1) hu)
  ·exact Finset.mem_union_right _ (hp2.1 u h2 hu)
 have q6b:zItem ∈ R1:=by
  by_cases hzM:z0 ∈ M
  ·simp only [zItem,if_pos hzM];exact hp1.1 z0 (by rw [hS1];exact qh3) hzM
  ·simp only [zItem,if_neg hzM];exact hp1.2.1 z0 (by rw [hS1];exact qh3) hzM
 have q1q:zItem ∈ R2∨ none ∈ R2:=by
  rcases qh4 with hz2 | hr2
  ·left
   by_cases hzM:z0 ∈ M
   ·simp only [zItem,if_pos hzM];exact hp2.1 z0 hz2 hzM
   ·simp only [zItem,if_neg hzM];exact hp2.2.1 z0 hz2 hzM
  ·exact hp2.2.2 hr2
 have q78:(M.image some).card = M.card:=Finset.card_image_of_injective M (Option.some_injective (Fin n))
 have q3h:none ∉ M.image some:=by simp
 have q79:Items.card = M.card + 1:=by
  simp only [Items,Finset.card_insert_of_notMem q3h,q78]
 refine ⟨?_,?_,?_⟩
 ·intro qkw
  rcases q1q with qkx | qdx
  ·have qh5:c1 = c2:=(hc1 zItem q6b).symm.trans (hc2 zItem qkx)
   have hle:=z101 q18 (Finset.subset_insert none (M.image some))
    (qkw.image some) ⟨c1,fun a ha=>by
     rcases Finset.mem_union.mp (q85 ha) with h1 | h2
     ·exact hc1 a h1
     ·rw [qh5];exact hc2 a h2⟩
   omega
  ·have q8w:Items ⊆ (R1 ∩ Items) ∪ (R2 ∩ Items):=by
    intro a ha
    simp only [Finset.mem_union,Finset.mem_inter]
    by_cases q9s:a = none
    ·subst q9s;exact Or.inr ⟨qdx,ha⟩
    ·have haM:a ∈ M.image some:=by
      simp only [Items,Finset.mem_insert] at ha;exact ha.resolve_left q9s
     rcases Finset.mem_union.mp (q85 haM) with h1 | h2
     ·exact Or.inl ⟨h1,ha⟩
     ·exact Or.inr ⟨h2,ha⟩
   have hle:=z134 q18
    (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    ⟨c1,fun a ha=>hc1 a (Finset.mem_inter.mp ha).1⟩
    ⟨c2,fun a ha=>hc2 a (Finset.mem_inter.mp ha).1⟩
   have qok:=Finset.card_le_card q8w
   omega
 ·intro qh6
  have q6c:zItem = none:=by simp [zItem,qh6]
  have q86:none ∈ R1:=by rwa [← q6c]
  have qbb:none ∈ R2:=by
   rcases q1q with h | h
   ·rwa [q6c] at h
   ·exact h
  have qh5:c1 = c2:=(hc1 none q86).symm.trans (hc2 none qbb)
  have q1p:Items ⊆ R1 ∪ R2:=by
   intro a ha;simp only [Items,Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact Finset.mem_union_left _ q86
   ·exact q85 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c1,fun a ha=>by
    rcases Finset.mem_union.mp (q1p ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [qh5];exact hc2 a h2⟩
  omega
 ·intro qol ⟨r,hrS,qj6⟩
  have hz2:z0 ∈ orIn n C w2:=qh4.resolve_right qol
  have qkx:zItem ∈ R2:=by
   by_cases hzM:z0 ∈ M
   ·simp only [zItem,if_pos hzM];exact hp2.1 z0 hz2 hzM
   ·simp only [zItem,if_neg hzM];exact hp2.2.1 z0 hz2 hzM
  have qh5:c1 = c2:=(hc1 zItem q6b).symm.trans (hc2 zItem qkx)
  have qdy:none ∈ R1 ∪ R2:=by
   have hr':r ∈ S1 ∪ orIn n C w2:=by rwa [← qcd]
   rcases Finset.mem_union.mp hr' with h1 | h2
   ·exact Finset.mem_union_left _ (hp1.2.1 r (by rw [hS1];exact h1) qj6)
   ·exact Finset.mem_union_right _ (hp2.2.1 r h2 qj6)
  have q1p:Items ⊆ R1 ∪ R2:=by
   intro a ha;simp only [Items,Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact qdy
   ·exact q85 ha
  have hle:=z101 q18 (Finset.Subset.refl Items) ⟨none,Finset.mem_insert_self _ _⟩
   ⟨c1,fun a ha=>by
    rcases Finset.mem_union.mp (q1p ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [qh5];exact hc2 a h2⟩
  omega
def z124 (n:ℕ) (C:Circuit) (g1 g2 w:ℕ):Prop:=
 OrReaches n C w g1∨ OrReaches n C w g2
noncomputable def z126 {n:ℕ} (C:Circuit) (s:Fin n→ Bool) (z1:Fin n) (g1 g2 a:ℕ):Fin n:=
 letI:=Classical.dec
 if h0:(side (n:=n) C a 0).card = 1 then
  let u:=Classical.choose (Finset.card_eq_one.mp h0)
  if h1:(side (n:=n) C a 1).card = 1 then
   let v:=Classical.choose (Finset.card_eq_one.mp h1)
   if z124 n C g1 g2 (opnd C a 0)∧ ¬ z124 n C g1 g2 (opnd C a 1) then v
   else if z124 n C g1 g2 (opnd C a 1)∧ ¬ z124 n C g1 g2 (opnd C a 0) then u
   else if s u = s z1 then u else v
  else u
 else if h1:(side (n:=n) C a 1).card = 1 then
  Classical.choose (Finset.card_eq_one.mp h1)
 else z1
lemma z128 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) (s:Fin n→ Bool) (z1:Fin n) (g1 g2:ℕ)
  {a:ℕ} (ha:a ∈ tops G C \ centreless G C):
  side (n:=n) C a 0 = {z126 C s z1 g1 g2 a}∨ 
   side (n:=n) C a 1 = {z126 C s z1 g1 g2 a}:=by
 have hst:=z129 hAO h4 ha
 unfold z126
 by_cases h0:(side (n:=n) C a 0).card = 1
 ·simp only [dif_pos h0]
  have hu:=Classical.choose_spec (Finset.card_eq_one.mp h0)
  by_cases h1:(side (n:=n) C a 1).card = 1
  ·simp only [dif_pos h1]
   have hv:=Classical.choose_spec (Finset.card_eq_one.mp h1)
   split_ifs
   ·exact Or.inr hv
   ·exact Or.inl hu
   ·exact Or.inl hu
   ·exact Or.inr hv
  ·simp only [dif_neg h1];exact Or.inl hu
 ·have h1:(side (n:=n) C a 1).card = 1:=hst.2.2.resolve_left h0
  simp only [dif_neg h0,dif_pos h1]
  exact Or.inr (Classical.choose_spec (Finset.card_eq_one.mp h1))
lemma z127 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) (h4:NoFourCycle G) (s:Fin n→ Bool) (z1:Fin n) (g1 g2:ℕ)
  {u v:Fin n} (he:s(u,v) ∈ starEdges G C):
  ∃ a ∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a = u∨ z126 C s z1 g1 g2 a = v:=by
 simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product] at he
 rcases he with ⟨a,ha,⟨p0,p1⟩,⟨hp0,hp1⟩,qg0⟩
 have haS:a ∈ tops G C \ centreless G C:=by
  rw [Finset.mem_sdiff];refine ⟨ha,fun hc=>?_⟩
  rw [centreless,Finset.mem_filter] at hc
  rcases hc.2 with h0 | h1
  ·rw [h0] at hp0;exact Finset.notMem_empty _ hp0
  ·rw [h1] at hp1;exact Finset.notMem_empty _ hp1
 refine ⟨a,haS,?_⟩
 rw [Sym2.eq_iff] at qg0
 rcases z128 hAO h4 s z1 g1 g2 haS with h0 | h1
 ·rw [h0,Finset.mem_singleton] at hp0
  rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·exact Or.inl hp0.symm
  ·exact Or.inr hp0.symm
 ·rw [h1,Finset.mem_singleton] at hp1
  rcases qg0 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·exact Or.inr hp1.symm
  ·exact Or.inl hp1.symm
lemma z100 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {g:ℕ} (hg:g = g1∨ g = g2):
  ∀ w < n + C.gates.length,(∀ k,w = n + k→ ¬ BelowF G C k)→ 
   (orIn n C w).Nonempty→ OrReaches n C w g→ 
   ∃ m ∈ orN G C \ lam G C,
    OrReaches n C w m∧ OrReaches n C (n + m) g∧ 
    (orIn n C (n + m)).Nonempty∧ orIn n C (n + m) ⊆ orIn n C w∧ 
    (orIn n C (opnd C m 0) = ∅∨ orIn n C (opnd C m 1) = ∅):=by
 have hgj:=z094.mp ((q00 g).mpr hg)
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro q53 hnb q52 hrg
  by_cases hwn:w < n
  ·exact absurd hrg (z112 hwn)
  ·have q0d:w - n < C.gates.length:=by omega
   have q0f:w = n + (w - n):=by omega
   set k:=w - n
   have q5w:¬ BelowF G C k:=hnb k q0f
   have q3d:(gateAt C k).op = GateOp.or:=by
    rcases hL.1.1 _ (z069 q0d) with q17 | hor
    ·exfalso;have q0g:=z107 (n:=n) q0d q17
     rw [← q0f] at q0g;exact q52.ne_empty q0g
    ·exact hor
   have q04:k ∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
   by_cases q0g:orIn n C (opnd C k 0) = ∅∨ orIn n C (opnd C k 1) = ∅
   ·refine ⟨k,Finset.mem_sdiff.mpr ⟨q04,fun hkl=>?_⟩,
     by rw [q0f];exact z115 q0d,by rwa [← q0f],
     by rwa [← q0f],by rw [← q0f],q0g⟩
    have hf:=Finset.mem_filter.mp hkl
    rcases q0g with h0 | h1
    ·exact hf.2.1.ne_empty h0
    ·exact hf.2.2.1.ne_empty h1
   ·push Not at q0g
    have q6w:(orIn n C (opnd C k 0)).Nonempty:=q0g.1
    have q62:(orIn n C (opnd C k 1)).Nonempty:=q0g.2
    rw [q0f,z111 q0d] at hrg
    have qom:k ≠ g:=fun h=>by rw [h,hgj.2.1] at q3d;cases q3d
    rcases hrg with rfl | ⟨_,u,hu,hnu,qjq,qmp⟩
    ·exact absurd rfl qom
    ·rw [z071 hL.1 q0d] at hu
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
     have qmq:∀ b:Fin 2,∀ m,opnd C k b = n + m→ ¬ BelowF G C m:=fun b m hm hbm=>
      z091 hL q01 hne q0d q3d q5w b (by rw [hm];exact hbm)
     have q6d:∀ b:Fin 2,orIn n C (opnd C k b) ⊆ orIn n C w:=by
      intro b;rw [q0f,z108 hL.1 q0d q3d]
      fin_cases b
      ·exact Finset.subset_union_left
      ·exact Finset.subset_union_right
     rcases hu with rfl | rfl
     ·obtain ⟨m,hm,hwm,hmg,qky,qdz,hme⟩:=
       ih (opnd C k 0) (by omega) (by omega) (qmq 0) q6w qmp
      refine ⟨m,hm,?_,hmg,qky,Finset.Subset.trans qdz (q6d 0),hme⟩
      rw [q0f,z111 q0d]
      exact Or.inr ⟨q3d,opnd C k 0,z105 hL.1 q0d 0,hwm.1,z104 hL.1 q0d 0,hwm⟩
     ·obtain ⟨m,hm,hwm,hmg,qky,qdz,hme⟩:=
       ih (opnd C k 1) (by omega) (by omega) (qmq 1) q62 qmp
      refine ⟨m,hm,?_,hmg,qky,Finset.Subset.trans qdz (q6d 1),hme⟩
      rw [q0f,z111 q0d]
      exact Or.inr ⟨q3d,opnd C k 1,z105 hL.1 q0d 1,hwm.1,z104 hL.1 q0d 1,hwm⟩
lemma z122 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C:Circuit} (hL:IsLeastAO G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {w:ℕ} (q53:w < n + C.gates.length) (hnb:∀ k,w = n + k→ ¬ BelowF G C k)
  (q0g:orIn n C w = ∅) (hr1:OrReaches n C w g1) (hr2:OrReaches n C w g2):
  ∃ m ∈ orN G C \ lam G C,g2 < m∧ orIn n C (n + m) = ∅:=by
 have hnw:n ≤ w:=hr1.1
 have q0d:w - n < C.gates.length:=by omega
 have q0f:w = n + (w - n):=by omega
 set k:=w - n
 have q5w:¬ BelowF G C k:=hnb k q0f
 have qo8:g2 ≤ k:=by have:=z113 hr2;omega
 have qpk:k ≠ g2:=by
  intro h;subst h
  have q2p:=z094.mp ((q00 k).mpr (Or.inr rfl))
  rw [q0f,z111 q0d] at hr1
  rcases hr1 with h1 | ⟨hor,_⟩
  ·omega
  ·rw [q2p.2.1] at hor;cases hor
 have q3d:(gateAt C k).op = GateOp.or:=by
  rcases hL.1.1 _ (z069 q0d) with q17 | hor
  ·exfalso
   have hkj:=(q00 k).mp (z094.mpr ⟨q0d,q17,q5w⟩)
   rcases hkj with rfl | rfl <;> omega
  ·exact hor
 have q04:k ∈ orN G C:=z096.mpr ⟨q0d,q3d,q5w⟩
 have q50:orIn n C (opnd C k 0) = ∅:=by
  have hu:=z108 hL.1 q0d q3d
  rw [← q0f,q0g] at hu
  exact (Finset.union_eq_empty.mp hu.symm).1
 refine ⟨k,Finset.mem_sdiff.mpr ⟨q04,fun hkl=>(Finset.mem_filter.mp hkl).2.1.ne_empty q50⟩,
  by omega,by rwa [← q0f]⟩
lemma z131 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hAO:IsAO2 n C) {a:ℕ} (ha:a ∈ tops G C) (b:Fin 2)
  {g:ℕ} (hr:OrReaches n C (opnd C a b) g)
  {w:Fin n} (hw:w ∈ side (n:=n) C a (1 - b)):
  ∀ x:Fin n→ Bool,gateVal n C g x = true→ x w = true→ graphFun G ∅ x = true:=by
 have ha':=z098.mp ha
 intro x hgx hxw
 apply ha'.2.2 x
 rw [z070,z140 hAO x ha'.1 ha'.2.1,Bool.and_eq_true]
 have hv1:=z117 hAO x hr hgx
 have hv2:=z110 hAO x hw hxw
 fin_cases b
 ·exact ⟨hv1,hv2⟩
 ·exact ⟨hv2,hv1⟩
lemma z072 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2)
  (hsz:s z1 = s z2) (q1l:s zp1 = s zp2)
  {v u:Fin n} (qh7:s(v,u) ∈ Ustar G C)
  (q1f:
   (gateVal n C g1 (pairInput v u) = true→ 
    (¬ ∀ x,gateVal n C g1 x = true→ x u = true→ graphFun G ∅ x = true)∧ 
    (∀ w:Fin n,s w = s v→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w u))∧ 
   (gateVal n C g2 (pairInput v u) = true→ 
    (¬ ∀ x,gateVal n C g2 x = true→ x u = true→ graphFun G ∅ x = true)∧ 
    (∀ w:Fin n,s w = s v→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w u)))
  (q4g:¬ (gateVal n C g1 (pairInput v u) = true∧ gateVal n C g2 (pairInput v u) = true∧ 
   ∀ x,gateVal n C g1 x = true→ gateVal n C g2 x = true→ graphFun G ∅ x = true)):
  (∃ a ∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a = v)∨ 
  (∃ a ∈ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g = g1∨ g = g2)∧ 
   gateVal n C g (pairInput v u) = true∧ 
   side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g∧ v ∈ side (n:=n) C a (1 - b))∨ 
  (s v = s zp1∧ ∃ a ∈ tops G C \ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g = g1∨ g = g2)∧ 
   gateVal n C g (pairInput v u) = true∧ 
   side (n:=n) C a (1 - b) = {v}∧ OrReaches n C (opnd C a b) g∧ 
   ∃ g':ℕ,(g' = g1∨ g' = g2)∧ g' ≠ g∧ OrReaches n C (opnd C a (1 - b)) g'∧ 
   ∃ mv ∈ orN G C \ lam G C,OrReaches n C (n + mv) g'∧ orIn n C (n + mv) = {v}∧ 
   ∃ u':Fin n,side (n:=n) C a b = {u'}∧ s u' = s z1∧ 
   ∃ mu ∈ orN G C \ lam G C,OrReaches n C (n + mu) g∧ orIn n C (n + mu) = {u'}):=by
 have hne:∃ a b:Fin n,G.Adj a b:=⟨z1,zp1,hf1.1⟩
 have qh8:G.Adj v u:=SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp qh7).1
 have q6e:s(v,u) ∉ starEdges G C:=(Finset.mem_sdiff.mp qh7).2
 have hcx:circuitFun n C (pairInput v u) = true:=by
  rw [congrFun hL.2.1 (pairInput v u)];exact (z074 v u).mpr qh8
 obtain ⟨a,ha,hva⟩:=(z023 hL hne _).mp hcx
 have ha':=z098.mp ha
 rw [z070,z140 hL.1 _ ha'.1 ha'.2.1,Bool.and_eq_true] at hva
 have hw0:=(z103 hL q01 hne q00 (opnd C a 0)
  (by have:=z104 hL.1 ha'.1 0;omega) (z130 hL hne ha 0) (pairInput v u)).mp hva.1
 have hw1:=(z103 hL q01 hne q00 (opnd C a 1)
  (by have:=z104 hL.1 ha'.1 1;omega) (z130 hL hne ha 1) (pairInput v u)).mp hva.2
 have q54:¬ ((∃ w ∈ side (n:=n) C a 0,pairInput v u w = true)∧ 
   (∃ w ∈ side (n:=n) C a 1,pairInput v u w = true)):=by
  rintro ⟨⟨w0,q95,qgm⟩,⟨w1,qgn,qgo⟩⟩
  apply q6e
  simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
  simp only [pairInput,decide_eq_true_eq] at qgm qgo
  have q52:w0 ≠ w1:=fun h=>by subst h;exact G.loopless.irrefl w0 (z132 hL.1 ha q95 qgn)
  refine ⟨a,ha,(w0,w1),⟨q95,qgn⟩,?_⟩
  rw [Sym2.eq_iff]
  rcases qgm with rfl | rfl <;> rcases qgo with rfl | rfl
  ·exact absurd rfl q52
  ·exact Or.inl ⟨rfl,rfl⟩
  ·exact Or.inr ⟨rfl,rfl⟩
  ·exact absurd rfl q52
 have q1k:∀ g,(g = g1∨ g = g2)→ 
   ¬ (OrReaches n C (opnd C a 0) g∧ OrReaches n C (opnd C a 1) g):=by
  rintro g hg ⟨h0,h1⟩
  have hgj:=z094.mp ((q00 g).mpr hg)
  apply hgj.2.2
  intro x hgx
  apply ha'.2.2 x
  rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Bool.and_eq_true]
  exact ⟨z117 hL.1 x h0 hgx,z117 hL.1 x h1 hgx⟩
 have q2r:∀ g g',(g = g1∧ g' = g2∨ g = g2∧ g' = g1)→ 
   gateVal n C g (pairInput v u) = true→ gateVal n C g' (pairInput v u) = true→ 
   ¬ (OrReaches n C (opnd C a 0) g∧ OrReaches n C (opnd C a 1) g'):=by
  rintro g g' qon hgv qmr ⟨h0,h1⟩
  apply q4g
  rcases qon with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  ·refine ⟨hgv,qmr,fun x hx1 hx2=>ha'.2.2 x ?_⟩
   rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Bool.and_eq_true]
   exact ⟨z117 hL.1 x h0 hx1,z117 hL.1 x h1 hx2⟩
  ·refine ⟨qmr,hgv,fun x hx1 hx2=>ha'.2.2 x ?_⟩
   rw [z070,z140 hL.1 x ha'.1 ha'.2.1,Bool.and_eq_true]
   exact ⟨z117 hL.1 x h0 hx2,z117 hL.1 x h1 hx1⟩
 have q0v:∀ b:Fin 2,∀ g,(g = g1∨ g = g2)→ 
   OrReaches n C (opnd C a b) g→ gateVal n C g (pairInput v u) = true→ 
   (∃ w ∈ side (n:=n) C a (1 - b),pairInput v u w = true)→ 
   v ∈ side (n:=n) C a (1 - b):=by
  intro b g hg hrb hgv ⟨w,hwm,hxw⟩
  simp only [pairInput,decide_eq_true_eq] at hxw
  rcases hxw with rfl | rfl
  ·exact hwm
  ·exfalso
   have q3i:=z131 hL.1 ha b hrb hwm
   rcases hg with rfl | rfl
   ·exact (q1f.1 hgv).1 q3i
   ·exact (q1f.2 hgv).1 q3i
 have qh9:∃ b:Fin 2,∃ g:ℕ,(g = g1∨ g = g2)∧ 
   OrReaches n C (opnd C a b) g∧ gateVal n C g (pairInput v u) = true∧ 
   v ∈ side (n:=n) C a (1 - b):=by
  rcases hw0 with h0 | ⟨hr0,hg1⟩ | ⟨hr0,hg2⟩
  ·rcases hw1 with h1 | ⟨hr1,hg1⟩ | ⟨hr1,hg2⟩
   ·exact absurd ⟨h0,h1⟩ q54
   ·exact ⟨1,g1,Or.inl rfl,hr1,hg1,q0v 1 g1 (Or.inl rfl) hr1 hg1 (by simpa [side] using h0)⟩
   ·exact ⟨1,g2,Or.inr rfl,hr1,hg2,q0v 1 g2 (Or.inr rfl) hr1 hg2 (by simpa [side] using h0)⟩
  ·rcases hw1 with h1 | ⟨hr1,_⟩ | ⟨hr1,hg2⟩
   ·exact ⟨0,g1,Or.inl rfl,hr0,hg1,q0v 0 g1 (Or.inl rfl) hr0 hg1 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0,hr1⟩ (q1k g1 (Or.inl rfl))
   ·exact absurd ⟨hr0,hr1⟩ (q2r g1 g2 (Or.inl ⟨rfl,rfl⟩) hg1 hg2)
  ·rcases hw1 with h1 | ⟨hr1,hg1⟩ | ⟨hr1,_⟩
   ·exact ⟨0,g2,Or.inr rfl,hr0,hg2,q0v 0 g2 (Or.inr rfl) hr0 hg2 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0,hr1⟩ (q2r g2 g1 (Or.inr ⟨rfl,rfl⟩) hg2 hg1)
   ·exact absurd ⟨hr0,hr1⟩ (q1k g2 (Or.inr rfl))
 obtain ⟨b,g,hg,hrb,hgv,q0p⟩:=qh9
 by_cases q0g:side (n:=n) C a b = ∅
 ·right;left
  have haC:a ∈ centreless G C:=by
   unfold centreless;rw [Finset.mem_filter]
   refine ⟨ha,?_⟩
   fin_cases b
   ·exact Or.inl q0g
   ·exact Or.inr q0g
  exact ⟨a,haC,b,g,hg,hgv,q0g,hrb,q0p⟩
 ·have qax:(side (n:=n) C a b).Nonempty:=Finset.nonempty_iff_ne_empty.mpr q0g
  have haS:a ∈ tops G C \ centreless G C:=by
   rw [Finset.mem_sdiff];refine ⟨ha,fun hc=>?_⟩
   unfold centreless at hc;rw [Finset.mem_filter] at hc
   rcases z043 b with rfl | rfl
   ·rcases hc.2 with h0 | h1
    ·exact q0g h0
    ·simp only [sub_zero] at q0p;rw [h1] at q0p;exact Finset.notMem_empty _ q0p
   ·rcases hc.2 with h0 | h1
    ·have h11:(1:Fin 2) - 1 = 0:=rfl;rw [h11,h0] at q0p;exact Finset.notMem_empty _ q0p
    ·exact q0g h1
  have q09:side (n:=n) C a (1 - b) = {v}:=by
   ext w
   simp only [Finset.mem_singleton]
   constructor
   ·intro hw
    by_contra q52
    have q4h:1 < (side (n:=n) C a (1 - b)).card:=
     Finset.one_lt_card.mpr ⟨w,hw,v,q0p,q52⟩
    have hst:=z129 hL.1 h4 haS
    have q1c:(side (n:=n) C a b).card = 1:=by
     rcases z043 b with rfl | rfl
     ·simp only [sub_zero] at q4h;exact hst.2.2.resolve_right (by omega)
     ·have h11:(1:Fin 2) - 1 = 0:=rfl;rw [h11] at q4h
      exact hst.2.2.resolve_left (by omega)
    obtain ⟨w0,hw0⟩:=Finset.card_eq_one.mp q1c
    have q95:w0 ∈ side (n:=n) C a b:=by rw [hw0];simp
    have q6f:G.Adj v w0:=by
     rcases z043 b with rfl | rfl
     ·exact (z132 hL.1 ha q95 q0p).symm
     ·exact z132 hL.1 ha q0p q95
    have q6g:G.Adj w w0:=by
     rcases z043 b with rfl | rfl
     ·exact (z132 hL.1 ha q95 hw).symm
     ·exact z132 hL.1 ha hw q95
    have qms:s w = s v:=z015 (q03 w w0 q6g) (q03 v w0 q6f)
    have q3i:=z131 hL.1 ha b hrb hw
    have qe0:G.Adj w u:=by
     rcases hg with rfl | rfl
     ·exact (q1f.1 hgv).2 w qms q3i
     ·exact (q1f.2 hgv).2 w qms q3i
    have qbc:w0 = u:=z102 h4 q52 q6g q6f qe0 qh8
    subst qbc
    apply q6e
    simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
    rcases z043 b with rfl | rfl
    ·exact ⟨a,ha,(w0,v),⟨q95,q0p⟩,Sym2.eq_swap⟩
    ·exact ⟨a,ha,(v,w0),⟨q0p,q95⟩,rfl⟩
   ·rintro rfl;exact q0p
  by_cases qj7:z126 C s z1 g1 g2 a = v
  ·exact Or.inl ⟨a,haS,qj7⟩
  ·right;right
   have q0a:(side (n:=n) C a (1 - b)).card = 1:=by rw [q09];simp
   have q1c:(side (n:=n) C a b).card = 1:=by
    by_contra qmt
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09
     rw [dif_neg qmt,dif_pos q0a]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
    ·have h11:(1:Fin 2) - 1 = 0:=rfl
     rw [h11] at q0a q09
     rw [dif_pos q0a,dif_neg qmt]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
   obtain ⟨u',hu'⟩:=Finset.card_eq_one.mp q1c
   have qbd:z124 n C g1 g2 (opnd C a b):=by
    rcases hg with rfl | rfl
    ·exact Or.inl hrb
    ·exact Or.inr hrb
   have q4i:z124 n C g1 g2 (opnd C a (1 - b)):=by
    by_contra qha
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09 qha
     rw [dif_pos q1c,dif_pos q0a,if_pos ⟨qbd,qha⟩]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
    ·have h11:(1:Fin 2) - 1 = 0:=rfl
     rw [h11] at q0a q09 qha
     rw [dif_pos q0a,dif_pos q1c,if_neg (fun h=>qha h.1),if_pos ⟨qbd,qha⟩]
     have hch:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     exact Finset.singleton_injective (hch.symm.trans q09)
   have q9t:s u' = s z1:=by
    have q5h:G.Adj u' v:=by
     have qhb:u' ∈ side (n:=n) C a b:=by rw [hu'];simp
     rcases z043 b with rfl | rfl
     ·exact z132 hL.1 ha qhb q0p
     ·exact (z132 hL.1 ha q0p qhb).symm
    have qbe:s u' ≠ s v:=q03 u' v q5h
    by_contra qhc
    have qhd:s v = s z1:=z015 qbe.symm (Ne.symm qhc)
    apply qj7
    unfold z126
    rcases z043 b with rfl | rfl
    ·simp only [sub_zero] at q0a q09 q4i
     have qkz:=Classical.choose_spec (Finset.card_eq_one.mp q1c)
     have ql0:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     have qhe:Classical.choose (Finset.card_eq_one.mp q1c) = u':=
      Finset.singleton_injective (qkz.symm.trans hu')
     have qj8:Classical.choose (Finset.card_eq_one.mp q0a) = v:=
      Finset.singleton_injective (ql0.symm.trans q09)
     rw [dif_pos q1c,dif_pos q0a,if_neg (fun h=>h.2 q4i),
      if_neg (fun h=>h.2 qbd),qhe,if_neg qhc,qj8]
    ·have h11:(1:Fin 2) - 1 = 0:=rfl
     rw [h11] at q0a q09 q4i
     have qkz:=Classical.choose_spec (Finset.card_eq_one.mp q0a)
     have ql0:=Classical.choose_spec (Finset.card_eq_one.mp q1c)
     have qhe:Classical.choose (Finset.card_eq_one.mp q0a) = v:=
      Finset.singleton_injective (qkz.symm.trans q09)
     have qj8:Classical.choose (Finset.card_eq_one.mp q1c) = u':=
      Finset.singleton_injective (ql0.symm.trans hu')
     rw [dif_pos q0a,dif_pos q1c,if_neg (fun h=>h.2 qbd),
      if_neg (fun h=>h.2 q4i),qhe,if_pos qhd]
   have qe1:s v = s zp1:=by
    have q5h:G.Adj u' v:=by
     have qhb:u' ∈ side (n:=n) C a b:=by rw [hu'];simp
     rcases z043 b with rfl | rfl
     ·exact z132 hL.1 ha qhb q0p
     ·exact (z132 hL.1 ha q0p qhb).symm
    exact z015 (q03 u' v q5h).symm (by rw [q9t];exact (q03 z1 zp1 hf1.1).symm)
   obtain ⟨g',hg',qj9⟩:∃ g',(g' = g1∨ g' = g2)∧ OrReaches n C (opnd C a (1 - b)) g':=by
    rcases q4i with h1 | h2
    ·exact ⟨g1,Or.inl rfl,h1⟩
    ·exact ⟨g2,Or.inr rfl,h2⟩
   have q7a:g' ≠ g:=by
    intro heq;subst heq
    apply q1k g' hg'
    fin_cases b
    ·exact ⟨hrb,by simpa using qj9⟩
    ·exact ⟨by simpa using qj9,hrb⟩
   obtain ⟨mv,qe2,_,q38,qhf,q7b,_⟩:=
    z100 hL q01 hne q00 hg'
     (opnd C a (1 - b)) (by have:=z104 hL.1 ha'.1 (1 - b);omega)
     (z130 hL hne ha (1 - b)) (by rw [side] at q09;rw [q09];simp) qj9
   have q05:orIn n C (n + mv) = {v}:=by
    rw [side] at q09;rw [q09] at q7b
    ext w;constructor
    ·exact fun hw=>q7b hw
    ·intro hw;rw [Finset.mem_singleton] at hw;subst hw
     obtain ⟨y,hy⟩:=qhf
     have:=Finset.mem_singleton.mp (q7b hy);subst this;exact hy
   obtain ⟨mu,qe3,_,q3j,qhg,q7c,_⟩:=
    z100 hL q01 hne q00 hg
     (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega)
     (z130 hL hne ha b) (by rw [side] at hu';rw [hu'];simp) hrb
   have q06:orIn n C (n + mu) = {u'}:=by
    rw [side] at hu';rw [hu'] at q7c
    ext w;constructor
    ·exact fun hw=>q7c hw
    ·intro hw;rw [Finset.mem_singleton] at hw;subst hw
     obtain ⟨y,hy⟩:=qhg
     have:=Finset.mem_singleton.mp (q7c hy);subst this;exact hy
   exact ⟨qe1,a,haS,b,g,hg,hgv,q09,hrb,g',hg',q7a,qj9,
    mv,qe2,q38,q05,u',hu',q9t,mu,qe3,q3j,q06⟩
lemma z136 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {w:ℕ} (q53:w < n + C.gates.length) (q76:∀ k,w = n + k→ ¬ BelowF G C k)
  (A:Finset (Fin n)) (ql1:A.Nonempty) (qhh:A ⊆ orIn n C w)
  (FacAll:Finset ℕ)
  (q2n:∀ k,OrReaches n C w k→ k ∈ lam G C ∪ FacAll→ (orIn n C (n + k) ∩ A).card ≤ 1):
  let H:=(orN G C \ lam G C).filter (fun k=>
   OrReaches n C w k∧ k ∉ FacAll∧ 2 ≤ (orIn n C (n + k) ∩ A).card)
  A.card ≤ H.card + 1:=by
 intro H
 let R:ℕ→ Finset (Fin n):=fun u=>
  if hu:u < n then
   if ⟨u,hu⟩ ∈ A then {⟨u,hu⟩} else ∅
  else if OrReaches n C w (u - n) then orIn n C u ∩ A else ∅
 have q3g:∀ k ∈ H,k < C.gates.length:=fun k hk=>
  (z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have q83:∀ u < n + C.gates.length,(∀ k ∈ H,u ≠ n + k)→ (R u).card ≤ 1:=by
  intro u hu q8o
  dsimp only [R]
  split_ifs with hun q23 q0q
  ·simp
  ·simp
  ·have q0d:u - n < C.gates.length:=by omega
   have q1d:u = n + (u - n):=by omega
   set k:=u - n
   have q5w:¬ BelowF G C k:=by
    intro hbk
    have q9r:∀ x < n + C.gates.length,(∀ m,x = n + m→ ¬ BelowF G C m)→ 
      OrReaches n C x k→ False:=by
     intro x
     induction x using Nat.strong_induction_on with
     | ind x ihx=>
      intro qoo qe4 ql2
      by_cases hxn:x < n
      ·exact z112 hxn ql2
      ·have q36:x - n < C.gates.length:=by omega
       have qbf:x = n + (x - n):=by omega
       rw [qbf,z111 q36] at ql2
       rcases ql2 with heq | ⟨qaw,y,hy,hny,qpl,qop⟩
       ·exact qe4 (x - n) qbf (heq ▸ hbk)
       ·rw [z071 hL.1 q36] at hy
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
        have qoq:∀ m,y = n + m→ ¬ BelowF G C m:=by
         intro m hm hbm
         rcases hy with rfl | rfl
         ·exact z091 hL q01 hne q36 qaw (qe4 _ qbf) 0 (by rw [hm];exact hbm)
         ·exact z091 hL q01 hne q36 qaw (qe4 _ qbf) 1 (by rw [hm];exact hbm)
        exact ihx y (by omega) (by omega) qoq qop
    exact q9r w q53 q76 q0q
   rcases hL.1.1 _ (z069 q0d) with q17 | hor
   ·rw [q1d,z107 (n:=n) q0d q17];simp
   ·have q04:k ∈ orN G C:=z096.mpr ⟨q0d,hor,q5w⟩
    by_cases hkl:k ∈ lam G C
    ·rw [q1d];exact q2n k q0q (Finset.mem_union_left _ hkl)
    ·by_cases hkf:k ∈ FacAll
     ·rw [q1d];exact q2n k q0q (Finset.mem_union_right _ hkf)
     ·by_contra hgt
      push Not at hgt
      have hkH:k ∈ H:=Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨q04,hkl⟩,q0q,hkf,by rw [← q1d];omega⟩
      exact q8o k hkH q1d
  ·simp
 have qdk:∀ k ∈ H,R (n + k) ⊆ R (opnd C k 0) ∪ R (opnd C k 1):=by
  intro k hk
  have hkf:=Finset.mem_filter.mp hk
  have q04:=z096.mp (Finset.mem_sdiff.mp hkf.1).1
  have q0q:OrReaches n C w k:=hkf.2.1
  intro a ha
  dsimp only [R] at ha
  rw [dif_neg (by omega),Nat.add_sub_cancel_left,if_pos q0q,Finset.mem_inter,
   z108 hL.1 q04.1 q04.2.1,Finset.mem_union] at ha
  rw [Finset.mem_union]
  rcases ha.1 with h0 | h1
  ·left
   dsimp only [R]
   by_cases h0n:opnd C k 0 < n
   ·rw [dif_pos h0n]
    have q3z:a = ⟨opnd C k 0,h0n⟩:=(z095 C a ⟨opnd C k 0,h0n⟩).mp h0
    subst q3z;rw [if_pos ha.2];exact Finset.mem_singleton_self _
   ·rw [dif_neg h0n]
    have hr0:OrReaches n C w (opnd C k 0 - n):=by
     apply z116 q0q
     rw [z111 q04.1]
     refine Or.inr ⟨q04.2.1,opnd C k 0,z105 hL.1 q04.1 0,by omega,
      z104 hL.1 q04.1 0,?_⟩
     have qhe:opnd C k 0 = n + (opnd C k 0 - n):=by omega
     have hrs:OrReaches n C (n + (opnd C k 0 - n)) (opnd C k 0 - n):=
      z115 (by have:=z104 hL.1 q04.1 0;have:=q04.1;omega)
     rwa [← qhe] at hrs
    rw [if_pos hr0,Finset.mem_inter];exact ⟨h0,ha.2⟩
  ·right
   dsimp only [R]
   by_cases h1n:opnd C k 1 < n
   ·rw [dif_pos h1n]
    have q3z:a = ⟨opnd C k 1,h1n⟩:=(z095 C a ⟨opnd C k 1,h1n⟩).mp h1
    subst q3z;rw [if_pos ha.2];exact Finset.mem_singleton_self _
   ·rw [dif_neg h1n]
    have hr1:OrReaches n C w (opnd C k 1 - n):=by
     apply z116 q0q
     rw [z111 q04.1]
     refine Or.inr ⟨q04.2.1,opnd C k 1,z105 hL.1 q04.1 1,by omega,
      z104 hL.1 q04.1 1,?_⟩
     have qj8:opnd C k 1 = n + (opnd C k 1 - n):=by omega
     have hrs:OrReaches n C (n + (opnd C k 1 - n)) (opnd C k 1 - n):=
      z115 (by have:=z104 hL.1 q04.1 1;have:=q04.1;omega)
     rwa [← qj8] at hrs
    rw [if_pos hr1,Finset.mem_inter];exact ⟨h1,ha.2⟩
 obtain ⟨comp,q18,q2w⟩:=z106 hL.1 A H q3g R q83 qdk
 obtain ⟨c,hc⟩:=q2w w q53
 have q9u:A ⊆ R w:=by
  intro a ha
  dsimp only [R]
  by_cases hwn:w < n
  ·rw [dif_pos hwn]
   have q3z:a = ⟨w,hwn⟩:=(z095 C a ⟨w,hwn⟩).mp (qhh ha)
   subst q3z;rw [if_pos ha];exact Finset.mem_singleton_self _
  ·rw [dif_neg hwn]
   have hrw:OrReaches n C w (w - n):=by
    have q8s:w = n + (w - n):=by omega
    have hrs:OrReaches n C (n + (w - n)) (w - n):=z115 (by omega)
    rwa [← q8s] at hrs
   rw [if_pos hrw,Finset.mem_inter];exact ⟨qhh ha,ha⟩
 exact z101 q18 (Finset.Subset.refl A) ql1 ⟨c,fun a ha=>hc a (q9u ha)⟩
lemma z037 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  (q29:centreless G C = ∅):
  ∃ m ∈ orN G C \ lam G C,g2 < m:=by
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q9b:=z120 hL hne
 have q32:=z121 hL hne
 have q9v:BelowF G C (C.output - n):=by
  rcases Finset.mem_union.mp q32 with h | h
  ·exact (z098.mp h).2.2
  ·exact (z097.mp h).2.2
 have q4j:∀ k < C.gates.length,¬ BelowF G C k→ InCone n C g2 k→ 
   OrReaches n C (n + k) g2:=by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
   intro hk hnb hin
   have hgt:g2 < k:=z079 hin
   have q3d:(gateAt C k).op = GateOp.or:=by
    rcases hL.1.1 _ (z069 hk) with q17 | hor
    ·exfalso
     have hkj:=(q00 k).mp (z094.mpr ⟨hk,q17,hnb⟩)
     rcases hkj with rfl | rfl <;> omega
    ·exact hor
   rw [z078 hk] at hin
   rcases hin with ⟨w,hw,hnw,qmu,heq | q0c⟩
   ·rw [z111 hk]
    refine Or.inr ⟨q3d,w,hw,hnw,qmu,?_⟩
    rw [show w = n + g2 by omega];exact z115 q2p.1
   ·have qhi:¬ BelowF G C (w - n):=by
     intro hbw
     rw [z071 hL.1 hk] at hw
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     rcases hw with rfl | rfl
     ·exact z091 hL q01 hne hk q3d hnb 0
       (by rw [show opnd C k 0 = n + (opnd C k 0 - n) by omega];exact hbw)
     ·exact z091 hL q01 hne hk q3d hnb 1
       (by rw [show opnd C k 1 = n + (opnd C k 1 - n) by omega];exact hbw)
    have qe5:=ih (w - n) (by omega) (by omega) qhi q0c
    rw [z111 hk]
    exact Or.inr ⟨q3d,w,hw,hnw,qmu,by rwa [show n + (w - n) = w by omega] at qe5⟩
 have qe6:∀ j < C.gates.length,BelowF G C j→ InCone n C g2 j→ 
   ∃ a ∈ tops G C,∃ b:Fin 2,OrReaches n C (opnd C a b) g2:=by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih=>
   intro hj hbf hin
   rcases hL.1.1 _ (z069 hj) with q17 | hor
   ·have q8x:j ∈ tops G C:=z098.mpr ⟨hj,q17,hbf⟩
    rw [z078 hj] at hin
    rcases hin with ⟨w,hw,hnw,qfz,heq | q0c⟩
    ·rw [z071 hL.1 hj] at hw
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     have hrg:OrReaches n C w g2:=by rw [show w = n + g2 by omega];exact z115 q2p.1
     rcases hw with rfl | rfl
     ·exact ⟨j,q8x,0,hrg⟩
     ·exact ⟨j,q8x,1,hrg⟩
    ·rw [z071 hL.1 hj] at hw
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     rcases hw with rfl | rfl
     ·have qhi:=z130 hL hne q8x 0 (opnd C j 0 - n) (by omega)
      have hr:=q4j (opnd C j 0 - n) (by omega) qhi q0c
      exact ⟨j,q8x,0,by rwa [show n + (opnd C j 0 - n) = opnd C j 0 by omega] at hr⟩
     ·have qhi:=z130 hL hne q8x 1 (opnd C j 1 - n) (by omega)
      have hr:=q4j (opnd C j 1 - n) (by omega) qhi q0c
      exact ⟨j,q8x,1,by rwa [show n + (opnd C j 1 - n) = opnd C j 1 by omega] at hr⟩
   ·rw [z078 hj] at hin
    rcases hin with ⟨w,hw,hnw,qfz,heq | q0c⟩
    ·exfalso
     rw [z071 hL.1 hj] at hw
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     have qor:BelowF G C g2:=by
      rcases hw with rfl | rfl
      ·have h0:=(z119 hL hj hor hbf 0).2.2;rwa [← heq] at h0
      ·have h1:=(z119 hL hj hor hbf 1).2.2;rwa [← heq] at h1
     exact q2p.2.2 qor
    ·rw [z071 hL.1 hj] at hw
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     rcases hw with rfl | rfl
     ·have h0:=z119 hL hj hor hbf 0
      exact ih (opnd C j 0 - n) (by omega) h0.2.1 h0.2.2 q0c
     ·have h1:=z119 hL hj hor hbf 1
      exact ih (opnd C j 1 - n) (by omega) h1.2.1 h1.2.2 q0c
 have qbg:InCone n C g2 (C.output - n):=by
  have hc:=(z088 hL hne g2 q2p.1).2
  rcases hc with heq | ⟨_,hin⟩
  ·exfalso;apply q2p.2.2;rw [show g2 = C.output - n by omega];exact q9v
  ·exact hin
 obtain ⟨a,ha,b,hrb⟩:=qe6 (C.output - n) (by omega) q9v qbg
 have ha':=z098.mp ha
 have qax:(side (n:=n) C a b).Nonempty:=by
  rw [Finset.nonempty_iff_ne_empty]
  intro q0g
  have hac:a ∈ centreless G C:=by
   unfold centreless;rw [Finset.mem_filter]
   refine ⟨ha,?_⟩;fin_cases b
   ·exact Or.inl q0g
   ·exact Or.inr q0g
  rw [q29] at hac;exact Finset.notMem_empty _ hac
 obtain ⟨m,hm,_,qg4,_,_,_⟩:=z100 hL q01 hne q00 (Or.inr rfl)
  (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega) (z130 hL hne ha b) qax hrb
 have hle:g2 ≤ m:=by have:=z113 qg4;omega
 have qmv:m ≠ g2:=by
  intro h;subst h
  have h1:=(z096.mp (Finset.mem_sdiff.mp hm).1).2.1
  rw [h1] at q2p;cases q2p.2.1
 exact ⟨m,hm,by omega⟩
lemma z022 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z zp:Fin n}
  (hf1:z000 G C g1 C1 D1 z zp) (hf2:z000 G C g2 C2 D2 z zp):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z,zp,hf1.1⟩
 have qdf:g1 ≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q39:z ≠ zp:=G.ne_of_adj hf1.1
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 rfl rfl
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 set Cs:=C1 ∪ C2
 set Ds:=D1 ∪ D2
 set MC:=Cs.filter (fun c=>s(c,zp) ∈ Ustar G C)
 set MD:=Ds.filter (fun d=>s(z,d) ∈ Ustar G C)
 set FacC:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k∨ OrReaches n C w2C k)
 set FacD:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k∨ OrReaches n C w2D k)
 have q5i:∀ k ∈ FacC,k < g2:=by
  intro k hk
  have hr:=(Finset.mem_filter.mp hk).2
  rcases hr with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 b1;omega
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 b2;omega
 have q1g:∀ k ∈ FacD,k < g2:=by
  intro k hk
  have hr:=(Finset.mem_filter.mp hk).2
  rcases hr with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 (1 - b1);omega
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 (1 - b2);omega
 have q7d:Disjoint Cs Ds:=by
  rw [Finset.disjoint_left];intro u huC huD
  have hsc:s u = s z:=by
   rcases Finset.mem_union.mp huC with h | h
   ·exact z046 q03 hf1 h
   ·exact z046 q03 hf2 h
  have hsd:s u = s zp:=by
   rcases Finset.mem_union.mp huD with h | h
   ·exact z047 q03 hf1 h
   ·exact z047 q03 hf2 h
  exact q03 z zp hf1.1 (hsc.symm.trans hsd)
 have q5j:Disjoint FacC FacD:=by
  rw [Finset.disjoint_left];intro k hkC hkD
  have q04:=z096.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hkC).1).1
  have q68:orIn n C (n + k) ⊆ Cs:=by
   rcases (Finset.mem_filter.mp hkC).2 with h1 | h2
   ·exact Finset.Subset.trans (z109 h1) (by rw [show orIn n C w1C = C1 from qci];exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (z109 h2) (Finset.Subset.trans q44 Finset.subset_union_right)
  have q69:orIn n C (n + k) ⊆ Ds:=by
   rcases (Finset.mem_filter.mp hkD).2 with h1 | h2
   ·exact Finset.Subset.trans (z109 h1) (by rw [show orIn n C w1D = D1 from qb0];exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (z109 h2) (Finset.Subset.trans q2o Finset.subset_union_right)
  have q0g:orIn n C (n + k) = ∅:=by
   ext u;simp only [Finset.notMem_empty,iff_false]
   intro hu;exact Finset.disjoint_left.mp q7d (q68 hu) (q69 hu)
  have qo9:k < g2:=q5i k hkC
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>by have:=z113 h;omega
  have q10:∀ x,wval C x (n + k) = true↔ OrReaches n C (n + k) g1∧ gateVal n C g1 x = true:=by
   intro x
   have h:=z103 hL q01 hne q00 (n + k) (by omega)
    (fun m hm=>by have:m = k:=(by omega);subst this;exact q04.2.2) x
   simpa [q0g,hn2] using h
  have hr1:OrReaches n C (n + k) g1:=((q10 (fun _=>true)).mp (z138 hL.1 (n + k) (by omega))).1
  have qdn:g1 ≤ k:=by have:=z113 hr1;omega
  have qgb:k ≠ g1:=fun h=>by rw [h,q5x.2.1] at q04;cases q04.2.1
  apply z090 hL hne q04.1 (by omega:n + g1 < n + k)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [q10 x];simp [hr1,z070]
 have q2q:∀ a,a ∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b = n + m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have qbh:C1 ∪ C2 = C1 ∪ orIn n C w2C:=by
  by_cases hr:OrReaches n C w2C g1
  ·have h:=q6h hr
   rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
  ·rw [show orIn n C w2C = C2 from q3k hr]
 have q5k:D1 ∪ D2 = D1 ∪ orIn n C w2D:=by
  by_cases hr:OrReaches n C w2D g1
  ·have h:=q5a hr
   rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
  ·rw [show orIn n C w2D = D2 from q2a hr]
 have qhj:z ∈ orIn n C w2C∨ OrReaches n C w2C g1:=by
  by_cases hr:OrReaches n C w2C g1
  ·exact Or.inr hr
  ·left;rw [show orIn n C w2C = C2 from q3k hr];exact hf2.2.1
 have qe7:zp ∈ orIn n C w2D∨ OrReaches n C w2D g1:=by
  by_cases hr:OrReaches n C w2D g1
  ·exact Or.inr hr
  ·left;rw [show orIn n C w2D = D2 from q2a hr];exact hf2.2.2.1
 have q5l:=z099 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n + g2)
  (z104 hL.1 q2p.1 b2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2)
  (show orIn n C w1C = C1 from qci) q44 qbh
  (fun u hu=>by rcases Finset.mem_union.mp hu with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
  hf1.2.1 qhj
 have q7e:=z099 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n + g2)
  (z104 hL.1 q2p.1 (1 - b2))
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1))
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2))
  (show orIn n C w1D = D1 from qb0) q2o q5k
  (fun u hu=>by rcases Finset.mem_union.mp hu with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
  hf1.2.2.1 qe7
 have qhk:Cs.filter (fun u=>s(zp,u) ∈ Ustar G C) = MC:=by
  ext u;simp [MC,Sym2.eq_swap]
 dsimp only at q5l q7e
 rw [qhk] at q5l
 have q5m:FacC ∪ FacD ⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have run_surgery:∀ L:Fin n→ Finset (Fin n),
   (∀ u ∈ L z,G.Adj z u)→ (∀ u ∈ L zp,G.Adj zp u)→ 
   (∀ e ∈ Ustar G C,(∃ u ∈ L z,e = s(z,u))∨ (∃ u ∈ L zp,e = s(zp,u)))→ 
   let Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   let Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
   2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (L z).card + (L zp).card + (Zact \ Zhas).card:=by
  intro L hLz q5y q8w Zact Zhas
  let topOf:Fin n→ ℕ:=fun v=>
   if h:∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v then Classical.choose h else 0
  have qhl:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv=>(Finset.mem_filter.mp hv).2)
   (fun v hv u hu=>by
    have hv':=(Finset.mem_filter.mp hv).1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl
    ·exact hLz u hu
    ·exact q5y u hu)
   (fun e he=>by
    rcases q8w e he with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    ·exact ⟨z,Finset.mem_filter.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp,Finset.mem_filter.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩)
   (fun v hv=>by
    have h:=(Finset.mem_filter.mp hv).2
    simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
   (fun v hv=>by
    have h:=(Finset.mem_filter.mp hv).2
    simp only [topOf,dif_pos h]
    have hsp:=Classical.choose_spec h
    have q3f:=z128 hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at q3f)
   (fun v1 hv1 v2 hv2 heq=>by
    have h1:=(Finset.mem_filter.mp hv1).2
    have h2:=(Finset.mem_filter.mp hv2).2
    simp only [topOf,dif_pos h1,dif_pos h2] at heq
    have qhm:=Classical.choose_spec h1
    have qhn:=Classical.choose_spec h2
    rw [← qhm.2,heq,qhn.2])
  have qe8:∑ v ∈ Zact,(L v).card ≤ (L z).card + (L zp).card:=by
   calc ∑ v ∈ Zact,(L v).card ≤ ∑ v ∈ ({z,zp}:Finset (Fin n)),(L v).card:=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (L z).card + (L zp).card:=Finset.sum_pair q39
  omega
 by_cases he0:s(z,zp) ∈ Ustar G C
 ·
  have qja:z ∈ MC:=Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf1.2.1,he0⟩
  have q9w:zp ∈ MD:=Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf1.2.2.1,he0⟩
  have qho:MC.card ≤ FacC.card + 1:=q5l.1 ⟨z,qja⟩
  have qcl:MD.card ≤ FacD.card + 1:=q7e.1 ⟨zp,q9w⟩
  have q7f:FacC.card + FacD.card ≤ (orN G C \ lam G C).card:=by
   rw [← Finset.card_union_of_disjoint q5j];exact Finset.card_le_card q5m
  by_cases qmw:(MD.erase zp).Nonempty
  ·
   let L:Fin n→ Finset (Fin n):=fun v=>if v = z then MD else if v = zp then MC.erase z else ∅
   have hLz:L z = MD:=by simp [L]
   have q5y:L zp = MC.erase z:=by simp [L,q39.symm]
   have q8w:∀ e ∈ Ustar G C,(∃ u ∈ L z,e = s(z,u))∨ (∃ u ∈ L zp,e = s(zp,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Finset.mem_union,z045,Finset.mem_image] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·left;exact ⟨d,by rw [hLz];exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd,he⟩,rfl⟩
    ·by_cases hcz:c = z
     ·subst hcz;left;exact ⟨zp,by rw [hLz];exact q9w,rfl⟩
     ·right;exact ⟨c,by rw [q5y];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc,he⟩⟩,Sym2.eq_swap⟩
    ·left;exact ⟨d,by rw [hLz];exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd,he⟩,rfl⟩
    ·by_cases hcz:c = z
     ·subst hcz;left;exact ⟨zp,by rw [hLz];exact q9w,rfl⟩
     ·right;exact ⟨c,by rw [q5y];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc,he⟩⟩,Sym2.eq_swap⟩
   have q55:=run_surgery L
    (fun u hu=>by rw [hLz] at hu;rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
    (fun u hu=>by rw [q5y] at hu;rcases Finset.mem_union.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
    q8w
   dsimp only at q55
   set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
   have qhp:(Zact \ Zhas).card ≤ 2:=by
    calc (Zact \ Zhas).card ≤ Zact.card:=Finset.card_le_card Finset.sdiff_subset
     _ ≤ ({z,zp}:Finset (Fin n)).card:=Finset.card_le_card (Finset.filter_subset _ _)
     _ = 2:=Finset.card_pair q39
   have qbi:(MC.erase z).card = MC.card - 1:=Finset.card_erase_of_mem qja
   rw [hLz,q5y,qbi] at q55
   by_cases q0m:centreless G C = ∅
   ·obtain ⟨m,q9x,qg4⟩:=z037 hL q01 hne q0y q00 q0m
    have q7g:m ∉ FacC ∪ FacD:=by
     intro hmF;rcases Finset.mem_union.mp hmF with h | h
     ·have:=q5i m h;omega
     ·have:=q1g m h;omega
    have q7h:FacC.card + FacD.card + 1 ≤ (orN G C \ lam G C).card:=by
     have qe9:insert m (FacC ∪ FacD) ⊆ orN G C \ lam G C:=Finset.insert_subset q9x q5m
     have qhq:=Finset.card_le_card qe9
     rw [Finset.card_insert_of_notMem q7g,Finset.card_union_of_disjoint q5j] at qhq
     exact qhq
    have qhr:z ∈ Zhas:=by
     have qhs:z ∈ Zact:=Finset.mem_filter.mpr ⟨by simp,by rw [hLz];exact ⟨zp,q9w⟩⟩
     rw [Finset.mem_filter];refine ⟨qhs,?_⟩
     obtain ⟨d,hd⟩:=qmw
     have q1e:d ≠ zp:=(Finset.mem_erase.mp hd).1
     have qea:=Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)
     have qbj:s(z,d) ∈ Ustar G C:=qea.2
     have qos:G.Adj z d:=SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp qbj).1
     have q4k:¬ (gateVal n C g1 (pairInput z d) = true∧ gateVal n C g2 (pairInput z d) = true∧ 
       ∀ x,gateVal n C g1 x = true→ gateVal n C g2 x = true→ graphFun G ∅ x = true):=by
      rintro ⟨_,_,qaz⟩
      obtain ⟨c1,hc1,q87⟩:=z049 hf1
      obtain ⟨d1,hd1,q6i⟩:=z050 hf1
      obtain ⟨c2,hc2,q6x⟩:=z049 hf2
      obtain ⟨d2,hd2,q8y⟩:=z050 hf2
      let x:Fin n→ Bool:=fun w=>decide (w = c1∨ w = d1∨ w = c2∨ w = d2)
      have q1o:gateVal n C g1 x = true:=by
       rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
       exact ⟨⟨c1,hc1,by simp [x]⟩,⟨d1,hd1,by simp [x]⟩⟩
      have ql3:gateVal n C g2 x = true:=by
       rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
       exact ⟨⟨c2,hc2,by simp [x]⟩,⟨d2,hd2,by simp [x]⟩⟩
      have hFx:=(z073 x).mp (qaz x q1o ql3)
      rcases hFx with ⟨a,b,hab,ha,hb⟩
      simp only [x,decide_eq_true_eq] at ha hb
      have q9y:s c1 = s z:=z046 q03 hf1 hc1
      have q9z:s c2 = s z:=z046 q03 hf2 hc2
      have qa0:s d1 = s zp:=z047 q03 hf1 hd1
      have qa1:s d2 = s zp:=z047 q03 hf2 hd2
      have q3y:∀ c d',(c = c1∨ c = c2)→ (d' = d1∨ d' = d2)→ ¬ G.Adj c d':=by
       intro c d' hc hd' qk9
       have qot:c ≠ z:=hc.elim (fun h=>h ▸ q87) (fun h=>h ▸ q6x)
       have ql4:d' ≠ zp:=hd'.elim (fun h=>h ▸ q6i) (fun h=>h ▸ q8y)
       have qbk:G.Adj c zp:=hc.elim (fun h=>h ▸ hf1.2.2.2.1 c1 hc1) (fun h=>h ▸ hf2.2.2.2.1 c2 hc2)
       have hdz:G.Adj d' z:=hd'.elim (fun h=>h ▸ hf1.2.2.2.2.1 d1 hd1) (fun h=>h ▸ hf2.2.2.2.2.1 d2 hd2)
       exact ql4 (z102 h4 qot qk9 hdz.symm qbk hf1.1)
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inl rfl) hab
      ·exact q03 _ _ hab (q9y.trans q9z.symm)
      ·exact q3y _ _ (Or.inl rfl) (Or.inr rfl) hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inl rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inr rfl) (Or.inl rfl) hab.symm
      ·exact q03 _ _ hab (qa0.trans qa1.symm)
      ·exact q03 _ _ hab (q9z.trans q9y.symm)
      ·exact q3y _ _ (Or.inr rfl) (Or.inl rfl) hab
      ·exact G.loopless.irrefl _ hab
      ·exact q3y _ _ (Or.inr rfl) (Or.inr rfl) hab
      ·exact q3y _ _ (Or.inl rfl) (Or.inr rfl) hab.symm
      ·exact q03 _ _ hab (qa1.trans qa0.symm)
      ·exact q3y _ _ (Or.inr rfl) (Or.inr rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
     have hnw:
       (gateVal n C g1 (pairInput z d) = true→ 
        (¬ ∀ x,gateVal n C g1 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
        (∀ w:Fin n,s w = s z→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d))∧ 
       (gateVal n C g2 (pairInput z d) = true→ 
        (¬ ∀ x,gateVal n C g2 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
        (∀ w:Fin n,s w = s z→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d)):=by
      constructor
      ·intro h1
       have hd1:d ∈ D1:=by
        rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
        rcases h1.2 with ⟨d',hd',q3x⟩
        simp only [pairInput,decide_eq_true_eq] at q3x
        rcases q3x with rfl | rfl
        ·exact absurd (z047 q03 hf1 hd') (q03 _ zp hf1.1)
        ·exact hd'
       exact ⟨z056 h4 hf1 hd1 q1e,
        fun w hsw hw=>z054 q03 h4 hf1 hw hsw hd1 q1e⟩
      ·intro h2
       have hd2:d ∈ D2:=by
        rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h2
        rcases h2.2 with ⟨d',hd',q3x⟩
        simp only [pairInput,decide_eq_true_eq] at q3x
        rcases q3x with rfl | rfl
        ·exact absurd (z047 q03 hf2 hd') (q03 _ zp hf2.1)
        ·exact hd'
       exact ⟨z056 h4 hf2 hd2 q1e,
        fun w hsw hw=>z054 q03 h4 hf2 hw hsw hd2 q1e⟩
     rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl rfl qbj hnw q4k with
      hA | ⟨a,haC,_⟩ | ⟨qa2,_⟩
     ·exact hA
     ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     ·exact absurd qa2 (q03 z zp hf1.1)
    have q6j:(Zact \ Zhas).card ≤ 1:=by
     have q3e:Zact \ Zhas ⊆ {zp}:=by
      intro v hv
      have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      have hv2:=(Finset.mem_sdiff.mp hv).2
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h=>hv2 (h ▸ qhr))
     exact (Finset.card_le_card q3e).trans (by simp)
    omega
   ·have qa3:1 ≤ (centreless G C).card:=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr q0m)
    omega
  ·
   have q88:MD = {zp}:=by
    ext d;simp only [Finset.mem_singleton]
    constructor
    ·intro hd;by_contra qay
     exact qmw ⟨d,Finset.mem_erase.mpr ⟨qay,hd⟩⟩
    ·rintro rfl;exact q9w
   let L:Fin n→ Finset (Fin n):=fun v=>if v = zp then MC else ∅
   have hLz:L z = ∅:=by simp [L,q39]
   have q5y:L zp = MC:=by simp [L]
   have q8w:∀ e ∈ Ustar G C,(∃ u ∈ L z,e = s(z,u))∨ (∃ u ∈ L zp,e = s(zp,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Finset.mem_union,z045,Finset.mem_image] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·have qbl:d ∈ MD:=Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd,he⟩
     rw [q88,Finset.mem_singleton] at qbl;subst qbl
     right;exact ⟨z,by rw [q5y];exact qja,Sym2.eq_swap⟩
    ·right;exact ⟨c,by rw [q5y];exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc,he⟩,Sym2.eq_swap⟩
    ·have qbl:d ∈ MD:=Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd,he⟩
     rw [q88,Finset.mem_singleton] at qbl;subst qbl
     right;exact ⟨z,by rw [q5y];exact qja,Sym2.eq_swap⟩
    ·right;exact ⟨c,by rw [q5y];exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc,he⟩,Sym2.eq_swap⟩
   have q55:=run_surgery L
    (fun u hu=>by rw [hLz] at hu;exact absurd hu (Finset.notMem_empty _))
    (fun u hu=>by rw [q5y] at hu;rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
    q8w
   dsimp only at q55
   set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
   have q6j:(Zact \ Zhas).card ≤ 1:=by
    have q3e:Zact \ Zhas ⊆ {zp}:=by
     intro v hv
     have hv1:=Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
     simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
     rcases hv1.1 with rfl | rfl
     ·rw [hLz] at hv1;exact absurd hv1.2 (by simp)
     ·rfl
    exact (Finset.card_le_card q3e).trans (by simp)
   rw [hLz,q5y,Finset.card_empty,zero_add] at q55
   have qjb:FacC.card ≤ (orN G C \ lam G C).card:=
    Finset.card_le_card (Finset.filter_subset _ _)
   by_cases q0m:centreless G C = ∅
   ·obtain ⟨m,q9x,qg4⟩:=z037 hL q01 hne q0y q00 q0m
    have q7g:m ∉ FacC:=fun h=>by have:=q5i m h;omega
    have q7h:FacC.card + 1 ≤ (orN G C \ lam G C).card:=by
     have qe9:=Finset.insert_subset q9x (Finset.filter_subset _ _:FacC ⊆ orN G C \ lam G C)
     have qhq:=Finset.card_le_card qe9
     rw [Finset.card_insert_of_notMem q7g] at qhq;exact qhq
    omega
   ·have qa3:1 ≤ (centreless G C).card:=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr q0m)
    omega
 ·
  have qht:z ∉ MC:=fun h=>he0 (Finset.mem_filter.mp h).2
  have qeb:zp ∉ MD:=fun h=>he0 (Finset.mem_filter.mp h).2
  have qho:MC.card ≤ FacC.card:=q5l.2.1 qht
  have qcl:MD.card ≤ FacD.card:=q7e.2.1 qeb
  have q7f:FacC.card + FacD.card ≤ (orN G C \ lam G C).card:=by
   rw [← Finset.card_union_of_disjoint q5j];exact Finset.card_le_card q5m
  have qbm:s(z,zp) ∈ starEdges G C:=by
   by_contra hns
   exact he0 (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hf1.1,hns⟩)
  obtain ⟨a0,qmx,qhu⟩:=z127 hL.1 h4 s z g1 g2 qbm
  let L:Fin n→ Finset (Fin n):=fun v=>if v = z then MD else if v = zp then MC else ∅
  have hLz:L z = MD:=by simp [L]
  have q5y:L zp = MC:=by simp [L,q39.symm]
  have q8w:∀ e ∈ Ustar G C,(∃ u ∈ L z,e = s(z,u))∨ (∃ u ∈ L zp,e = s(zp,u)):=by
   intro e he
   have heF:=q5n he
   simp only [Finset.mem_union,z045,Finset.mem_image] at heF
   rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
   ·left;exact ⟨d,by rw [hLz];exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd,he⟩,rfl⟩
   ·right;exact ⟨c,by rw [q5y];exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc,he⟩,Sym2.eq_swap⟩
   ·left;exact ⟨d,by rw [hLz];exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd,he⟩,rfl⟩
   ·right;exact ⟨c,by rw [q5y];exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc,he⟩,Sym2.eq_swap⟩
  have q55:=run_surgery L
   (fun u hu=>by rw [hLz] at hu;rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
   (fun u hu=>by rw [q5y] at hu;rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h;exact (hf1.2.2.2.1 u h).symm;exact (hf2.2.2.2.1 u h).symm)
   q8w
  dsimp only at q55
  set Zact:=({z,zp}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
  set Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
  have q6j:(Zact \ Zhas).card ≤ 1:=by
   rcases qhu with qhv | qec
   ·have q3e:Zact \ Zhas ⊆ {zp}:=by
     intro v hv
     have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
     have hv2:=(Finset.mem_sdiff.mp hv).2
     simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,a0,qmx,qhv⟩) hv2
     ·rfl
    exact (Finset.card_le_card q3e).trans (by simp)
   ·have q3e:Zact \ Zhas ⊆ {z}:=by
     intro v hv
     have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
     have hv2:=(Finset.mem_sdiff.mp hv).2
     simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·rfl
     ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,a0,qmx,qec⟩) hv2
    exact (Finset.card_le_card q3e).trans (by simp)
  rw [hLz,q5y] at q55
  omega
lemma z014 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C) (hne:∃ u v:Fin n,G.Adj u v)
  {g1 g2:ℕ} (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {w:ℕ} (q53:w < n + C.gates.length) (q76:∀ k,w = n + k→ ¬ BelowF G C k)
  {u v:Fin n} (hu:u ∈ orIn n C w) (hv:v ∈ orIn n C w) (qa2:s u ≠ s v)
  (FacAll:Finset ℕ) (qa4:∀ k ∈ FacAll,∀ x y,x ∈ orIn n C (n + k)→ y ∈ orIn n C (n + k)→ s x = s y):
  ∃ m ∈ orN G C \ lam G C,m ∉ FacAll∧ 2 ≤ (orIn n C (n + m)).card:=by
 have huv:u ≠ v:=fun h=>qa2 (h ▸ rfl)
 let A:Finset (Fin n):={u,v}
 have q2n:∀ k,OrReaches n C w k→ k ∈ lam G C ∪ FacAll→ (orIn n C (n + k) ∩ A).card ≤ 1:=by
  intro k _ hk
  by_contra hgt;push Not at hgt
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp hgt
  have hx':=Finset.mem_inter.mp hx
  have hy':=Finset.mem_inter.mp hy
  have qou:s x ≠ s y:=by
   simp only [A,Finset.mem_insert,Finset.mem_singleton] at hx' hy'
   rcases hx'.2 with rfl | rfl <;> rcases hy'.2 with rfl | rfl
   ·exact absurd rfl hxy
   ·exact qa2
   ·exact qa2.symm
   ·exact absurd rfl hxy
  rcases Finset.mem_union.mp hk with qa5 | q6y
  ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨a,ha,b,q0t,hr⟩
   obtain ⟨c,hc⟩:=Finset.card_eq_one.mp q0t
   have q0c:=z109 hr
   have hcm:c ∈ side (n:=n) C a (1 - b):=by rw [hc];simp
   have hax:G.Adj c x:=by
    fin_cases b
    ·exact (z132 hL.1 ha (q0c hx'.1) hcm).symm
    ·exact z132 hL.1 ha hcm (q0c hx'.1)
   have hay:G.Adj c y:=by
    fin_cases b
    ·exact (z132 hL.1 ha (q0c hy'.1) hcm).symm
    ·exact z132 hL.1 ha hcm (q0c hy'.1)
   have h1:=q03 c x hax
   have h2:=q03 c y hay
   cases sc:s c <;> cases sx:s x <;> cases sy:s y <;> simp_all
  ·exact qou (qa4 k q6y x y hx'.1 hy'.1)
 have hwb:=z136 hL q01 hne q00 q53 q76 A ⟨u,by simp [A]⟩
  (fun x hx=>by simp only [A,Finset.mem_insert,Finset.mem_singleton] at hx;rcases hx with rfl | rfl <;> assumption)
  FacAll q2n
 rw [Finset.card_pair huv] at hwb
 have qov:((orN G C \ lam G C).filter (fun k=>
   OrReaches n C w k∧ k ∉ FacAll∧ 2 ≤ (orIn n C (n + k) ∩ A).card)).Nonempty:=
  Finset.card_pos.mp (by omega)
 obtain ⟨m,hm⟩:=qov
 have hmf:=Finset.mem_filter.mp hm
 exact ⟨m,hmf.1,hmf.2.2.1,le_trans hmf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
lemma z021 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z zp1 zp2:Fin n} (q0h:zp1 ≠ zp2)
  (hf1:z000 G C g1 C1 D1 z zp1) (hf2:z000 G C g2 C2 D2 z zp2):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z,zp1,hf1.1⟩
 have qdf:g1 ≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q1l:s zp1 = s zp2:=by
  have h1:=q03 z zp1 hf1.1
  have h2:=q03 z zp2 hf2.1
  cases sz:s z <;> cases s1:s zp1 <;> cases s2:s zp2 <;> simp_all
 have q2s:z ≠ zp1:=G.ne_of_adj hf1.1
 have q2t:z ≠ zp2:=G.ne_of_adj hf2.1
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 rfl q1l
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 have q4l:¬ OrReaches n C w1C g1:=by fin_cases b1 <;> assumption
 have q7i:¬ OrReaches n C w1C g2:=by fin_cases b1 <;> assumption
 have q4m:¬ OrReaches n C w1D g1:=by fin_cases b1 <;> assumption
 have q7j:¬ OrReaches n C w1D g2:=by fin_cases b1 <;> assumption
 have q2x:¬ OrReaches n C w2C g1:=fun h=>q0h (q6h h).2.1
 have q7k:¬ OrReaches n C w2C g2:=by fin_cases b2 <;> assumption
 have q7l:¬ OrReaches n C w2D g2:=by fin_cases b2 <;> assumption
 have q4n:orIn n C w2C = C2:=q3k q2x
 set MC1:=C1.filter (fun c=>s(c,zp1) ∈ Ustar G C)
 set MC2:=C2.filter (fun c=>s(c,zp2) ∈ Ustar G C)
 set MD1:=D1.filter (fun d=>s(z,d) ∈ Ustar G C)
 set MD2:=D2.filter (fun d=>s(z,d) ∈ Ustar G C)
 set MD:=MD1 ∪ MD2
 set FacC1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k)
 set FacC2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2C k)
 set FacD:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k∨ OrReaches n C w2D k)
 have q2q:∀ a,a ∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b = n + m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have q1w:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n + g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1) q4l
  (show orIn n C w1C = C1 from qci) (fun u hu=>(hf1.2.2.2.1 u hu).symm)
 have q1h:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 b2)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2) q2x
  q4n (fun u hu=>(hf2.2.2.2.1 u hu).symm)
 have qa6:C1.filter (fun u=>s(zp1,u) ∈ Ustar G C) = MC1:=by ext u;simp [MC1,Sym2.eq_swap]
 have qa7:C2.filter (fun u=>s(zp2,u) ∈ Ustar G C) = MC2:=by ext u;simp [MC2,Sym2.eq_swap]
 dsimp only at q1w q1h
 rw [qa6] at q1w
 rw [qa7] at q1h
 have ql5:(MC1.erase z).card ≤ FacC1.card:=by
  by_cases hzM:z ∈ MC1
  ·rw [Finset.card_erase_of_mem hzM];have h1:MC1.card ≤ FacC1.card + 1:=q1w.1 ⟨z,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM];exact q1w.2 ⟨z,hf1.2.1,hzM⟩
 have ql6:(MC2.erase z).card ≤ FacC2.card:=by
  by_cases hzM:z ∈ MC2
  ·rw [Finset.card_erase_of_mem hzM];have h2:MC2.card ≤ FacC2.card + 1:=q1h.1 ⟨z,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM];exact q1h.2 ⟨z,hf2.2.1,hzM⟩
 have q0j:∀ k ∈ FacC1,k < g2∧ ¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ C1∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk
  have hkf:=Finset.mem_filter.mp hk
  have hle:=z113 hkf.2
  have hlt:=z104 hL.1 q5x.1 b1
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q4l (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7i (z116 hkf.2 h)
  have q0c:orIn n C (n + k) ⊆ C1:=by
   have:=z109 hkf.2;rwa [show orIn n C w1C = C1 from qci] at this
  exact ⟨by omega,hn1,hn2,q0c,
   z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q0k:∀ k ∈ FacC2,k < g2∧ ¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ C2∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk
  have hkf:=Finset.mem_filter.mp hk
  have hle:=z113 hkf.2
  have hlt:=z104 hL.1 q2p.1 b2
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q2x (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7k (z116 hkf.2 h)
  have q0c:orIn n C (n + k) ⊆ C2:=by
   have:=z109 hkf.2;rwa [q4n] at this
  exact ⟨by omega,hn1,hn2,q0c,
   z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q1g:∀ k ∈ FacD,k < g2∧ orIn n C (n + k) ⊆ D1 ∪ D2:=by
  intro k hk
  rcases (Finset.mem_filter.mp hk).2 with h1 | h2
  ·have:=z113 h1;have:=z104 hL.1 q5x.1 (1 - b1)
   have q0c:=z109 h1
   rw [show orIn n C w1D = D1 from qb0] at q0c
   exact ⟨by omega,Finset.Subset.trans q0c Finset.subset_union_left⟩
  ·have:=z113 h2;have:=z104 hL.1 q2p.1 (1 - b2)
   exact ⟨by omega,Finset.Subset.trans (z109 h2) (Finset.Subset.trans q2o Finset.subset_union_right)⟩
 have qa8:Disjoint FacC1 FacC2:=by
  rw [Finset.disjoint_left];intro k hk1 hk2
  have h1:=q0j k hk1
  have h2:=q0k k hk2
  obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by omega:1 < (orIn n C (n + k)).card)
  exact q0h (z102 h4 qd2
   (hf1.2.2.2.1 u1 (h1.2.2.2.1 hu1)) (hf1.2.2.2.1 u2 (h1.2.2.2.1 hu2))
   (hf2.2.2.2.1 u1 (h2.2.2.2.1 hu1)) (hf2.2.2.2.1 u2 (h2.2.2.2.1 hu2)))
 have qbn:Disjoint FacC1 FacD:=by
  rw [Finset.disjoint_left];intro k hk1 hkD
  have h1:=q0j k hk1
  have hD:=q1g k hkD
  obtain ⟨u,hu⟩:=Finset.card_pos.mp (by omega:0 < (orIn n C (n + k)).card)
  have hsc:=z046 q03 hf1 (h1.2.2.2.1 hu)
  have hsd:s u = s zp1:=by
   rcases Finset.mem_union.mp (hD.2 hu) with h | h
   ·exact z047 q03 hf1 h
   ·exact (z047 q03 hf2 h).trans q1l.symm
  exact q03 z zp1 hf1.1 (hsc.symm.trans hsd)
 have qbo:Disjoint FacC2 FacD:=by
  rw [Finset.disjoint_left];intro k hk2 hkD
  have h2:=q0k k hk2
  have hD:=q1g k hkD
  obtain ⟨u,hu⟩:=Finset.card_pos.mp (by omega:0 < (orIn n C (n + k)).card)
  have hsc:=z046 q03 hf2 (h2.2.2.2.1 hu)
  have hsd:s u = s zp1:=by
   rcases Finset.mem_union.mp (hD.2 hu) with h | h
   ·exact z047 q03 hf1 h
   ·exact (z047 q03 hf2 h).trans q1l.symm
  exact q03 z zp1 hf1.1 (hsc.symm.trans hsd)
 set FacAll:=FacC1 ∪ FacC2 ∪ FacD
 have q07:FacAll ⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.filter_subset _ _)
 have q13:FacAll.card = FacC1.card + FacC2.card + FacD.card:=by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨qbn,qbo⟩),
   Finset.card_union_of_disjoint qa8]
 have q0b:∀ k ∈ FacAll,k < g2:=by
  intro k hk;simp only [FacAll,Finset.mem_union] at hk
  rcases hk with (h | h) | h
  ·exact (q0j k h).1
  ·exact (q0k k h).1
  ·exact (q1g k h).1
 have q2b:∀ k ∈ FacAll,∀ x y,x ∈ orIn n C (n + k)→ y ∈ orIn n C (n + k)→ s x = s y:=by
  intro k hk x y hx hy;simp only [FacAll,Finset.mem_union] at hk
  rcases hk with (h | h) | h
  ·exact (z046 q03 hf1 ((q0j k h).2.2.2.1 hx)).trans
    (z046 q03 hf1 ((q0j k h).2.2.2.1 hy)).symm
  ·exact (z046 q03 hf2 ((q0k k h).2.2.2.1 hx)).trans
    (z046 q03 hf2 ((q0k k h).2.2.2.1 hy)).symm
  ·have hsD:∀ u ∈ D1 ∪ D2,s u = s zp1:=fun u hu=>by
    rcases Finset.mem_union.mp hu with h1 | h2
    ·exact z047 q03 hf1 h1
    ·exact (z047 q03 hf2 h2).trans q1l.symm
   exact (hsD x ((q1g k h).2 hx)).trans (hsD y ((q1g k h).2 hy)).symm
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have run_surgery3:∀ L:Fin n→ Finset (Fin n),
   (∀ u ∈ L z,G.Adj z u)→ (∀ u ∈ L zp1,G.Adj zp1 u)→ (∀ u ∈ L zp2,G.Adj zp2 u)→ 
   (∀ e ∈ Ustar G C,(∃ u ∈ L z,e = s(z,u))∨ (∃ u ∈ L zp1,e = s(zp1,u))∨ (∃ u ∈ L zp2,e = s(zp2,u)))→ 
   let Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
   let Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
   2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (L z).card + (L zp1).card + (L zp2).card + (Zact \ Zhas).card:=by
  intro L hLz hL1 hL2 q8w Zact Zhas
  let topOf:Fin n→ ℕ:=fun v=>
   if h:∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v then Classical.choose h else 0
  have qhl:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv=>(Finset.mem_filter.mp hv).2)
   (fun v hv u hu=>by
    have hv':=(Finset.mem_filter.mp hv).1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl | rfl
    ·exact hLz u hu
    ·exact hL1 u hu
    ·exact hL2 u hu)
   (fun e he=>by
    rcases q8w e he with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    ·exact ⟨z,Finset.mem_filter.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp1,Finset.mem_filter.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩
    ·exact ⟨zp2,Finset.mem_filter.mpr ⟨by simp,⟨u,hu⟩⟩,u,hu,rfl⟩)
   (fun v hv=>by
    have h:=(Finset.mem_filter.mp hv).2
    simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
   (fun v hv=>by
    have h:=(Finset.mem_filter.mp hv).2
    simp only [topOf,dif_pos h]
    have hsp:=Classical.choose_spec h
    have q3f:=z128 hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at q3f)
   (fun v1 hv1 v2 hv2 heq=>by
    have h1:=(Finset.mem_filter.mp hv1).2
    have h2:=(Finset.mem_filter.mp hv2).2
    simp only [topOf,dif_pos h1,dif_pos h2] at heq
    have qhm:=Classical.choose_spec h1
    have qhn:=Classical.choose_spec h2
    rw [← qhm.2,heq,qhn.2])
  have qe8:∑ v ∈ Zact,(L v).card ≤ (L z).card + (L zp1).card + (L zp2).card:=by
   calc ∑ v ∈ Zact,(L v).card ≤ ∑ v ∈ ({z,zp1,zp2}:Finset (Fin n)),(L v).card:=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (L z).card + (L zp1).card + (L zp2).card:=by
      rw [Finset.sum_insert (by simp [q2s,q2t]),Finset.sum_pair q0h];omega
  omega
 have q0l:∀ c1 ∈ MC1.erase z,
   (∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = zp1)∨ 
   (∃ a ∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g1∧ zp1 ∈ side (n:=n) C a (1 - b))∨ 
   (∃ mv ∈ orN G C \ lam G C,g2 < mv∧ orIn n C (n + mv) = {zp1}∧ 
    ∃ u':Fin n,s u' = s z∧ ∃ mu ∈ orN G C \ lam G C,OrReaches n C (n + mu) g1∧ orIn n C (n + mu) = {u'}):=by
  intro c1 hc1
  have q87:c1 ≠ z:=(Finset.mem_erase.mp hc1).1
  have q45:=Finset.mem_filter.mp (Finset.mem_of_mem_erase hc1)
  have hU:s(zp1,c1) ∈ Ustar G C:=by rw [Sym2.eq_swap];exact q45.2
  have hG:G.Adj zp1 c1:=(hf1.2.2.2.1 c1 q45.1).symm
  have q3a:gateVal n C g2 (pairInput zp1 c1) = false:=by
   rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf2 hG]
   simp only [z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff]
   rintro (⟨d,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
   ·exact q2s rfl
   ·exact q87 rfl
   ·exact absurd (z046 q03 hf2 hc).symm (q03 z _ hf1.1)
   ·exact q0h rfl
  have hnw:
    (gateVal n C g1 (pairInput zp1 c1) = true→ 
     (¬ ∀ x,gateVal n C g1 x = true→ x c1 = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s zp1→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c1))∧ 
    (gateVal n C g2 (pairInput zp1 c1) = true→ 
     (¬ ∀ x,gateVal n C g2 x = true→ x c1 = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s zp1→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c1)):=
   ⟨fun _=>⟨z055 h4 hf1 q45.1 q87,
    fun w hsw hw=>z053 q03 h4 hf1 hw hsw q45.1 q87⟩,
   fun h2=>by rw [q3a] at h2;cases h2⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l hU hnw
    (fun h=>by rw [q3a] at h;cases h.2.1) with
   hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,ql7⟩ | ⟨_,a,haS,b,g,hg,hgv,_,_,g',hg',q7a,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
  ·exact Or.inl hA
  ·have q56:g = g1:=hg.resolve_right (fun h=>by rw [h,q3a] at hgv;cases hgv)
   subst q56
   exact Or.inr (Or.inl ⟨a,haC,b,q0g,hrb,ql7⟩)
  ·have q56:g = g1:=hg.resolve_right (fun h=>by rw [h,q3a] at hgv;cases hgv)
   rw [q56] at q3j
   have qed:g' = g2:=hg'.resolve_left (by rw [q56] at q7a;exact q7a)
   rw [qed] at q38
   have q1r:g2 < mv:=by
    have hle:=z113 q38
    have qay:mv ≠ g2:=fun h=>by
     have h1:=(z096.mp (Finset.mem_sdiff.mp hmv).1).2.1
     rw [h,q2p.2.1] at h1;cases h1
    omega
   exact Or.inr (Or.inr ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩)
 have q0n:∀ c2 ∈ MC2.erase z,
   (∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = zp2)∨ 
   (∃ a ∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g2∧ zp2 ∈ side (n:=n) C a (1 - b))∨ 
   (∃ mv ∈ orN G C \ lam G C,OrReaches n C (n + mv) g1∧ orIn n C (n + mv) = {zp2}∧ 
    ∃ u':Fin n,s u' = s z∧ ∃ mu ∈ orN G C \ lam G C,g2 < mu∧ orIn n C (n + mu) = {u'}):=by
  intro c2 hc2
  have q6x:c2 ≠ z:=(Finset.mem_erase.mp hc2).1
  have q46:=Finset.mem_filter.mp (Finset.mem_of_mem_erase hc2)
  have hU:s(zp2,c2) ∈ Ustar G C:=by rw [Sym2.eq_swap];exact q46.2
  have hG:G.Adj zp2 c2:=(hf2.2.2.2.1 c2 q46.1).symm
  have q3b:gateVal n C g1 (pairInput zp2 c2) = false:=by
   rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf1 hG]
   simp only [z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff]
   rintro (⟨d,_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨c,hc,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩)
   ·exact q2t rfl
   ·exact q6x rfl
   ·exact absurd ((z046 q03 hf1 hc).symm.trans q1l.symm) (q03 z zp1 hf1.1)
   ·exact q0h.symm rfl
  have hnw:
    (gateVal n C g1 (pairInput zp2 c2) = true→ 
     (¬ ∀ x,gateVal n C g1 x = true→ x c2 = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s zp2→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c2))∧ 
    (gateVal n C g2 (pairInput zp2 c2) = true→ 
     (¬ ∀ x,gateVal n C g2 x = true→ x c2 = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s zp2→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c2)):=
   ⟨fun h1=>(by rw [q3b] at h1;cases h1),
   fun _=>⟨z055 h4 hf2 q46.1 q6x,
    fun w hsw hw=>z053 q03 h4 hf2 hw hsw q46.1 q6x⟩⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l hU hnw
    (fun h=>by rw [q3b] at h;cases h.1) with
   hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,ql7⟩ | ⟨_,a,haS,b,g,hg,hgv,_,_,g',hg',q7a,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
  ·exact Or.inl hA
  ·have q56:g = g2:=hg.resolve_left (fun h=>by rw [h,q3b] at hgv;cases hgv)
   subst q56
   exact Or.inr (Or.inl ⟨a,haC,b,q0g,hrb,ql7⟩)
  ·have q56:g = g2:=hg.resolve_left (fun h=>by rw [h,q3b] at hgv;cases hgv)
   rw [q56] at q3j
   have qed:g' = g1:=hg'.resolve_right (by rw [q56] at q7a;exact q7a)
   rw [qed] at q38
   have q2c:g2 < mu:=by
    have hle:=z113 q3j
    have qay:mu ≠ g2:=fun h=>by
     have h1:=(z096.mp (Finset.mem_sdiff.mp hmu).1).2.1
     rw [h,q2p.2.1] at h1;cases h1
    omega
   exact Or.inr (Or.inr ⟨mv,hmv,q38,q05,u',q24,mu,hmu,q2c,q06⟩)
 have q2d:∀ d ∈ MD,d ≠ zp1→ d ≠ zp2→ 
   (∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = z)∨ 
   (∃ a ∈ centreless G C,∃ b:Fin 2,∃ g:ℕ,(g = g1∨ g = g2)∧ 
    gateVal n C g (pairInput z d) = true∧ 
    side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g∧ z ∈ side (n:=n) C a (1 - b)):=by
  intro d hd qee qef
  have qbj:s(z,d) ∈ Ustar G C:=by
   rcases Finset.mem_union.mp hd with h1 | h2
   ·exact (Finset.mem_filter.mp h1).2
   ·exact (Finset.mem_filter.mp h2).2
  have q4k:¬ (gateVal n C g1 (pairInput z d) = true∧ gateVal n C g2 (pairInput z d) = true∧ 
    ∀ x,gateVal n C g1 x = true→ gateVal n C g2 x = true→ graphFun G ∅ x = true):=by
   rintro ⟨qmy,qmz,qaz⟩
   have hd1:d ∈ D1:=by
    rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at qmy
    rcases qmy.2 with ⟨d',hd',q3x⟩
    simp only [pairInput,decide_eq_true_eq] at q3x
    rcases q3x with rfl | rfl
    ·exact absurd (z047 q03 hf1 hd') (q03 _ zp1 hf1.1)
    ·exact hd'
   have hd2:d ∈ D2:=by
    rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at qmz
    rcases qmz.2 with ⟨d',hd',q3x⟩
    simp only [pairInput,decide_eq_true_eq] at q3x
    rcases q3x with rfl | rfl
    ·exact absurd (z047 q03 hf2 hd') (q03 _ zp2 hf2.1)
    ·exact hd'
   obtain ⟨c1,hc1,q87⟩:=z049 hf1
   obtain ⟨c2,hc2,q6x⟩:=z049 hf2
   let x:Fin n→ Bool:=fun w=>decide (w = c1∨ w = c2∨ w = d)
   have q1o:gateVal n C g1 x = true:=by
    rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
    exact ⟨⟨c1,hc1,by simp [x]⟩,⟨d,hd1,by simp [x]⟩⟩
   have ql3:gateVal n C g2 x = true:=by
    rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
    exact ⟨⟨c2,hc2,by simp [x]⟩,⟨d,hd2,by simp [x]⟩⟩
   have hFx:=(z073 x).mp (qaz x q1o ql3)
   rcases hFx with ⟨a,b,hab,ha,hb⟩
   simp only [x,decide_eq_true_eq] at ha hb
   have qn0:=z046 q03 hf1 hc1
   have qn1:=z046 q03 hf2 hc2
   have qhw:=z051 h4 hf1 hc1 q87 hd1 qee
   have qhx:=z051 h4 hf2 hc2 q6x hd2 qef
   rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
   ·exact G.loopless.irrefl _ hab
   ·exact q03 _ _ hab (qn0.trans qn1.symm)
   ·exact qhw hab
   ·exact q03 _ _ hab (qn1.trans qn0.symm)
   ·exact G.loopless.irrefl _ hab
   ·exact qhx hab
   ·exact qhw hab.symm
   ·exact qhx hab.symm
   ·exact G.loopless.irrefl _ hab
  have hnw:
    (gateVal n C g1 (pairInput z d) = true→ 
     (¬ ∀ x,gateVal n C g1 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s z→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d))∧ 
    (gateVal n C g2 (pairInput z d) = true→ 
     (¬ ∀ x,gateVal n C g2 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
     (∀ w:Fin n,s w = s z→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d)):=by
   constructor
   ·intro h1
    have hd1:d ∈ D1:=by
     rw [hf1.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,decide_eq_true_eq] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd (z047 q03 hf1 hd') (q03 _ zp1 hf1.1)
     ·exact hd'
    exact ⟨z056 h4 hf1 hd1 qee,
     fun w hsw hw=>z054 q03 h4 hf1 hw hsw hd1 qee⟩
   ·intro h2
    have hd2:d ∈ D2:=by
     rw [hf2.2.2.2.2.2.2.2,Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq] at h2
     rcases h2.2 with ⟨d',hd',q3x⟩
     simp only [pairInput,decide_eq_true_eq] at q3x
     rcases q3x with rfl | rfl
     ·exact absurd (z047 q03 hf2 hd') (q03 _ zp2 hf2.1)
     ·exact hd'
    exact ⟨z056 h4 hf2 hd2 qef,
     fun w hsw hw=>z054 q03 h4 hf2 hw hsw hd2 qef⟩
  rcases z072 q03 h4 hL q01 q00 hf1 hf2 rfl q1l qbj hnw q4k with
   hA | hB | ⟨qa2,_⟩
  ·exact Or.inl hA
  ·exact Or.inr hB
  ·exact absurd qa2 (q03 z zp1 hf1.1)
 have close_slack1:MD.card + (MC1.erase z).card + (MC2.erase z).card ≤ FacAll.card + 1→ False:=by
  intro qjc
  let L1:Fin n→ Finset (Fin n):=fun v=>
   if v = z then MD else if v = zp1 then MC1.erase z else if v = zp2 then MC2.erase z else ∅
  have q8z:L1 z = MD:=by simp [L1]
  have q5o:L1 zp1 = MC1.erase z:=by simp [L1,q2s.symm]
  have q5p:L1 zp2 = MC2.erase z:=by simp [L1,q2t.symm,q0h.symm]
  have qeg:∀ e ∈ Ustar G C,(∃ u ∈ L1 z,e = s(z,u))∨ (∃ u ∈ L1 zp1,e = s(zp1,u))∨ (∃ u ∈ L1 zp2,e = s(zp2,u)):=by
   intro e he
   have heF:=q5n he
   simp only [Finset.mem_union,z045,Finset.mem_image] at heF
   rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
   ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,he⟩),rfl⟩
   ·by_cases hcz:c = z
    ·subst hcz;left;exact ⟨zp1,by rw [q8z];exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1,he⟩),rfl⟩
    ·right;left;exact ⟨c,by rw [q5o];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
   ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd,he⟩),rfl⟩
   ·by_cases hcz:c = z
    ·subst hcz;left;exact ⟨zp2,by rw [q8z];exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1,he⟩),rfl⟩
    ·right;right;exact ⟨c,by rw [q5p];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
  have q6k:=run_surgery3 L1
   (fun u hu=>by rw [q8z] at hu;rcases Finset.mem_union.mp hu with h | h;exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm;exact (hf2.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm)
   (fun u hu=>by rw [q5o] at hu;exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
   (fun u hu=>by rw [q5p] at hu;exact (hf2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
   qeg
  dsimp only at q6k
  set Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L1 v).Nonempty)
  set Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
  rw [q8z,q5o,q5p] at q6k
  have q7f:FacAll.card ≤ (orN G C \ lam G C).card:=Finset.card_le_card q07
  have qa9:(Zact \ Zhas).card ≤ 3:=by
   calc (Zact \ Zhas).card ≤ ({z,zp1,zp2}:Finset (Fin n)).card:=
      Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
    _ = 3:=by rw [Finset.card_insert_of_notMem (by simp [q2s,q2t]),Finset.card_pair q0h]
  by_cases qaa:2 ≤ (centreless G C).card
  ·omega
  ·by_cases q6l:(centreless G C).card = 1
   ·
    by_cases hZ3:(Zact \ Zhas).card ≤ 2
    ·omega
    ·have q6m:Zact \ Zhas = {z,zp1,zp2}:=by
      apply Finset.eq_of_subset_of_card_le
      ·exact Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _)
      ·rw [Finset.card_insert_of_notMem (by simp [q2s,q2t]),Finset.card_pair q0h];omega
     have q08:zp1 ∈ Zact \ Zhas:=by rw [q6m];simp
     have q0e:zp2 ∈ Zact \ Zhas:=by rw [q6m];simp
     obtain ⟨c1,hc1⟩:(MC1.erase z).Nonempty:=by
      have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q08).1).2;rwa [q5o] at this
     obtain ⟨c2,hc2⟩:(MC2.erase z).Nonempty:=by
      have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q0e).1).2;rwa [q5p] at this
     have qhy:∃ m ∈ orN G C \ lam G C,g2 < m:=by
      rcases q0l c1 hc1 with hA1 | ⟨a1,qeh,b1',qbp,qjd,q40⟩ | ⟨mv,hmv,q1r,_⟩
      ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA1⟩) (Finset.mem_sdiff.mp q08).2
      ·rcases q0n c2 hc2 with hA2 | ⟨a2,qhz,b2',qbq,qje,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA2⟩) (Finset.mem_sdiff.mp q0e).2
       ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
        have qei:a1 = a0:=Finset.mem_singleton.mp (ha0 ▸ qeh)
        have qej:a2 = a0:=Finset.mem_singleton.mp (ha0 ▸ qhz)
        rw [qei] at qeh qbp qjd q40
        rw [qej] at qbq qje
        have ql8:b1' = b2':=by
         by_contra q2e
         have q51:1 - b1' = b2':=z044 q2e
         rw [q51,qbq] at q40;exact Finset.notMem_empty _ q40
        subst ql8
        have q1x:a0 ∈ tops G C:=(Finset.mem_filter.mp qeh).1
        have qek:=z098.mp q1x
        obtain ⟨m,hm,qg4,_⟩:=z122 hL q0y q00
         (by have:=z104 hL.1 qek.1 b1';omega) (z130 hL hne q1x b1')
         qbp qjd qje
        exact ⟨m,hm,qg4⟩
       ·exact ⟨mu,hmu,q2c⟩
      ·exact ⟨mv,hmv,q1r⟩
     obtain ⟨m,hm,qg4⟩:=qhy
     have qel:m ∉ FacAll:=fun h=>by have:=q0b m h;omega
     have qcm:FacAll.card + 1 ≤ (orN G C \ lam G C).card:=by
      have:=Finset.card_le_card (Finset.insert_subset hm q07)
      rwa [Finset.card_insert_of_notMem qel] at this
     omega
   ·
    have q0m:centreless G C = ∅:=Finset.card_eq_zero.mp (by omega)
    obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q0m
    have qab:m0 ∉ FacAll:=fun h=>by have:=q0b m0 h;omega
    have q5q:FacAll.card + 1 ≤ (orN G C \ lam G C).card:=by
     have:=Finset.card_le_card (Finset.insert_subset hm0 q07)
     rwa [Finset.card_insert_of_notMem qab] at this
    by_cases q2f:∃ d ∈ MD,d ≠ zp1∧ d ≠ zp2
    ·obtain ⟨d,hd,hd1,hd2⟩:=q2f
     have qac:∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = z:=by
      rcases q2d d hd hd1 hd2 with hA | ⟨a,haC,_⟩
      ·exact hA
      ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     have q7m:z ∉ Zact \ Zhas:=fun h=>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1,qac⟩)
     have q5d:Zact \ Zhas ⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h=>q7m (h ▸ hv))
     have ql9:(Zact \ Zhas).card ≤ 2:=(Finset.card_le_card q5d).trans (by rw [Finset.card_pair q0h])
     by_cases qla:(Zact \ Zhas).card ≤ 1
     ·omega
     ·have qi0:Zact \ Zhas = {zp1,zp2}:=
       Finset.eq_of_subset_of_card_le q5d (by rw [Finset.card_pair q0h];omega)
      have q08:zp1 ∈ Zact \ Zhas:=by rw [qi0];simp
      have q0e:zp2 ∈ Zact \ Zhas:=by rw [qi0];simp
      obtain ⟨c1,hc1⟩:(MC1.erase z).Nonempty:=by
       have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q08).1).2;rwa [q5o] at this
      obtain ⟨c2,hc2⟩:(MC2.erase z).Nonempty:=by
       have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q0e).1).2;rwa [q5p] at this
      obtain ⟨m1,hm1,qi1,q1i⟩:∃ m1 ∈ orN G C \ lam G C,g2 < m1∧ orIn n C (n + m1) = {zp1}:=by
       rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,_⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
       ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mv,hmv,q1r,q05⟩
      obtain ⟨m2,hm2,qi2,u',q24,q16⟩:
        ∃ m2 ∈ orN G C \ lam G C,g2 < m2∧ ∃ u':Fin n,s u' = s z∧ orIn n C (n + m2) = {u'}:=by
       rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | ⟨_,_,_,_,u',q24,mu,hmu,q2c,q06⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA⟩) (Finset.mem_sdiff.mp q0e).2
       ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mu,hmu,q2c,u',q24,q06⟩
      have qem:m1 ≠ m2:=by
       intro heq;subst heq
       rw [q1i] at q16
       have q7n:zp1 = u':=Finset.singleton_injective q16
       exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s q7n.symm))
      have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
       rw [Finset.disjoint_left];intro k hk hkf
       simp only [Finset.mem_insert,Finset.mem_singleton] at hk
       have:=q0b k hkf
       rcases hk with rfl | rfl <;> omega
      have q57:{m1,m2} ∪ FacAll ⊆ orN G C \ lam G C:=
       Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07
      have q2g:=Finset.card_le_card q57
      rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
      omega
    ·
     push Not at q2f
     let L2:Fin n→ Finset (Fin n):=fun v=>
      if v = zp1 then MC1 else if v = zp2 then MC2 else ∅
     have qlb:L2 z = ∅:=by simp [L2,q2s,q2t]
     have q7o:L2 zp1 = MC1:=by simp [L2]
     have q7p:L2 zp2 = MC2:=by simp [L2,q0h.symm]
     have qlc:∀ e ∈ Ustar G C,(∃ u ∈ L2 z,e = s(z,u))∨ (∃ u ∈ L2 zp1,e = s(zp1,u))∨ (∃ u ∈ L2 zp2,e = s(zp2,u)):=by
      intro e he
      have heF:=q5n he
      simp only [Finset.mem_union,z045,Finset.mem_image] at heF
      rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
      ·have qbl:d ∈ MD:=Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,he⟩)
       by_cases hd1:d = zp1
       ·subst hd1;right;left;exact ⟨z,by rw [q7o];exact Finset.mem_filter.mpr ⟨hf1.2.1,he⟩,Sym2.eq_swap⟩
       ·have hd2:d = zp2:=q2f d qbl hd1
        subst hd2;right;right;exact ⟨z,by rw [q7p];exact Finset.mem_filter.mpr ⟨hf2.2.1,he⟩,Sym2.eq_swap⟩
      ·right;left;exact ⟨c,by rw [q7o];exact Finset.mem_filter.mpr ⟨hc,he⟩,Sym2.eq_swap⟩
      ·have qbl:d ∈ MD:=Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd,he⟩)
       by_cases hd1:d = zp1
       ·subst hd1;right;left;exact ⟨z,by rw [q7o];exact Finset.mem_filter.mpr ⟨hf1.2.1,he⟩,Sym2.eq_swap⟩
       ·have hd2:d = zp2:=q2f d qbl hd1
        subst hd2;right;right;exact ⟨z,by rw [q7p];exact Finset.mem_filter.mpr ⟨hf2.2.1,he⟩,Sym2.eq_swap⟩
      ·right;right;exact ⟨c,by rw [q7p];exact Finset.mem_filter.mpr ⟨hc,he⟩,Sym2.eq_swap⟩
     have qco:=run_surgery3 L2
      (fun u hu=>by rw [qlb] at hu;exact absurd hu (Finset.notMem_empty _))
      (fun u hu=>by rw [q7o] at hu;exact (hf1.2.2.2.1 u (Finset.mem_filter.mp hu).1).symm)
      (fun u hu=>by rw [q7p] at hu;exact (hf2.2.2.2.1 u (Finset.mem_filter.mp hu).1).symm)
      qlc
     dsimp only at qco
     set Zact2:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L2 v).Nonempty)
     set Zhas2:=Zact2.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
     rw [qlb,q7o,q7p,Finset.card_empty,zero_add] at qco
     have qcp:Zact2 \ Zhas2 ⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
      rcases hv1.1 with rfl | rfl | rfl
      ·rw [qlb] at hv1;exact absurd hv1.2 (by simp)
      ·exact Or.inl rfl
      ·exact Or.inr rfl
     have qn2:(Zact2 \ Zhas2).card ≤ 2:=(Finset.card_le_card qcp).trans (by rw [Finset.card_pair q0h])
     have q7q:MD.card = (if z ∈ MC1 then 1 else 0) + (if z ∈ MC2 then 1 else 0):=by
      have q88:MD = ({zp1,zp2}:Finset (Fin n)).filter (fun d=>s(z,d) ∈ Ustar G C):=by
       ext d;constructor
       ·intro hd
        have qn3:s(z,d) ∈ Ustar G C:=by
         rcases Finset.mem_union.mp hd with h | h <;> exact (Finset.mem_filter.mp h).2
        by_cases h1:d = zp1
        ·subst h1;exact Finset.mem_filter.mpr ⟨by simp,qn3⟩
        ·have h2:=q2f d hd h1;subst h2;exact Finset.mem_filter.mpr ⟨by simp,qn3⟩
       ·intro hd;have hdf:=Finset.mem_filter.mp hd
        simp only [Finset.mem_insert,Finset.mem_singleton] at hdf
        rcases hdf.1 with rfl | rfl
        ·exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1,hdf.2⟩)
        ·exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1,hdf.2⟩)
      rw [q88]
      have qi3:z ∈ MC1↔ s(z,zp1) ∈ Ustar G C:=by
       simp [MC1,hf1.2.1]
      have qi4:z ∈ MC2↔ s(z,zp2) ∈ Ustar G C:=by
       simp [MC2,hf2.2.1]
      rw [Finset.filter_insert,Finset.filter_singleton]
      by_cases h1:s(z,zp1) ∈ Ustar G C <;> by_cases h2:s(z,zp2) ∈ Ustar G C <;>
       simp [h1,h2,qi3,qi4,q0h]
     have qld:MC1.card + MC2.card = MD.card + (MC1.erase z).card + (MC2.erase z).card:=by
      rw [q7q]
      by_cases h1:z ∈ MC1 <;> by_cases h2:z ∈ MC2
      ·rw [Finset.card_erase_of_mem h1,Finset.card_erase_of_mem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h1⟩;have:=Finset.card_pos.mpr ⟨z,h2⟩;omega
      ·rw [Finset.card_erase_of_mem h1,Finset.erase_eq_of_notMem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h1⟩;omega
      ·rw [Finset.erase_eq_of_notMem h1,Finset.card_erase_of_mem h2];simp [h1,h2]
       have:=Finset.card_pos.mpr ⟨z,h2⟩;omega
      ·rw [Finset.erase_eq_of_notMem h1,Finset.erase_eq_of_notMem h2];simp [h1,h2]
     by_cases qn4:(Zact2 \ Zhas2).card ≤ 1
     ·omega
     ·have qcq:Zact2 \ Zhas2 = {zp1,zp2}:=
       Finset.eq_of_subset_of_card_le qcp (by rw [Finset.card_pair q0h];omega)
      have q08:zp1 ∈ Zact2 \ Zhas2:=by rw [qcq];simp
      have q0e:zp2 ∈ Zact2 \ Zhas2:=by rw [qcq];simp
      by_cases q62:(MC1.erase z).Nonempty
      ·by_cases qi5:(MC2.erase z).Nonempty
       ·obtain ⟨c1,hc1⟩:=q62
        obtain ⟨c2,hc2⟩:=qi5
        obtain ⟨m1,hm1,qi1,q1i⟩:∃ m1 ∈ orN G C \ lam G C,g2 < m1∧ orIn n C (n + m1) = {zp1}:=by
         rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,_⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mv,hmv,q1r,q05⟩
        obtain ⟨m2,hm2,qi2,u',q24,q16⟩:
          ∃ m2 ∈ orN G C \ lam G C,g2 < m2∧ ∃ u':Fin n,s u' = s z∧ orIn n C (n + m2) = {u'}:=by
         rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | ⟨_,_,_,_,u',q24,mu,hmu,q2c,q06⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA⟩) (Finset.mem_sdiff.mp q0e).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mu,hmu,q2c,u',q24,q06⟩
        have qem:m1 ≠ m2:=by
         intro heq;subst heq
         rw [q1i] at q16
         have q7n:zp1 = u':=Finset.singleton_injective q16
         exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s q7n.symm))
        have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
         rw [Finset.disjoint_left];intro k hk hkf
         simp only [Finset.mem_insert,Finset.mem_singleton] at hk
         have:=q0b k hkf
         rcases hk with rfl | rfl <;> omega
        have q57:{m1,m2} ∪ FacAll ⊆ orN G C \ lam G C:=
         Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07
        have q2g:=Finset.card_le_card q57
        rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
        omega
       ·
        have q3l:MC2.Nonempty:=by
         have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q0e).1).2;rwa [q7p] at this
        obtain ⟨c2,hc2,q6x⟩:=z049 hf2
        have qad:c2 ∉ MC2:=fun h=>qi5 ⟨c2,Finset.mem_erase.mpr ⟨q6x,h⟩⟩
        have qae:MC2.card ≤ FacC2.card:=q1h.2 ⟨c2,hc2,qad⟩
        have qen:MC1.card ≤ FacC1.card + 1:=q1w.1 (by
         have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q08).1).2;rwa [q7o] at this)
        obtain ⟨c1,hc1⟩:=q62
        obtain ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,qcr,q06⟩:
          ∃ mv ∈ orN G C \ lam G C,g2 < mv∧ orIn n C (n + mv) = {zp1}∧ 
           ∃ u':Fin n,s u' = s z∧ ∃ mu ∈ orN G C \ lam G C,OrReaches n C (n + mu) g1∧ orIn n C (n + mu) = {u'}:=by
         rcases q0l c1 hc1 with hA | ⟨a,haC,_⟩ | hC
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have qaf:mv ≠ mu:=by
         intro heq;subst heq;rw [q05] at q06
         exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s (Finset.singleton_injective q06).symm))
        have qi6:mv ∉ FacAll:=fun h=>by have:=q0b mv h;omega
        have q89:mu ∉ FacAll:=by
         intro h;simp only [FacAll,Finset.mem_union] at h
         rcases h with (h1 | h2) | hD
         ·exact (q0j mu h1).2.1 qcr
         ·exact (q0k mu h2).2.1 qcr
         ·have qle:u' ∈ D1 ∪ D2:=(q1g mu hD).2 (by rw [q06];simp)
          rcases Finset.mem_union.mp qle with h1 | h2
          ·exact q03 z zp1 hf1.1 (q24.symm.trans (z047 q03 hf1 h1))
          ·exact q03 z zp2 hf2.1 (q24.symm.trans (z047 q03 hf2 h2))
        have q0z:Disjoint ({mv,mu}:Finset ℕ) FacAll:=by
         rw [Finset.disjoint_left];intro k hk hkf
         simp only [Finset.mem_insert,Finset.mem_singleton] at hk
         rcases hk with rfl | rfl
         ·exact qi6 hkf
         ·exact q89 hkf
        have q2g:FacAll.card + 2 ≤ (orN G C \ lam G C).card:=by
         have q57:{mv,mu} ∪ FacAll ⊆ orN G C \ lam G C:=
          Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) q07
         have:=Finset.card_le_card q57
         rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qaf] at this
         omega
        omega
      ·
       have qlf:MC1.Nonempty:=by
        have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q08).1).2;rwa [q7o] at this
       obtain ⟨c1,hc1,q87⟩:=z049 hf1
       have qi7:c1 ∉ MC1:=fun h=>q62 ⟨c1,Finset.mem_erase.mpr ⟨q87,h⟩⟩
       have qen:MC1.card ≤ FacC1.card:=q1w.2 ⟨c1,hc1,qi7⟩
       by_cases qi5:(MC2.erase z).Nonempty
       ·have qae:MC2.card ≤ FacC2.card + 1:=q1h.1 (by
         have:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp q0e).1).2;rwa [q7p] at this)
        obtain ⟨c2,hc2⟩:=qi5
        obtain ⟨mv,hmv,qcs,q05,u',q24,mu,hmu,q2c,q06⟩:
          ∃ mv ∈ orN G C \ lam G C,OrReaches n C (n + mv) g1∧ orIn n C (n + mv) = {zp2}∧ 
           ∃ u':Fin n,s u' = s z∧ ∃ mu ∈ orN G C \ lam G C,g2 < mu∧ orIn n C (n + mu) = {u'}:=by
         rcases q0n c2 hc2 with hA | ⟨a,haC,_⟩ | hC
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA⟩) (Finset.mem_sdiff.mp q0e).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have q89:mu ∉ FacAll:=fun h=>by have:=q0b mu h;omega
        have qaf:mv ≠ mu:=by
         intro heq;subst heq;rw [q05] at q06
         exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s (Finset.singleton_injective q06).symm))
        have qjf:FacC1.card + FacC2.card + 2 ≤ (orN G C \ lam G C).card:=by
         by_cases qeo:mv ∈ FacAll
         ·have qlg:mv ∈ FacD:=by
           simp only [FacAll,Finset.mem_union] at qeo
           rcases qeo with (h1 | h2) | hD
           ·exact absurd qcs (q0j mv h1).2.1
           ·exact absurd qcs (q0k mv h2).2.1
           ·exact hD
          have qow:1 ≤ FacD.card:=Finset.card_pos.mpr ⟨mv,qlg⟩
          have qcm:FacAll.card + 1 ≤ (orN G C \ lam G C).card:=by
           have:=Finset.card_le_card (Finset.insert_subset hmu q07)
           rwa [Finset.card_insert_of_notMem q89] at this
          rw [q13] at qcm;omega
         ·have q0z:Disjoint ({mv,mu}:Finset ℕ) FacAll:=by
           rw [Finset.disjoint_left];intro k hk hkf
           simp only [Finset.mem_insert,Finset.mem_singleton] at hk
           rcases hk with rfl | rfl
           ·exact qeo hkf
           ·exact q89 hkf
          have q57:{mv,mu} ∪ FacAll ⊆ orN G C \ lam G C:=
           Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) q07
          have:=Finset.card_le_card q57
          rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qaf,q13] at this
          omega
        omega
       ·obtain ⟨c2,hc2,q6x⟩:=z049 hf2
        have qad:c2 ∉ MC2:=fun h=>qi5 ⟨c2,Finset.mem_erase.mpr ⟨q6x,h⟩⟩
        have qae:MC2.card ≤ FacC2.card:=q1h.2 ⟨c2,hc2,qad⟩
        omega
 by_cases qag:(D1 ∩ D2).Nonempty
 ·obtain ⟨d0,hd0⟩:=qag
  have qlh:=(Finset.mem_inter.mp hd0).1
  have qli:=(Finset.mem_inter.mp hd0).2
  have q5k:D1 ∪ D2 = D1 ∪ orIn n C w2D:=by
   by_cases hr:OrReaches n C w2D g1
   ·have h:=q5a hr;rw [Finset.union_eq_right.mpr h.1,h.2.2];rfl
   ·rw [show orIn n C w2D = D2 from q2a hr]
  have qep:d0 ∈ orIn n C w2D∨ OrReaches n C w2D g1:=by
   by_cases hr:OrReaches n C w2D g1
   ·exact Or.inr hr
   ·left;rw [show orIn n C w2D = D2 from q2a hr];exact qli
  have qeq:=z099 hL q01 h4 hne q00
   (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n + g2)
   (z104 hL.1 q2p.1 (1 - b2))
   (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1))
   (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2))
   (show orIn n C w1D = D1 from qb0) q2o q5k
   (fun u hu=>by rcases Finset.mem_union.mp hu with h | h;exact (hf1.2.2.2.2.1 u h).symm;exact (hf2.2.2.2.2.1 u h).symm)
   qlh qep
  have q7r:(D1 ∪ D2).filter (fun u=>s(z,u) ∈ Ustar G C) = MD:=by
   ext u;simp [MD,MD1,MD2,Finset.filter_union]
  dsimp only at qeq
  rw [q7r] at qeq
  have qcl:MD.card ≤ FacD.card + 1:=by
   by_cases qct:MD.Nonempty
   ·exact qeq.1 qct
   ·rw [Finset.not_nonempty_iff_eq_empty.mp qct];simp
  exact close_slack1 (by rw [q13];omega)
 ·
  have q4o:Disjoint D1 D2:=Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp qag)
  have q2y:¬ OrReaches n C w2D g1:=fun hr=>
   Finset.disjoint_left.mp q4o hf1.2.2.1 ((q5a hr).1 hf1.2.2.1)
  have q4p:orIn n C w2D = D2:=q2a q2y
  set FacD1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k)
  set FacD2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2D k)
  have q8a:FacD = FacD1 ∪ FacD2:=by ext k;simp [FacD,FacD1,FacD2,and_or_left]
  have q1y:∀ k ∈ FacD1,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
    orIn n C (n + k) ⊆ D1∧ 2 ≤ (orIn n C (n + k)).card:=by
   intro k hk
   have hkf:=Finset.mem_filter.mp hk
   have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q4m (z116 hkf.2 h)
   have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7j (z116 hkf.2 h)
   have q0c:orIn n C (n + k) ⊆ D1:=by
    have:=z109 hkf.2;rwa [show orIn n C w1D = D1 from qb0] at this
   exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
  have q2z:∀ k ∈ FacD2,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
    orIn n C (n + k) ⊆ D2∧ 2 ≤ (orIn n C (n + k)).card:=by
   intro k hk
   have hkf:=Finset.mem_filter.mp hk
   have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q2y (z116 hkf.2 h)
   have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7l (z116 hkf.2 h)
   have q0c:orIn n C (n + k) ⊆ D2:=by
    have:=z109 hkf.2;rwa [q4p] at this
   exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
  have qah:Disjoint FacD1 FacD2:=by
   rw [Finset.disjoint_left];intro k hk1 hk2
   obtain ⟨u,hu⟩:=Finset.card_pos.mp (by have:=(q1y k hk1).2.2.2;omega:0 < (orIn n C (n + k)).card)
   exact Finset.disjoint_left.mp q4o ((q1y k hk1).2.2.1 hu) ((q2z k hk2).2.2.1 hu)
  have q90:FacD.card = FacD1.card + FacD2.card:=by
   rw [q8a,Finset.card_union_of_disjoint qah]
  have q14:∀ k ∈ FacAll,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2:=by
   intro k hk;simp only [FacAll,q8a,Finset.mem_union] at hk
   rcases hk with (h | h) | (h | h)
   ·exact ⟨(q0j k h).2.1,(q0j k h).2.2.1⟩
   ·exact ⟨(q0k k h).2.1,(q0k k h).2.2.1⟩
   ·exact ⟨(q1y k h).1,(q1y k h).2.1⟩
   ·exact ⟨(q2z k h).1,(q2z k h).2.1⟩
  have q47:=z125 hL q01 h4 hne q00
   (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n + g2)
   (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1)) q4m
   (show orIn n C w1D = D1 from qb0) (fun u hu=>(hf1.2.2.2.2.1 u hu).symm)
  have q48:=z125 hL q01 h4 hne q00
   (z104 hL.1 q2p.1 (1 - b2))
   (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2)) q2y
   q4p (fun u hu=>(hf2.2.2.2.2.1 u hu).symm)
  have qbs:MD.card = MD1.card + MD2.card:=
   Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) q4o)
  dsimp only at q47 q48
  by_cases qcu:MC1 = C1∧ MC2 = C2∧ MD1 = D1∧ MD2 = D2
  ·
   obtain ⟨q5r,qer,q3m,q3n⟩:=qcu
   have qes:MD1.card ≤ FacD1.card + 1:=q47.1 ⟨zp1,by change zp1 ∈ MD1;rw [q3m];exact hf1.2.2.1⟩
   have qet:MD2.card ≤ FacD2.card + 1:=q48.1 ⟨zp2,by change zp2 ∈ MD2;rw [q3n];exact hf2.2.2.1⟩
   let L1:Fin n→ Finset (Fin n):=fun v=>
    if v = z then MD else if v = zp1 then MC1.erase z else if v = zp2 then MC2.erase z else ∅
   have q8z:L1 z = MD:=by simp [L1]
   have q5o:L1 zp1 = MC1.erase z:=by simp [L1,q2s.symm]
   have q5p:L1 zp2 = MC2.erase z:=by simp [L1,q2t.symm,q0h.symm]
   have qeg:∀ e ∈ Ustar G C,(∃ u ∈ L1 z,e = s(z,u))∨ (∃ u ∈ L1 zp1,e = s(zp1,u))∨ (∃ u ∈ L1 zp2,e = s(zp2,u)):=by
    intro e he
    have heF:=q5n he
    simp only [Finset.mem_union,z045,Finset.mem_image] at heF
    rcases heF with (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩) | (⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩)
    ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,he⟩),rfl⟩
    ·by_cases hcz:c = z
     ·subst hcz;left;exact ⟨zp1,by rw [q8z];exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1,he⟩),rfl⟩
     ·right;left;exact ⟨c,by rw [q5o];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
    ·left;exact ⟨d,by rw [q8z];exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd,he⟩),rfl⟩
    ·by_cases hcz:c = z
     ·subst hcz;left;exact ⟨zp2,by rw [q8z];exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1,he⟩),rfl⟩
     ·right;right;exact ⟨c,by rw [q5p];exact Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨hc,he⟩⟩,Sym2.eq_swap⟩
   have q6k:=run_surgery3 L1
    (fun u hu=>by rw [q8z] at hu;rcases Finset.mem_union.mp hu with h | h;exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm;exact (hf2.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm)
    (fun u hu=>by rw [q5o] at hu;exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
    (fun u hu=>by rw [q5p] at hu;exact (hf2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
    qeg
   dsimp only at q6k
   set Zact:=({z,zp1,zp2}:Finset (Fin n)).filter (fun v=>(L1 v).Nonempty)
   set Zhas:=Zact.filter (fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = v)
   rw [q8z,q5o,q5p] at q6k
   have qa9:(Zact \ Zhas).card ≤ 3:=by
    calc (Zact \ Zhas).card ≤ ({z,zp1,zp2}:Finset (Fin n)).card:=
       Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
     _ = 3:=by rw [Finset.card_insert_of_notMem (by simp [q2s,q2t]),Finset.card_pair q0h]
   obtain ⟨c1,hc1,q87⟩:=z049 hf1
   obtain ⟨c2,hc2,q6x⟩:=z049 hf2
   obtain ⟨d1,hd1,q6i⟩:=z050 hf1
   obtain ⟨d2,hd2,q8y⟩:=z050 hf2
   have q6n:c1 ∈ MC1.erase z:=Finset.mem_erase.mpr ⟨q87,by rw [q5r];exact hc1⟩
   have q8b:c2 ∈ MC2.erase z:=Finset.mem_erase.mpr ⟨q6x,by rw [qer];exact hc2⟩
   have qai:d1 ∈ MD:=Finset.mem_union_left _ (by rw [q3m];exact hd1)
   have qi8:d2 ∈ MD:=Finset.mem_union_right _ (by rw [q3n];exact hd2)
   have q49:d1 ≠ zp2:=fun h=>Finset.disjoint_left.mp q4o hd1 (h ▸ hf2.2.2.1)
   have q8c:d2 ≠ zp1:=fun h=>Finset.disjoint_right.mp q4o hd2 (h ▸ hf1.2.2.1)
   have q11:∀ k,(OrReaches n C (n + k) g1∨ OrReaches n C (n + k) g2)→ k ∉ FacAll:=by
    intro k hr hkf
    rcases hr with h1 | h2
    ·exact (q14 k hkf).1 h1
    ·exact (q14 k hkf).2 h2
   have q7f:FacAll.card ≤ (orN G C \ lam G C).card:=Finset.card_le_card q07
   by_cases qaa:2 ≤ (centreless G C).card
   ·omega
   ·by_cases q6l:(centreless G C).card = 1
    ·
     by_cases qla:(Zact \ Zhas).card ≤ 1
     ·omega
     ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
      have qbt:a0 ∈ centreless G C:=by rw [ha0];simp
      have q1x:a0 ∈ tops G C:=(Finset.mem_filter.mp qbt).1
      have qek:=z098.mp q1x
      by_cases hZ3:(Zact \ Zhas).card = 3
      ·
       have q6m:Zact \ Zhas = {z,zp1,zp2}:=
        Finset.eq_of_subset_of_card_le
         (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
         (by rw [Finset.card_insert_of_notMem (by simp [q2s,q2t]),Finset.card_pair q0h];omega)
       have q8d:z ∈ Zact \ Zhas:=by rw [q6m];simp
       have q08:zp1 ∈ Zact \ Zhas:=by rw [q6m];simp
       obtain ⟨b0,q6o,qi9,q96⟩:∃ b0:Fin 2,side (n:=n) C a0 b0 = ∅∧ 
         OrReaches n C (opnd C a0 b0) g1∧ z ∈ side (n:=n) C a0 (1 - b0):=by
        rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q8d).1,hA⟩) (Finset.mem_sdiff.mp q8d).2
        ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
         have qbu:gateVal n C g2 (pairInput z d1) = false:=by
          rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.2.1 d1 hd1).symm]
          simp only [z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff]
          rintro (⟨d,hd,⟨_,rfl⟩ | ⟨h1,_⟩⟩ | ⟨c,_,⟨_,rfl⟩ | ⟨_,h2⟩⟩)
          ·exact Finset.disjoint_left.mp q4o hd1 hd
          ·exact absurd (h1 ▸ z047 q03 hf1 hd1) (q03 z zp1 hf1.1)
          ·exact q49 rfl
          ·exact q2t.symm h2
         have q56:g = g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
         subst q56;exact ⟨b,q0g,hrb,hzs⟩
       have qia:OrReaches n C (opnd C a0 b0) g2:=by
        rcases q2d d2 qi8 q8c q8y with hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q8d).1,hA⟩) (Finset.mem_sdiff.mp q8d).2
        ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
         have qbv:gateVal n C g1 (pairInput z d2) = false:=by
          rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.2.1 d2 hd2).symm]
          simp only [z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff]
          rintro (⟨d,hd,⟨_,rfl⟩ | ⟨h1,_⟩⟩ | ⟨c,_,⟨_,rfl⟩ | ⟨_,h2⟩⟩)
          ·exact Finset.disjoint_left.mp q4o hd hd2
          ·exact absurd (h1 ▸ z047 q03 hf2 hd2) (q03 z zp2 hf2.1)
          ·exact q8c rfl
          ·exact q2s.symm h2
         have q56:g = g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
         subst q56
         have hbe:b = b0:=by
          by_contra q2e
          have q51:1 - b0 = b:=z044 (Ne.symm q2e)
          rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
         rwa [← hbe]
       obtain ⟨mp,hmp,qib,qeu⟩:=z122 hL q0y q00
        (by have:=z104 hL.1 qek.1 b0;omega) (z130 hL hne q1x b0)
        q6o qi9 qia
       obtain ⟨m2,hm2,q6p,qcv⟩:∃ m2 ∈ orN G C \ lam G C,m2 ∉ FacAll∧ (orIn n C (n + m2)).Nonempty:=by
        rcases q0l c1 q6n with hA | ⟨a,haC,b,q0g,_,q40⟩ | ⟨mv,hmv,q1r,q05,_⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
        ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
         have hbe:b = b0:=by
          by_contra q2e
          have q51:1 - b0 = b:=z044 (Ne.symm q2e)
          rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
         rw [hbe] at q40
         obtain ⟨mw,hmw,q6q,qox⟩:=z014 q03 hL q01 hne q00
          (by have:=z104 hL.1 qek.1 (1 - b0);omega)
          (z130 hL hne q1x (1 - b0)) q96 q40 (q03 z zp1 hf1.1)
          FacAll q2b
         exact ⟨mw,hmw,q6q,Finset.card_pos.mp (by omega)⟩
        ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega,by rw [q05];simp⟩
       have qic:mp ∉ FacAll:=fun h=>by have:=q0b mp h;omega
       have qev:mp ≠ m2:=fun h=>by rw [← h,qeu] at qcv;exact qcv.ne_empty rfl
       have q0z:Disjoint ({mp,m2}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        ·exact qic hkf
        ·exact q6p hkf
       have q2g:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hmp (Finset.singleton_subset_iff.mpr hm2)) q07)
       rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qev] at q2g
       omega
      ·
       have qn5:(Zact \ Zhas).card = 2:=by omega
       have qaj:∃ m ∈ orN G C \ lam G C,m ∉ FacAll:=by
        by_cases qew:z ∈ Zact \ Zhas
        ·
         obtain ⟨b0,q6o,q96⟩:∃ b0:Fin 2,side (n:=n) C a0 b0 = ∅∧ z ∈ side (n:=n) C a0 (1 - b0):=by
          rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,b,_,_,_,q0g,_,hzs⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp qew).1,hA⟩) (Finset.mem_sdiff.mp qew).2
          ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
           exact ⟨b,q0g,hzs⟩
         have qid:zp1 ∈ Zact \ Zhas∨ zp2 ∈ Zact \ Zhas:=by
          by_contra hno;push Not at hno
          have q0c:Zact \ Zhas ⊆ {z}:=by
           intro v hv
           have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
           simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
           rcases hv1 with rfl | rfl | rfl
           ·rfl
           ·exact absurd hv hno.1
           ·exact absurd hv hno.2
          have:=(Finset.card_le_card q0c).trans (by simp:({z}:Finset (Fin n)).card ≤ 1)
          omega
         rcases qid with q08 | q0e
         ·rcases q0l c1 q6n with hA | ⟨a,haC,b,q0g,_,q40⟩ | ⟨mv,hmv,q1r,_⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
          ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
           have hbe:b = b0:=by
            by_contra q2e
            have q51:1 - b0 = b:=z044 (Ne.symm q2e)
            rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
           rw [hbe] at q40
           obtain ⟨mw,hmw,q6q,_⟩:=z014 q03 hL q01 hne q00
            (by have:=z104 hL.1 qek.1 (1 - b0);omega)
            (z130 hL hne q1x (1 - b0)) q96 q40 (q03 z zp1 hf1.1)
            FacAll q2b
           exact ⟨mw,hmw,q6q⟩
          ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega⟩
         ·rcases q0n c2 q8b with hA | ⟨a,haC,b,q0g,_,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA⟩) (Finset.mem_sdiff.mp q0e).2
          ·have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
           have hbe:b = b0:=by
            by_contra q2e
            have q51:1 - b0 = b:=z044 (Ne.symm q2e)
            rw [q51,q0g] at q96;exact Finset.notMem_empty _ q96
           rw [hbe] at qbr
           obtain ⟨mw,hmw,q6q,_⟩:=z014 q03 hL q01 hne q00
            (by have:=z104 hL.1 qek.1 (1 - b0);omega)
            (z130 hL hne q1x (1 - b0)) q96 qbr (q03 z zp2 hf2.1)
            FacAll q2b
           exact ⟨mw,hmw,q6q⟩
          ·exact ⟨mu,hmu,fun h=>by have:=q0b mu h;omega⟩
        ·
         have q0c:Zact \ Zhas ⊆ {zp1,zp2}:=by
          intro v hv
          have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
          exact hv1.resolve_left (fun h=>qew (h ▸ hv))
         have qak:Zact \ Zhas = {zp1,zp2}:=
          Finset.eq_of_subset_of_card_le q0c (by rw [Finset.card_pair q0h];omega)
         have q08:zp1 ∈ Zact \ Zhas:=by rw [qak];simp
         have q0e:zp2 ∈ Zact \ Zhas:=by rw [qak];simp
         rcases q0l c1 q6n with hA1 | ⟨a1,qeh,b1',qbp,qjd,q40⟩ | ⟨mv,hmv,q1r,_⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA1⟩) (Finset.mem_sdiff.mp q08).2
         ·rcases q0n c2 q8b with hA2 | ⟨a2,qhz,b2',qbq,qje,qbr⟩ | ⟨_,_,_,_,_,_,mu,hmu,q2c,_⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA2⟩) (Finset.mem_sdiff.mp q0e).2
          ·have qei:a1 = a0:=Finset.mem_singleton.mp (ha0 ▸ qeh)
           have qej:a2 = a0:=Finset.mem_singleton.mp (ha0 ▸ qhz)
           subst qei;subst qej
           have ql8:b1' = b2':=by
            by_contra q2e
            have q51:1 - b1' = b2':=z044 q2e
            rw [q51,qbq] at q40;exact Finset.notMem_empty _ q40
           subst ql8
           obtain ⟨mp,hmp,qib,_⟩:=z122 hL q0y q00
            (by have:=z104 hL.1 qek.1 b1';omega) (z130 hL hne q1x b1')
            qbp qjd qje
           exact ⟨mp,hmp,fun h=>by have:=q0b mp h;omega⟩
          ·exact ⟨mu,hmu,fun h=>by have:=q0b mu h;omega⟩
         ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega⟩
       obtain ⟨m,hm,qel⟩:=qaj
       have q5q:=Finset.card_le_card (Finset.insert_subset hm q07)
       rw [Finset.card_insert_of_notMem qel] at q5q
       omega
    ·
     have q0m:centreless G C = ∅:=Finset.card_eq_zero.mp (by omega)
     have qac:∃ a ∈ tops G C \ centreless G C,z126 C s z g1 g2 a = z:=by
      rcases q2d d1 qai q6i q49 with hA | ⟨a,haC,_⟩
      ·exact hA
      ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
     have q7m:z ∉ Zact \ Zhas:=fun h=>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1,qac⟩)
     have q5d:Zact \ Zhas ⊆ {zp1,zp2}:=by
      intro v hv
      have hv1:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h=>q7m (h ▸ hv))
     have ql9:(Zact \ Zhas).card ≤ 2:=(Finset.card_le_card q5d).trans (by rw [Finset.card_pair q0h])
     by_cases hZ0:(Zact \ Zhas).card = 0
     ·obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q0m
      have qab:m0 ∉ FacAll:=fun h=>by have:=q0b m0 h;omega
      have q5q:=Finset.card_le_card (Finset.insert_subset hm0 q07)
      rw [Finset.card_insert_of_notMem qab] at q5q
      omega
     ·by_cases hZ1:(Zact \ Zhas).card = 1
      ·
       have qb2:∃ m1 m2,m1 ≠ m2∧ m1 ∈ orN G C \ lam G C∧ m2 ∈ orN G C \ lam G C∧ 
         m1 ∉ FacAll∧ m2 ∉ FacAll:=by
        have qlj:(Zact \ Zhas).Nonempty:=Finset.card_pos.mp (by omega)
        obtain ⟨v,hv⟩:=qlj
        have hv':=q5d hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with q30 | q30
        ·rw [q30] at hv
         rcases q0l c1 q6n with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,hA⟩) (Finset.mem_sdiff.mp hv).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·have qex:mv ≠ mu:=fun h=>by
           rw [h,q06] at q05
           have:=Finset.singleton_injective q05
           exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s this))
          exact ⟨mv,mu,qex,hmv,hmu,fun h=>by have:=q0b mv h;omega,
           q11 mu (Or.inl q3j)⟩
        ·rw [q30] at hv
         rcases q0n c2 q8b with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,qey,q05,u',q24,mu,hmu,q2c,q06⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,hA⟩) (Finset.mem_sdiff.mp hv).2
         ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
         ·have qex:mv ≠ mu:=fun h=>by
           rw [h,q06] at q05
           have:=Finset.singleton_injective q05
           exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s this))
          exact ⟨mv,mu,qex,hmv,hmu,q11 mv (Or.inl qey),
           fun h=>by have:=q0b mu h;omega⟩
       obtain ⟨m1,m2,qem,hm1,hm2,qal,q6p⟩:=qb2
       have q0z:Disjoint ({m1,m2}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        ·exact qal hkf
        ·exact q6p hkf
       have q2g:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) q07)
       rw [Finset.card_union_of_disjoint q0z,Finset.card_pair qem] at q2g
       omega
      ·
       have qak:Zact \ Zhas = {zp1,zp2}:=
        Finset.eq_of_subset_of_card_le q5d (by rw [Finset.card_pair q0h];omega)
       have q08:zp1 ∈ Zact \ Zhas:=by rw [qak];simp
       have q0e:zp2 ∈ Zact \ Zhas:=by rw [qak];simp
       obtain ⟨m1,hm1,qal,q1i,u',q24,m3,hm3,qie,q8e⟩:
         ∃ m1 ∈ orN G C \ lam G C,m1 ∉ FacAll∧ orIn n C (n + m1) = {zp1}∧ 
         ∃ u':Fin n,s u' = s z∧ ∃ m3 ∈ orN G C \ lam G C,m3 ∉ FacAll∧ orIn n C (n + m3) = {u'}:=by
        rcases q0l c1 q6n with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,q1r,q05,u',q24,mu,hmu,q3j,q06⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q08).1,hA⟩) (Finset.mem_sdiff.mp q08).2
        ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv,hmv,fun h=>by have:=q0b mv h;omega,q05,
          u',q24,mu,hmu,q11 mu (Or.inl q3j),q06⟩
       obtain ⟨m2,hm2,q6p,q16⟩:
         ∃ m2 ∈ orN G C \ lam G C,m2 ∉ FacAll∧ orIn n C (n + m2) = {zp2}:=by
        rcases q0n c2 q8b with hA | ⟨a,haC,_⟩ | ⟨mv,hmv,qey,q05,_⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q0e).1,hA⟩) (Finset.mem_sdiff.mp q0e).2
        ·rw [q0m] at haC;exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv,hmv,q11 mv (Or.inl qey),q05⟩
       have qem:m1 ≠ m2:=fun h=>by
        rw [h,q16] at q1i;exact q0h.symm (Finset.singleton_injective q1i)
       have qoy:m1 ≠ m3:=fun h=>by
        rw [h,q8e] at q1i
        have:=Finset.singleton_injective q1i
        exact q03 z zp1 hf1.1 (q24.symm.trans (congrArg s this))
       have qoz:m2 ≠ m3:=fun h=>by
        rw [h,q8e] at q16
        have:=Finset.singleton_injective q16
        exact q03 z zp2 hf2.1 (q24.symm.trans (congrArg s this))
       have q0z:Disjoint ({m1,m2,m3}:Finset ℕ) FacAll:=by
        rw [Finset.disjoint_left];intro k hk hkf
        simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        ·exact qal hkf
        ·exact q6p hkf
        ·exact qie hkf
       have qez:=Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.insert_subset hm2 (Finset.singleton_subset_iff.mpr hm3))) q07)
       rw [Finset.card_union_of_disjoint q0z,
        Finset.card_insert_of_notMem (by simp [qem,qoy]),Finset.card_pair qoz] at qez
       omega
  ·
   have qes:MD1.card ≤ FacD1.card + 1:=by
    by_cases h:MD1.Nonempty
    ·exact q47.1 h
    ·rw [Finset.not_nonempty_iff_eq_empty.mp h];simp
   have qet:MD2.card ≤ FacD2.card + 1:=by
    by_cases h:MD2.Nonempty
    ·exact q48.1 h
    ·rw [Finset.not_nonempty_iff_eq_empty.mp h];simp
   apply close_slack1
   rw [q13,q90,qbs]
   by_cases q3m:MD1 = D1
   ·by_cases q3n:MD2 = D2
    ·
     have qif:z ∈ MC1:=Finset.mem_filter.mpr ⟨hf1.2.1,(Finset.mem_filter.mp (by rw [q3m];exact hf1.2.2.1:zp1 ∈ MD1)).2⟩
     have qig:z ∈ MC2:=Finset.mem_filter.mpr ⟨hf2.2.1,(Finset.mem_filter.mp (by rw [q3n];exact hf2.2.2.1:zp2 ∈ MD2)).2⟩
     by_cases q5r:MC1 = C1
     ·have q3l:MC2 ≠ C2:=fun h=>qcu ⟨q5r,h,q3m,q3n⟩
      have hex:∃ r ∈ C2,r ∉ MC2:=by
       by_contra hno;push Not at hno
       exact q3l (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle:MC2.card ≤ FacC2.card:=q1h.2 hex
      rw [Finset.card_erase_of_mem qig]
      have qj5:=Finset.card_pos.mpr ⟨z,qig⟩
      omega
     ·have hex:∃ r ∈ C1,r ∉ MC1:=by
       by_contra hno;push Not at hno
       exact q5r (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle:MC1.card ≤ FacC1.card:=q1w.2 hex
      rw [Finset.card_erase_of_mem qif]
      have qj5:=Finset.card_pos.mpr ⟨z,qif⟩
      omega
    ·have hex:∃ r ∈ D2,r ∉ MD2:=by
      by_contra hno;push Not at hno
      exact q3n (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
     have hle:MD2.card ≤ FacD2.card:=q48.2 hex
     omega
   ·have hex:∃ r ∈ D1,r ∉ MD1:=by
     by_contra hno;push Not at hno
     exact q3m (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
    have hle:MD1.card ≤ FacD1.card:=q47.2 hex
    omega
lemma z020 {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
  {s:Fin n→ Bool} (q03:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C)
  {g1 g2:ℕ} (q0y:g1 < g2) (q00:∀ k,k ∈ junk G C↔ k = g1∨ k = g2)
  {C1 D1 C2 D2:Finset (Fin n)} {z1 zp1 z2 zp2:Fin n}
  (q5z:z1 ≠ z2) (q0h:zp1 ≠ zp2) (hsz:s z1 = s z2) (q1l:s zp1 = s zp2)
  (hf1:z000 G C g1 C1 D1 z1 zp1) (hf2:z000 G C g2 C2 D2 z2 zp2):False:=by
 classical
 have hne:∃ u v:Fin n,G.Adj u v:=⟨z1,zp1,hf1.1⟩
 have qdf:g1 ≠ g2:=Nat.ne_of_lt q0y
 have q5x:=z094.mp ((q00 g1).mpr (Or.inl rfl))
 have q2p:=z094.mp ((q00 g2).mpr (Or.inr rfl))
 have q02:s z1 ≠ s zp1:=q03 z1 zp1 hf1.1
 have q2h:z1 ≠ zp1:=fun h=>q02 (congrArg s h)
 have q1z:z1 ≠ zp2:=fun h=>q02 ((congrArg s h).trans q1l.symm)
 have q20:z2 ≠ zp1:=fun h=>q02 (hsz.trans (congrArg s h))
 have q2i:z2 ≠ zp2:=fun h=>q02 (hsz.trans ((congrArg s h).trans q1l.symm))
 obtain ⟨⟨qce,qcf,qcg,qch⟩,b1,qci,qb0⟩:=
  z066 q03 hL q01 q0y q00 hf1
 obtain ⟨qcj,qck,b2,q44,q2o,q6h,q3k,q5a,q2a⟩:=
  z067 q03 h4 hL q01 q0y q00 hf1 hf2 hsz q1l
 set w1C:=opnd C g1 b1
 set w1D:=opnd C g1 (1 - b1)
 set w2C:=opnd C g2 b2
 set w2D:=opnd C g2 (1 - b2)
 have q4l:¬ OrReaches n C w1C g1:=by fin_cases b1 <;> assumption
 have q7i:¬ OrReaches n C w1C g2:=by fin_cases b1 <;> assumption
 have q4m:¬ OrReaches n C w1D g1:=by fin_cases b1 <;> assumption
 have q7j:¬ OrReaches n C w1D g2:=by fin_cases b1 <;> assumption
 have q2x:¬ OrReaches n C w2C g1:=fun h=>q0h (q6h h).2.1
 have q7k:¬ OrReaches n C w2C g2:=by fin_cases b2 <;> assumption
 have q2y:¬ OrReaches n C w2D g1:=fun h=>q5z (q5a h).2.1
 have q7l:¬ OrReaches n C w2D g2:=by fin_cases b2 <;> assumption
 have q4n:orIn n C w2C = C2:=q3k q2x
 have q4p:orIn n C w2D = D2:=q2a q2y
 set FacC1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1C k)
 set FacD1:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w1D k)
 set FacC2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2C k)
 set FacD2:=(orN G C \ lam G C).filter (fun k=>OrReaches n C w2D k)
 have q2q:∀ a,a ∈ junk G C→ ∀ b:Fin 2,∀ m,opnd C a b = n + m→ ¬ BelowF G C m:=by
  intro a ha b m hm hbm
  have ha':=z094.mp ha
  exact z089 hL hne ha'.1 ha'.2.1 b (by rw [hm];exact hbm)
 have q1j:∀ k ∈ FacC1,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ C1∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk;have hkf:=Finset.mem_filter.mp hk
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q4l (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7i (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [show orIn n C w1C = C1 from qci] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q1s:∀ k ∈ FacD1,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ D1∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk;have hkf:=Finset.mem_filter.mp hk
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q4m (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7j (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [show orIn n C w1D = D1 from qb0] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q22:∀ k ∈ FacC2,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ C2∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk;have hkf:=Finset.mem_filter.mp hk
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q2x (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7k (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [q4n] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q2j:∀ k ∈ FacD2,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2∧ 
   orIn n C (n + k) ⊆ D2∧ 2 ≤ (orIn n C (n + k)).card:=by
  intro k hk;have hkf:=Finset.mem_filter.mp hk
  have hn1:¬ OrReaches n C (n + k) g1:=fun h=>q2y (z116 hkf.2 h)
  have hn2:¬ OrReaches n C (n + k) g2:=fun h=>q7l (z116 hkf.2 h)
  have q0c:=z109 hkf.2;rw [q4p] at q0c
  exact ⟨hn1,hn2,q0c,z123 hL q01 hne q00 (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have q0r:∀ {v1 v2:Fin n} {F1 F2:Finset ℕ},v1 ≠ v2→ 
   (∀ k ∈ F1,(∀ u ∈ orIn n C (n + k),G.Adj v1 u)∧ 2 ≤ (orIn n C (n + k)).card)→ 
   (∀ k ∈ F2,∀ u ∈ orIn n C (n + k),G.Adj v2 u)→ Disjoint F1 F2:=by
  intro v1 v2 F1 F2 qp0 h1 h2
  rw [Finset.disjoint_left];intro k hk1 hk2
  obtain ⟨u1,hu1,u2,hu2,qd2⟩:=Finset.one_lt_card.mp (by have:=(h1 k hk1).2;omega:1 < (orIn n C (n + k)).card)
  exact qp0 (z102 h4 qd2
   ((h1 k hk1).1 u1 hu1).symm ((h1 k hk1).1 u2 hu2).symm
   (h2 k hk2 u1 hu1).symm (h2 k hk2 u2 hu2).symm)
 have qf0:Disjoint FacC1 FacD1:=q0r q2h.symm
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm)
 have qf1:Disjoint FacC1 FacC2:=q0r q0h
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm)
 have qf2:Disjoint FacC1 FacD2:=q0r q20.symm
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.1 u ((q1j k hk).2.2.1 hu)).symm,(q1j k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 have qf3:Disjoint FacD1 FacC2:=q0r q1z
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm,(q1s k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm)
 have qf4:Disjoint FacD1 FacD2:=q0r q5z
  (fun k hk=>⟨fun u hu=>(hf1.2.2.2.2.1 u ((q1s k hk).2.2.1 hu)).symm,(q1s k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 have qf5:Disjoint FacC2 FacD2:=q0r q2i.symm
  (fun k hk=>⟨fun u hu=>(hf2.2.2.2.1 u ((q22 k hk).2.2.1 hu)).symm,(q22 k hk).2.2.2⟩)
  (fun k hk u hu=>(hf2.2.2.2.2.1 u ((q2j k hk).2.2.1 hu)).symm)
 set FacAll:=(FacC1 ∪ FacD1) ∪ (FacC2 ∪ FacD2)
 set Extra:=(orN G C \ lam G C) \ FacAll
 have q07:FacAll ⊆ orN G C \ lam G C:=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
 have q13:FacAll.card = FacC1.card + FacD1.card + FacC2.card + FacD2.card:=by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
   ⟨Finset.disjoint_union_right.mpr ⟨qf1,qf2⟩,Finset.disjoint_union_right.mpr ⟨qf3,qf4⟩⟩),
   Finset.card_union_of_disjoint qf0,Finset.card_union_of_disjoint qf5]
  omega
 have q8r:(orN G C \ lam G C).card = FacAll.card + Extra.card:=by
  rw [z019 q07];have:=Finset.card_le_card q07;omega
 have q14:∀ k ∈ FacAll,¬ OrReaches n C (n + k) g1∧ ¬ OrReaches n C (n + k) g2:=by
  intro k hk;simp only [FacAll,Finset.mem_union] at hk
  rcases hk with (h | h) | (h | h)
  ·exact ⟨(q1j k h).1,(q1j k h).2.1⟩
  ·exact ⟨(q1s k h).1,(q1s k h).2.1⟩
  ·exact ⟨(q22 k h).1,(q22 k h).2.1⟩
  ·exact ⟨(q2j k h).1,(q2j k h).2.1⟩
 have q0w:∀ k ∈ orN G C \ lam G C,(OrReaches n C (n + k) g1∨ OrReaches n C (n + k) g2)→ k ∈ Extra:=by
  intro k hk hr
  exact Finset.mem_sdiff.mpr ⟨hk,fun hkf=>hr.elim (q14 k hkf).1 (q14 k hkf).2⟩
 set E1:=z045 C1 D1 z1 zp1
 set E2:=z045 C2 D2 z2 zp2
 set U1:=Ustar G C ∩ E1
 set U2:=Ustar G C ∩ E2
 set U12:=U1 ∩ U2
 have q5n:=z135 q03 hL q01 h4 q00 hf1 hf2
 have q4q:Ustar G C = U1 ∪ U2:=by
  ext e;simp only [U1,U2,Finset.mem_union,Finset.mem_inter]
  constructor
  ·intro he;rcases Finset.mem_union.mp (q5n he) with h1 | h2
   ·exact Or.inl ⟨he,h1⟩
   ·exact Or.inr ⟨he,h2⟩
  ·rintro (⟨he,_⟩ | ⟨he,_⟩) <;> exact he
 have q5s:∀ e ∈ U12,e = s(z1,zp2)∨ e = s(z2,zp1):=by
  intro e he
  have he1:e ∈ E1:=(Finset.mem_inter.mp (Finset.mem_inter.mp he).1).2
  have he2:e ∈ E2:=(Finset.mem_inter.mp (Finset.mem_inter.mp he).2).2
  simp only [E1,E2,z045,Finset.mem_union,Finset.mem_image] at he1 he2
  rcases he1 with ⟨d1,hd1,rfl⟩ | ⟨c1,hc1,rfl⟩ <;>
  rcases he2 with ⟨d2,hd2,h2⟩ | ⟨c2,hc2,h2⟩ <;>
  rw [Sym2.eq_iff] at h2
  ·rcases h2 with ⟨h,_⟩ | ⟨h,_⟩
   ·exact absurd h.symm q5z
   ·exact absurd (hsz.trans (by rw [h];exact z047 q03 hf1 hd1)) q02
  ·rcases h2 with ⟨h,h'⟩ | ⟨_,h'⟩
   ·exact Or.inl (by rw [← h,← h'])
   ·exact absurd (q1l.trans (congrArg s h')).symm q02
  ·rcases h2 with ⟨h,h'⟩ | ⟨h,_⟩
   ·exact Or.inr (by rw [← h,← h'])
   ·exact absurd (hsz.trans (congrArg s h)) q02
  ·rcases h2 with ⟨_,h⟩ | ⟨h,_⟩
   ·exact absurd h.symm q0h
   ·exact absurd ((hsz.trans (z046 q03 hf2 hc2).symm).trans (congrArg s h)) q02
 have qjg:U12.card ≤ 1:=by
  by_contra hgt;push Not at hgt
  obtain ⟨e1,he1,e2,he2,qn6⟩:=Finset.one_lt_card.mp hgt
  have hm1:=q5s e1 he1
  have hm2:=q5s e2 he2
  have qb1:s(z1,zp2) ∈ U12∧ s(z2,zp1) ∈ U12:=by
   rcases hm1 with rfl | rfl <;> rcases hm2 with rfl | rfl
   ·exact absurd rfl qn6
   ·exact ⟨he1,he2⟩
   ·exact ⟨he2,he1⟩
   ·exact absurd rfl qn6
  have qlk:G.Adj z1 zp2:=SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_inter.mp qb1.1).1).1).1
  have qll:G.Adj z2 zp1:=SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_inter.mp qb1.2).1).1).1
  exact q0h (z102 h4 q5z hf1.1 qll qlk hf2.1)
 have qih:(∀ e ∈ U12,e = s(z1,zp2))∨ (∀ e ∈ U12,e = s(z2,zp1)):=by
  by_cases q0g:U12 = ∅
  ·left;intro e he;rw [q0g] at he;exact absurd he (Finset.notMem_empty _)
  ·obtain ⟨e0,he0⟩:=Finset.nonempty_iff_ne_empty.mpr q0g
   have q0t:U12.card = 1:=by have:=Finset.Nonempty.card_pos ⟨e0,he0⟩;omega
   obtain ⟨x,hx⟩:=Finset.card_eq_one.mp q0t
   have hx0:e0 = x:=Finset.mem_singleton.mp (hx ▸ he0)
   subst hx0
   rcases q5s e0 he0 with rfl | rfl
   ·left;intro e he;rw [hx,Finset.mem_singleton] at he;exact he
   ·right;intro e he;rw [hx,Finset.mem_singleton] at he;exact he
 set MC1:=C1.filter (fun c=>s(c,zp1) ∈ Ustar G C)
 set MD1:=D1.filter (fun d=>s(z1,d) ∈ Ustar G C)
 set MC2:=C2.filter (fun c=>s(c,zp2) ∈ Ustar G C)
 set MD2:=D2.filter (fun d=>s(z2,d) ∈ Ustar G C)
 have q6r:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 b1;omega:w1C < n + g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) b1) q4l
  (show orIn n C w1C = C1 from qci) (fun u hu=>(hf1.2.2.2.1 u hu).symm)
 have q8f:=z125 hL q01 h4 hne q00
  (by have:=z104 hL.1 q5x.1 (1 - b1);omega:w1D < n + g2)
  (q2q g1 ((q00 g1).mpr (Or.inl rfl)) (1 - b1)) q4m
  (show orIn n C w1D = D1 from qb0) (fun u hu=>(hf1.2.2.2.2.1 u hu).symm)
 have q6s:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 b2)
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) b2) q2x
  q4n (fun u hu=>(hf2.2.2.2.1 u hu).symm)
 have q8g:=z125 hL q01 h4 hne q00
  (z104 hL.1 q2p.1 (1 - b2))
  (q2q g2 ((q00 g2).mpr (Or.inr rfl)) (1 - b2)) q2y
  q4p (fun u hu=>(hf2.2.2.2.2.1 u hu).symm)
 have qf6:C1.filter (fun u=>s(zp1,u) ∈ Ustar G C) = MC1:=by ext u;simp [MC1,Sym2.eq_swap]
 have qf7:C2.filter (fun u=>s(zp2,u) ∈ Ustar G C) = MC2:=by ext u;simp [MC2,Sym2.eq_swap]
 dsimp only at q6r q8f q6s q8g
 rw [qf6] at q6r;rw [qf7] at q6s
 have q8h:U1.card = MD1.card + (MC1.erase z1).card:=by
  have q4y:Disjoint (MD1.image fun d=>s(z1,d)) ((MC1.erase z1).image fun c=>s(c,zp1)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Finset.mem_image,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,hd,rfl⟩;rcases h2 with ⟨c,⟨hcz,hc⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q02 (congrArg s h2'.symm)
  have qii:U1 = (MD1.image fun d=>s(z1,d)) ∪ ((MC1.erase z1).image fun c=>s(c,zp1)):=by
   ext e;simp only [U1,E1,z045,Finset.mem_inter,Finset.mem_union,Finset.mem_image,Finset.mem_erase,MD1,MC1,Finset.mem_filter]
   constructor
   ·rintro ⟨heU,⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩⟩
    ·exact Or.inl ⟨d,⟨hd,heU⟩,rfl⟩
    ·by_cases hcz:c = z1
     ·subst hcz;exact Or.inl ⟨zp1,⟨hf1.2.2.1,heU⟩,rfl⟩
     ·exact Or.inr ⟨c,⟨hcz,hc,heU⟩,rfl⟩
   ·rintro (⟨d,⟨hd,heU⟩,rfl⟩ | ⟨c,⟨_,hc,heU⟩,rfl⟩)
    ·exact ⟨heU,Or.inl ⟨d,hd,rfl⟩⟩
    ·exact ⟨heU,Or.inr ⟨c,hc,rfl⟩⟩
  rw [qii,Finset.card_union_of_disjoint q4y,
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
 have qbw:U2.card = MD2.card + (MC2.erase z2).card:=by
  have q4y:Disjoint (MD2.image fun d=>s(z2,d)) ((MC2.erase z2).image fun c=>s(c,zp2)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Finset.mem_image,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,hd,rfl⟩;rcases h2 with ⟨c,⟨hcz,hc⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q03 z2 zp2 hf2.1 (congrArg s h2'.symm)
  have qij:U2 = (MD2.image fun d=>s(z2,d)) ∪ ((MC2.erase z2).image fun c=>s(c,zp2)):=by
   ext e;simp only [U2,E2,z045,Finset.mem_inter,Finset.mem_union,Finset.mem_image,Finset.mem_erase,MD2,MC2,Finset.mem_filter]
   constructor
   ·rintro ⟨heU,⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩⟩
    ·exact Or.inl ⟨d,⟨hd,heU⟩,rfl⟩
    ·by_cases hcz:c = z2
     ·subst hcz;exact Or.inl ⟨zp2,⟨hf2.2.2.1,heU⟩,rfl⟩
     ·exact Or.inr ⟨c,⟨hcz,hc,heU⟩,rfl⟩
   ·rintro (⟨d,⟨hd,heU⟩,rfl⟩ | ⟨c,⟨_,hc,heU⟩,rfl⟩)
    ·exact ⟨heU,Or.inl ⟨d,hd,rfl⟩⟩
    ·exact ⟨heU,Or.inr ⟨c,hc,rfl⟩⟩
  rw [qij,Finset.card_union_of_disjoint q4y,
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
 set loss1:ℕ:=if MC1 = C1∧ MD1 = D1 then 1 else 0
 set loss2:ℕ:=if MC2 = C2∧ MD2 = D2 then 1 else 0
 have qlm:U1.card ≤ FacC1.card + FacD1.card + loss1:=by
  rw [q8h]
  by_cases hzM:z1 ∈ MC1
  ·rw [Finset.card_erase_of_mem hzM]
   have q97:zp1 ∈ MD1:=Finset.mem_filter.mpr ⟨hf1.2.2.1,(Finset.mem_filter.mp hzM).2⟩
   have qp1:MC1.card ≤ FacC1.card + 1:=q6r.1 ⟨z1,hzM⟩
   have qp2:MD1.card ≤ FacD1.card + 1:=q8f.1 ⟨zp1,q97⟩
   by_cases q4z:MC1 = C1∧ MD1 = D1
   ·simp only [loss1,if_pos q4z];omega
   ·simp only [loss1,if_neg q4z]
    by_cases q75:MC1 = C1
    ·have qln:MD1 ≠ D1:=fun h=>q4z ⟨q75,h⟩
     have hex:∃ r ∈ D1,r ∉ MD1:=by by_contra h;push Not at h;exact qln (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlo:MD1.card ≤ FacD1.card:=q8f.2 hex;omega
    ·have hex:∃ r ∈ C1,r ∉ MC1:=by by_contra h;push Not at h;exact q75 (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlp:MC1.card ≤ FacC1.card:=q6r.2 hex;have qj5:=Finset.card_pos.mpr ⟨z1,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have q97:zp1 ∉ MD1:=fun h=>hzM (Finset.mem_filter.mpr ⟨hf1.2.1,(Finset.mem_filter.mp h).2⟩)
   have qlp:MC1.card ≤ FacC1.card:=q6r.2 ⟨z1,hf1.2.1,hzM⟩
   have qlo:MD1.card ≤ FacD1.card:=q8f.2 ⟨zp1,hf1.2.2.1,q97⟩
   omega
 have qlq:U2.card ≤ FacC2.card + FacD2.card + loss2:=by
  rw [qbw]
  by_cases hzM:z2 ∈ MC2
  ·rw [Finset.card_erase_of_mem hzM]
   have q97:zp2 ∈ MD2:=Finset.mem_filter.mpr ⟨hf2.2.2.1,(Finset.mem_filter.mp hzM).2⟩
   have qp3:MC2.card ≤ FacC2.card + 1:=q6s.1 ⟨z2,hzM⟩
   have qp4:MD2.card ≤ FacD2.card + 1:=q8g.1 ⟨zp2,q97⟩
   by_cases q4z:MC2 = C2∧ MD2 = D2
   ·simp only [loss2,if_pos q4z];omega
   ·simp only [loss2,if_neg q4z]
    by_cases q75:MC2 = C2
    ·have qln:MD2 ≠ D2:=fun h=>q4z ⟨q75,h⟩
     have hex:∃ r ∈ D2,r ∉ MD2:=by by_contra h;push Not at h;exact qln (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qlr:MD2.card ≤ FacD2.card:=q8g.2 hex;omega
    ·have hex:∃ r ∈ C2,r ∉ MC2:=by by_contra h;push Not at h;exact q75 (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have qls:MC2.card ≤ FacC2.card:=q6s.2 hex;have qj5:=Finset.card_pos.mpr ⟨z2,hzM⟩;omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have q97:zp2 ∉ MD2:=fun h=>hzM (Finset.mem_filter.mpr ⟨hf2.2.1,(Finset.mem_filter.mp h).2⟩)
   have qls:MC2.card ≤ FacC2.card:=q6s.2 ⟨z2,hf2.2.1,hzM⟩
   have qlr:MD2.card ≤ FacD2.card:=q8g.2 ⟨zp2,hf2.2.2.1,q97⟩
   omega
 let isOwn:Fin n→ Prop:=fun v=>∃ a ∈ tops G C \ centreless G C,z126 C s z1 g1 g2 a = v
 set MD1_ns:=MD1.erase zp1
 set MC1_ns:=MC1.erase z1
 set MD2_ns:=(D2.erase zp2).filter (fun d=>s(z2,d) ∈ U2 \ U1)
 set MC2_ns:=(C2.erase z2).filter (fun c=>s(c,zp2) ∈ U2 \ U1)
 let e1_to_z1:Prop:=MD1_ns.Nonempty∨ isOwn z1∨ ¬ MC1_ns.Nonempty
 let e2_to_z2:Prop:=MD2_ns.Nonempty∨ isOwn z2∨ ¬ MC2_ns.Nonempty
 let L:Fin n→ Finset (Fin n):=fun v=>
  if v = z1 then (if s(z1,zp1) ∈ U1∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns)
  else if v = zp1 then (if s(z1,zp1) ∈ U1∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns)
  else if v = z2 then (if s(z2,zp2) ∈ U2∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns)
  else if v = zp2 then (if s(z2,zp2) ∈ U2∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns)
  else ∅
 have qcw:L z1 = if s(z1,zp1) ∈ U1∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns:=by simp [L]
 have q6t:L zp1 = if s(z1,zp1) ∈ U1∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns:=by simp [L,q2h.symm]
 have qcx:L z2 = if s(z2,zp2) ∈ U2∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns:=by simp [L,q5z.symm,q20]
 have q6u:L zp2 = if s(z2,zp2) ∈ U2∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns:=by simp [L,q1z.symm,q0h.symm,q2i.symm]
 have qbx:({z1,zp1,z2,zp2}:Finset (Fin n)).card = 4:=by
  rw [Finset.card_insert_of_notMem (by simp [q2h,q5z,q1z]),
   Finset.card_insert_of_notMem (by simp [q20.symm,q0h]),Finset.card_pair q2i]
 set Zact:=({z1,zp1,z2,zp2}:Finset (Fin n)).filter (fun v=>(L v).Nonempty)
 set Zhas:=Zact.filter isOwn
 set Znew:=Zact \ Zhas
 have qf8:s(z2,zp2) ∉ U1:=by
  intro h
  have hE1:=(Finset.mem_inter.mp h).2
  simp only [E1,z045,Finset.mem_union,Finset.mem_image,Sym2.eq_iff] at hE1
  rcases hE1 with ⟨d,hd,⟨h1,_⟩ | ⟨h1,_⟩⟩ | ⟨c,hc,⟨_,h2⟩ | ⟨h1,_⟩⟩
  ·exact q5z h1
  ·exact q02 (by rw [h1,← q1l])
  ·exact q0h h2
  ·exact q02 ((z046 q03 hf1 hc).symm.trans (by rw [h1];exact q1l.symm))
 have q8w:∀ e ∈ Ustar G C,∃ v ∈ Zact,∃ u ∈ L v,e = s(v,u):=by
  intro e he
  rw [q4q,Finset.mem_union] at he
  by_cases he1:e ∈ U1
  ·have hE1:=(Finset.mem_inter.mp he1).2
   have heU:=(Finset.mem_inter.mp he1).1
   simp only [E1,z045,Finset.mem_union,Finset.mem_image] at hE1
   rcases hE1 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
   ·by_cases q1e:d = zp1
    ·rw [q1e] at he1 ⊢
     by_cases q3o:e1_to_z1
     ·refine ⟨z1,Finset.mem_filter.mpr ⟨by simp,⟨zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp,rfl⟩
     ·refine ⟨zp1,Finset.mem_filter.mpr ⟨by simp,⟨z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7s:d ∈ MD1_ns:=Finset.mem_erase.mpr ⟨q1e,Finset.mem_filter.mpr ⟨hd,heU⟩⟩
     have hdL:d ∈ L z1:=by rw [qcw];split_ifs;exact Finset.mem_insert_of_mem q7s;exact q7s
     exact ⟨z1,Finset.mem_filter.mpr ⟨by simp,⟨d,hdL⟩⟩,d,hdL,rfl⟩
   ·by_cases hcz:c = z1
    ·rw [hcz] at he1 ⊢
     by_cases q3o:e1_to_z1
     ·refine ⟨z1,Finset.mem_filter.mpr ⟨by simp,⟨zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       zp1,by rw [qcw,if_pos ⟨he1,q3o⟩];simp,rfl⟩
     ·refine ⟨zp1,Finset.mem_filter.mpr ⟨by simp,⟨z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp⟩⟩,
       z1,by rw [q6t,if_pos ⟨he1,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7t:c ∈ MC1_ns:=Finset.mem_erase.mpr ⟨hcz,Finset.mem_filter.mpr ⟨hc,heU⟩⟩
     have hcL:c ∈ L zp1:=by rw [q6t];split_ifs;exact Finset.mem_insert_of_mem q7t;exact q7t
     exact ⟨zp1,Finset.mem_filter.mpr ⟨by simp,⟨c,hcL⟩⟩,c,hcL,Sym2.eq_swap⟩
  ·have he2:e ∈ U2:=he.resolve_left he1
   have qn7:e ∈ U2 \ U1:=Finset.mem_sdiff.mpr ⟨he2,he1⟩
   have hE2:=(Finset.mem_inter.mp he2).2
   simp only [E2,z045,Finset.mem_union,Finset.mem_image] at hE2
   rcases hE2 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
   ·by_cases q1e:d = zp2
    ·rw [q1e] at he2 ⊢
     by_cases q3o:e2_to_z2
     ·refine ⟨z2,Finset.mem_filter.mpr ⟨by simp,⟨zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp,rfl⟩
     ·refine ⟨zp2,Finset.mem_filter.mpr ⟨by simp,⟨z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7s:d ∈ MD2_ns:=Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨q1e,hd⟩,qn7⟩
     have hdL:d ∈ L z2:=by rw [qcx];split_ifs;exact Finset.mem_insert_of_mem q7s;exact q7s
     exact ⟨z2,Finset.mem_filter.mpr ⟨by simp,⟨d,hdL⟩⟩,d,hdL,rfl⟩
   ·by_cases hcz:c = z2
    ·rw [hcz] at he2 ⊢
     by_cases q3o:e2_to_z2
     ·refine ⟨z2,Finset.mem_filter.mpr ⟨by simp,⟨zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       zp2,by rw [qcx,if_pos ⟨he2,q3o⟩];simp,rfl⟩
     ·refine ⟨zp2,Finset.mem_filter.mpr ⟨by simp,⟨z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp⟩⟩,
       z2,by rw [q6u,if_pos ⟨he2,q3o⟩];simp,Sym2.eq_swap⟩
    ·have q7t:c ∈ MC2_ns:=Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hcz,hc⟩,qn7⟩
     have hcL:c ∈ L zp2:=by rw [q6u];split_ifs;exact Finset.mem_insert_of_mem q7t;exact q7t
     exact ⟨zp2,Finset.mem_filter.mpr ⟨by simp,⟨c,hcL⟩⟩,c,hcL,Sym2.eq_swap⟩
 have qp5:(L z1).card + (L zp1).card = U1.card:=by
  rw [q8h,qcw,q6t]
  have qf9:zp1 ∉ MD1_ns:=Finset.notMem_erase _ _
  have qlt:z1 ∉ MC1_ns:=Finset.notMem_erase _ _
  by_cases he1:s(z1,zp1) ∈ U1
  ·have q97:zp1 ∈ MD1:=Finset.mem_filter.mpr ⟨hf1.2.2.1,(Finset.mem_inter.mp he1).1⟩
   have qam:MD1_ns.card + 1 = MD1.card:=by
    rw [Finset.card_erase_of_mem q97];have:=Finset.card_pos.mpr ⟨zp1,q97⟩;omega
   by_cases q3o:e1_to_z1 <;> simp [he1,q3o,qf9,qlt] <;> omega
  ·have q97:zp1 ∉ MD1:=fun h=>he1 (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h).2,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf1.2.2.1)⟩)
   have qam:MD1_ns = MD1:=Finset.erase_eq_of_notMem q97
   simp [he1,qam]
 have qp6:(L z2).card + (L zp2).card = (U2 \ U1).card:=by
  have qfa:U2 \ U1 = (MD2_ns.image fun d=>s(z2,d)) ∪ (MC2_ns.image fun c=>s(c,zp2)) ∪
    (if s(z2,zp2) ∈ U2 then {s(z2,zp2)} else ∅):=by
   ext e;simp only [Finset.mem_union,Finset.mem_image,MD2_ns,MC2_ns,Finset.mem_filter,Finset.mem_erase]
   constructor
   ·intro he
    have he2:=(Finset.mem_sdiff.mp he).1
    have hE2:=(Finset.mem_inter.mp he2).2
    simp only [E2,z045,Finset.mem_union,Finset.mem_image] at hE2
    rcases hE2 with ⟨d,hd,rfl⟩ | ⟨c,hc,rfl⟩
    ·by_cases q1e:d = zp2
     ·subst q1e;right;rw [if_pos he2];exact Finset.mem_singleton_self _
     ·left;left;exact ⟨d,⟨⟨q1e,hd⟩,he⟩,rfl⟩
    ·by_cases hcz:c = z2
     ·subst hcz;right;rw [if_pos he2];exact Finset.mem_singleton_self _
     ·left;right;exact ⟨c,⟨⟨hcz,hc⟩,he⟩,rfl⟩
   ·rintro ((⟨d,⟨_,he⟩,rfl⟩ | ⟨c,⟨_,he⟩,rfl⟩) | hsp)
    ·exact he
    ·exact he
    ·split_ifs at hsp with he2
     ·rw [Finset.mem_singleton] at hsp;subst hsp;exact Finset.mem_sdiff.mpr ⟨he2,qf8⟩
     ·exact absurd hsp (Finset.notMem_empty _)
  have qp7:Disjoint (MD2_ns.image fun d=>s(z2,d)) (MC2_ns.image fun c=>s(c,zp2)):=by
   rw [Finset.disjoint_left];intro e h1 h2
   simp only [Finset.mem_image,MD2_ns,MC2_ns,Finset.mem_filter,Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d,⟨⟨q1e,hd⟩,_⟩,rfl⟩;rcases h2 with ⟨c,⟨⟨hcz,hc⟩,_⟩,heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl,rfl⟩ | ⟨_,h2'⟩
   ·exact hcz rfl
   ·exact q03 z2 zp2 hf2.1 (congrArg s h2'.symm)
  have hd3:Disjoint ((MD2_ns.image fun d=>s(z2,d)) ∪ (MC2_ns.image fun c=>s(c,zp2)))
    (if s(z2,zp2) ∈ U2 then {s(z2,zp2)} else ∅):=by
   rw [Finset.disjoint_right];intro e he hU
   split_ifs at he with he2
   ·rw [Finset.mem_singleton] at he;subst he
    simp only [Finset.mem_union,Finset.mem_image,MD2_ns,MC2_ns,Finset.mem_filter,Finset.mem_erase,Sym2.eq_iff] at hU
    rcases hU with ⟨d,⟨⟨q1e,_⟩,_⟩,⟨_,h⟩ | ⟨h,_⟩⟩ | ⟨c,⟨⟨hcz,_⟩,_⟩,⟨h,_⟩ | ⟨_,h⟩⟩
    ·exact q1e h
    ·exact q2i h
    ·exact hcz h
    ·exact q2i h.symm
   ·exact absurd he (Finset.notMem_empty _)
  have qan:(U2 \ U1).card = MD2_ns.card + MC2_ns.card + (if s(z2,zp2) ∈ U2 then 1 else 0):=by
   rw [qfa,Finset.card_union_of_disjoint hd3,Finset.card_union_of_disjoint qp7,
    Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨_,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl),
    Finset.card_image_of_injective _ (fun a b h=>by rw [Sym2.eq_iff] at h;rcases h with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ <;> rfl)]
   split_ifs <;> simp
  rw [qan,qcx,q6u]
  have qf9:zp2 ∉ MD2_ns:=fun h=>(Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  have qlt:z2 ∉ MC2_ns:=fun h=>(Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  by_cases he2:s(z2,zp2) ∈ U2 <;> by_cases q3o:e2_to_z2 <;>
   simp [he2,q3o,qf9,qlt] <;> omega
 have qc7:(∑ v ∈ Zact,(L v).card) ≤ (Ustar G C).card:=by
  have qdn:∑ v ∈ Zact,(L v).card ≤ ∑ v ∈ ({z1,zp1,z2,zp2}:Finset (Fin n)),(L v).card:=
   Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have qp8:∑ v ∈ ({z1,zp1,z2,zp2}:Finset (Fin n)),(L v).card =
    (L z1).card + (L zp1).card + (L z2).card + (L zp2).card:=by
   rw [Finset.sum_insert (by simp [q2h,q5z,q1z]),
    Finset.sum_insert (by simp [q20.symm,q0h]),Finset.sum_pair q2i];omega
  have qn8:(Ustar G C).card = U1.card + (U2 \ U1).card:=by
   have q4y:Disjoint U1 (U2 \ U1):=Finset.disjoint_sdiff
   rw [show Ustar G C = U1 ∪ (U2 \ U1) by rw [q4q,Finset.union_sdiff_self_eq_union],
    Finset.card_union_of_disjoint q4y]
  omega
 let topOf:Fin n→ ℕ:=fun v=>if h:isOwn v then Classical.choose h else 0
 have q55:=z093 hL q01 h4 qdf q00 hne Zact Zhas L topOf
  (Finset.filter_subset _ _)
  (fun v hv=>(Finset.mem_filter.mp hv).2)
  (fun v hv u hu=>by
   have hv':=(Finset.mem_filter.mp hv).1
   simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
   rcases hv' with rfl | rfl | rfl | rfl
   ·rw [qcw] at hu;split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf1.1
     ·exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [q6t] at hu;split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf1.1.symm
     ·exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [qcx] at hu;split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf2.1
     ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
    ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
   ·rw [q6u] at hu;split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf2.1.symm
     ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
    ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm)
  q8w
  (fun v hv=>by have h:=(Finset.mem_filter.mp hv).2;simp only [topOf,dif_pos h];exact (Classical.choose_spec h).1)
  (fun v hv=>by
   have h:=(Finset.mem_filter.mp hv).2;simp only [topOf,dif_pos h]
   have hsp:=Classical.choose_spec h
   have q3f:=z128 hL.1 h4 s z1 g1 g2 hsp.1
   rwa [hsp.2] at q3f)
  (fun v1 hv1 v2 hv2 heq=>by
   have h1:=(Finset.mem_filter.mp hv1).2;have h2:=(Finset.mem_filter.mp hv2).2
   simp only [topOf,dif_pos h1,dif_pos h2] at heq
   have qhm:=Classical.choose_spec h1;have qhn:=Classical.choose_spec h2
   rw [← qhm.2,heq,qhn.2])
 have qg5:(Ustar G C).card + U12.card = U1.card + U2.card:=by
  rw [q4q];exact Finset.card_union_add_card_inter U1 U2
 have qgc:2 * (centreless G C).card + Extra.card + U12.card + 2 ≤ Znew.card + loss1 + loss2:=by
  have qn9:2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (∑ v ∈ Zact,(L v).card) + Znew.card:=q55
  omega
 let A1_edge:Fin n→ Prop:=fun v=>
  (v = z1∧ ∃ d ∈ D1.erase zp1,s(z1,d) ∈ U1 \ E2)∨ 
  (v = zp1∧ ∃ c ∈ C1.erase z1,s(c,zp1) ∈ U1 \ E2)
 let A2_edge:Fin n→ Prop:=fun v=>
  (v = z2∧ ∃ d ∈ D2.erase zp2,s(z2,d) ∈ U2 \ E1)∨ 
  (v = zp2∧ ∃ c ∈ C2.erase z2,s(c,zp2) ∈ U2 \ E1)
 set A1:=(Znew ∩ {z1,zp1}).filter (fun v=>
  A1_edge v∧ ∃ a ∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g1∧ v ∈ side (n:=n) C a (1 - b))
 set A2:=(Znew ∩ {z2,zp2}).filter (fun v=>
  A2_edge v∧ ∃ a ∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b = ∅∧ OrReaches n C (opnd C a b) g2∧ v ∈ side (n:=n) C a (1 - b))
 set Zconf:=(Znew \ (A1 ∪ A2)).filter (fun v=>
  s v = s zp1∧ ∃ mv ∈ Extra,orIn n C (n + mv) = {v}∧ 
   ∃ u':Fin n,s u' = s z1∧ ∃ mu ∈ Extra,orIn n C (n + mu) = {u'})
 have qao:∀ v ∈ Znew ∩ {z1,zp1},A1_edge v→ v ∈ A1∨ v ∈ Zconf:=by
  intro v hv qfb
  have q2k:v ∈ Znew:=(Finset.mem_inter.mp hv).1
  have q21:¬ isOwn v:=fun ho=>(Finset.mem_sdiff.mp q2k).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q2k).1,ho⟩)
  rcases qfb with ⟨q30,d,hd,hzd⟩ | ⟨q30,c,hc,qbk⟩
  ·rw [q30] at hv q2k q21 ⊢
   have q1e:d ≠ zp1:=(Finset.mem_erase.mp hd).1
   have qlu:d ∈ D1:=Finset.mem_of_mem_erase hd
   have qlv:s(z1,d) ∈ Ustar G C:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd).1).1
   have qfc:s(z1,d) ∉ E2:=(Finset.mem_sdiff.mp hzd).2
   have qbu:gateVal n C g2 (pairInput z1 d) = false:=by
    rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.2.1 d qlu).symm];exact qfc
   have hnw:
     (gateVal n C g1 (pairInput z1 d) = true→ 
      (¬ ∀ x,gateVal n C g1 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s z1→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d))∧ 
     (gateVal n C g2 (pairInput z1 d) = true→ 
      (¬ ∀ x,gateVal n C g2 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s z1→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d)):=
    ⟨fun _=>⟨z056 h4 hf1 qlu q1e,fun w hsw hw=>z054 q03 h4 hf1 hw hsw qlu q1e⟩,
    fun h2=>(by rw [qbu] at h2;cases h2)⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qlv hnw
     (fun h=>by rw [qbu] at h;cases h.2.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨qa2,_⟩
   ·exact absurd hA q21
   ·have q56:g = g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv,Or.inl ⟨rfl,d,hd,hzd⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·exact absurd qa2 q02
  ·rw [q30] at hv q2k q21 ⊢
   have qna:c ≠ z1:=(Finset.mem_erase.mp hc).1
   have qlw:c ∈ C1:=Finset.mem_of_mem_erase hc
   have qfd:s(zp1,c) ∈ Ustar G C:=by rw [Sym2.eq_swap];exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp qbk).1).1
   have qby:s(zp1,c) ∉ E2:=by rw [Sym2.eq_swap];exact (Finset.mem_sdiff.mp qbk).2
   have qbu:gateVal n C g2 (pairInput zp1 c) = false:=by
    rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf2 (hf1.2.2.2.1 c qlw).symm];exact qby
   have hnw:
     (gateVal n C g1 (pairInput zp1 c) = true→ 
      (¬ ∀ x,gateVal n C g1 x = true→ x c = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s zp1→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c))∧ 
     (gateVal n C g2 (pairInput zp1 c) = true→ 
      (¬ ∀ x,gateVal n C g2 x = true→ x c = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s zp1→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c)):=
    ⟨fun _=>⟨z055 h4 hf1 qlw qna,fun w hsw hw=>z053 q03 h4 hf1 hw hsw qlw qna⟩,
    fun h2=>(by rw [qbu] at h2;cases h2)⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qfd hnw
     (fun h=>by rw [qbu] at h;cases h.2.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨hsv,_,_,_,g,hg,hgv,_,_,g',hg',_,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
   ·exact absurd hA q21
   ·have q56:g = g1:=hg.resolve_right (fun h=>by rw [h,qbu] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv,Or.inr ⟨rfl,c,hc,qbk⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·by_cases hA1:zp1 ∈ A1
    ·exact Or.inl hA1
    ·right
     have qp9:zp1 ∉ A2:=fun h=>by
      have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
      simp only [Finset.mem_insert,Finset.mem_singleton] at this
      exact this.elim q20.symm q0h
     have qfe:mv ∈ Extra:=q0w mv hmv (hg'.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     have qap:mu ∈ Extra:=q0w mu hmu (hg.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨q2k,fun h=>(Finset.mem_union.mp h).elim hA1 qp9⟩,
      hsv,mv,qfe,q05,u',q24,mu,qap,q06⟩
 have qaq:∀ v ∈ Znew ∩ {z2,zp2},A2_edge v→ v ∈ A2∨ v ∈ Zconf:=by
  intro v hv qfb
  have q2k:v ∈ Znew:=(Finset.mem_inter.mp hv).1
  have q21:¬ isOwn v:=fun ho=>(Finset.mem_sdiff.mp q2k).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp q2k).1,ho⟩)
  rcases qfb with ⟨q30,d,hd,hzd⟩ | ⟨q30,c,hc,qbk⟩
  ·rw [q30] at hv q2k q21 ⊢
   have q1e:d ≠ zp2:=(Finset.mem_erase.mp hd).1
   have q4e:d ∈ D2:=Finset.mem_of_mem_erase hd
   have qlv:s(z2,d) ∈ Ustar G C:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd).1).1
   have qff:s(z2,d) ∉ E1:=(Finset.mem_sdiff.mp hzd).2
   have qbv:gateVal n C g1 (pairInput z2 d) = false:=by
    rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.2.1 d q4e).symm];exact qff
   have hnw:
     (gateVal n C g1 (pairInput z2 d) = true→ 
      (¬ ∀ x,gateVal n C g1 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s z2→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d))∧ 
     (gateVal n C g2 (pairInput z2 d) = true→ 
      (¬ ∀ x,gateVal n C g2 x = true→ x d = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s z2→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w d)):=
    ⟨fun h1=>(by rw [qbv] at h1;cases h1),
    fun _=>⟨z056 h4 hf2 q4e q1e,fun w hsw hw=>z054 q03 h4 hf2 hw hsw q4e q1e⟩⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qlv hnw
     (fun h=>by rw [qbv] at h;cases h.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨qa2,_⟩
   ·exact absurd hA q21
   ·have q56:g = g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv,Or.inl ⟨rfl,d,hd,hzd⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·exact absurd (hsz.trans qa2) q02
  ·rw [q30] at hv q2k q21 ⊢
   have qnb:c ≠ z2:=(Finset.mem_erase.mp hc).1
   have q4d:c ∈ C2:=Finset.mem_of_mem_erase hc
   have qfd:s(zp2,c) ∈ Ustar G C:=by rw [Sym2.eq_swap];exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp qbk).1).1
   have qbz:s(zp2,c) ∉ E1:=by rw [Sym2.eq_swap];exact (Finset.mem_sdiff.mp qbk).2
   have qbv:gateVal n C g1 (pairInput zp2 c) = false:=by
    rw [Bool.eq_false_iff,ne_eq,z052 q03 h4 hf1 (hf2.2.2.2.1 c q4d).symm];exact qbz
   have hnw:
     (gateVal n C g1 (pairInput zp2 c) = true→ 
      (¬ ∀ x,gateVal n C g1 x = true→ x c = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s zp2→ (∀ x,gateVal n C g1 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c))∧ 
     (gateVal n C g2 (pairInput zp2 c) = true→ 
      (¬ ∀ x,gateVal n C g2 x = true→ x c = true→ graphFun G ∅ x = true)∧ 
      (∀ w:Fin n,s w = s zp2→ (∀ x,gateVal n C g2 x = true→ x w = true→ graphFun G ∅ x = true)→ G.Adj w c)):=
    ⟨fun h1=>(by rw [qbv] at h1;cases h1),
    fun _=>⟨z055 h4 hf2 q4d qnb,fun w hsw hw=>z053 q03 h4 hf2 hw hsw q4d qnb⟩⟩
   rcases z072 q03 h4 hL q01 q00 hf1 hf2 hsz q1l qfd hnw
     (fun h=>by rw [qbv] at h;cases h.1) with
    hA | ⟨a,haC,b,g,hg,hgv,q0g,hrb,hzs⟩ | ⟨hsv,_,_,_,g,hg,hgv,_,_,g',hg',_,_,mv,hmv,q38,q05,u',_,q24,mu,hmu,q3j,q06⟩
   ·exact absurd hA q21
   ·have q56:g = g2:=hg.resolve_left (fun h=>by rw [h,qbv] at hgv;cases hgv)
    rw [q56] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv,Or.inr ⟨rfl,c,hc,qbk⟩,a,haC,b,q0g,hrb,hzs⟩)
   ·by_cases hA2:zp2 ∈ A2
    ·exact Or.inl hA2
    ·right
     have qpa:zp2 ∉ A1:=fun h=>by
      have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
      simp only [Finset.mem_insert,Finset.mem_singleton] at this
      exact this.elim q1z.symm q0h.symm
     have qfe:mv ∈ Extra:=q0w mv hmv (hg'.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     have qap:mu ∈ Extra:=q0w mu hmu (hg.imp (fun h=>by rwa [← h]) (fun h=>by rwa [← h]))
     exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨q2k,fun h=>(Finset.mem_union.mp h).elim qpa hA2⟩,
      hsv,mv,qfe,q05,u',q24,mu,qap,q06⟩
 have qjh:(Znew ∩ {z1,zp1}).card + loss1 ≤ A1.card + (Zconf ∩ {zp1}).card + 1 + U12.card:=by
  have q3e:A1 ∪ (Zconf ∩ {zp1}) ⊆ Znew ∩ {z1,zp1}:=by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv;have h1:=(Finset.mem_inter.mp hv).1;have h2:=(Finset.mem_inter.mp hv).2
   rw [Finset.mem_singleton] at h2;subst h2
   exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).1,by simp⟩
  have qc8:Disjoint A1 (Zconf ∩ {zp1}):=by
   rw [Finset.disjoint_left];intro v hv1 hv2
   exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).1).2 (Finset.mem_union_left _ hv1)
  have qfg:(A1 ∪ (Zconf ∩ {zp1})).card = A1.card + (Zconf ∩ {zp1}).card:=
   Finset.card_union_of_disjoint qc8
  have qfh:z1 ∈ Znew→ (∃ d ∈ MD1_ns,s(z1,d) ∉ E2)→ z1 ∈ A1 ∪ (Zconf ∩ {zp1}):=by
   intro qik ⟨d,hd,qfi⟩
   have qil:=Finset.mem_erase.mp hd
   have q98:=Finset.mem_filter.mp qil.2
   have hU1:s(z1,d) ∈ U1:=Finset.mem_inter.mpr ⟨q98.2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ q98.1)⟩
   rcases qao z1 (Finset.mem_inter.mpr ⟨qik,by simp⟩)
     (Or.inl ⟨rfl,d,Finset.mem_erase.mpr ⟨qil.1,q98.1⟩,Finset.mem_sdiff.mpr ⟨hU1,qfi⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact absurd (Finset.mem_filter.mp hC).2.1 q02
  have qc0:zp1 ∈ Znew→ (∃ c ∈ MC1_ns,s(c,zp1) ∉ E2)→ zp1 ∈ A1 ∪ (Zconf ∩ {zp1}):=by
   intro qar ⟨c,hc,qfi⟩
   have qim:=Finset.mem_erase.mp hc
   have q99:=Finset.mem_filter.mp qim.2
   have hU1:s(c,zp1) ∈ U1:=Finset.mem_inter.mpr ⟨q99.2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ q99.1)⟩
   rcases qao zp1 (Finset.mem_inter.mpr ⟨qar,by simp⟩)
     (Or.inr ⟨rfl,c,Finset.mem_erase.mpr ⟨qim.1,q99.1⟩,Finset.mem_sdiff.mpr ⟨hU1,qfi⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hC,by simp⟩)
  have qpm:((Znew ∩ {z1,zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))).card + loss1 ≤ 1 + U12.card:=by
   set R:=(Znew ∩ {z1,zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))
   have qas:R ⊆ {z1,zp1}:=Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
   have qpb:R.card ≤ 2:=(Finset.card_le_card qas).trans (by rw [Finset.card_pair q2h])
   have q3c:z1 ∈ R→ ∀ d ∈ MD1_ns,s(z1,d) ∈ U12:=by
    intro hR d hd
    have q98:=Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)
    have hU1:s(z1,d) ∈ U1:=Finset.mem_inter.mpr ⟨q98.2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ q98.1)⟩
    by_contra hnu
    have qfi:s(z1,d) ∉ E2:=fun h=>hnu (Finset.mem_inter.mpr ⟨hU1,Finset.mem_inter.mpr ⟨q98.2,h⟩⟩)
    exact (Finset.mem_sdiff.mp hR).2 (qfh (Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1 ⟨d,hd,qfi⟩)
   have q2u:zp1 ∈ R→ ∀ c ∈ MC1_ns,s(c,zp1) ∈ U12:=by
    intro hR c hc
    have q99:=Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    have hU1:s(c,zp1) ∈ U1:=Finset.mem_inter.mpr ⟨q99.2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ q99.1)⟩
    by_contra hnu
    have qfi:s(c,zp1) ∉ E2:=fun h=>hnu (Finset.mem_inter.mpr ⟨hU1,Finset.mem_inter.mpr ⟨q99.2,h⟩⟩)
    exact (Finset.mem_sdiff.mp hR).2 (qc0 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1 ⟨c,hc,qfi⟩)
   have q91:zp1 ∈ Znew→ MC1_ns.Nonempty:=by
    intro qar
    have q8q:(L zp1).Nonempty:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp qar).1).2
    by_contra q0g
    have q3o:e1_to_z1:=Or.inr (Or.inr q0g)
    rw [q6t,if_neg (fun h=>h.2 q3o)] at q8q
    exact q0g q8q
   have q7u:¬ (z1 ∈ R∧ zp1 ∈ R):=by
    rintro ⟨qnc,qin⟩
    have qar:zp1 ∈ Znew:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp qin).1).1
    have qik:z1 ∈ Znew:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp qnc).1).1
    obtain ⟨c,hc⟩:=q91 qar
    have qfj:MD1_ns.Nonempty:=by
     have q8q:(L z1).Nonempty:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp qik).1).2
     by_contra q0g
     have qfk:¬ isOwn z1:=fun ho=>(Finset.mem_sdiff.mp qik).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp qik).1,ho⟩)
     have qfl:¬ e1_to_z1:=fun h=>h.elim q0g (fun h=>h.elim qfk (fun h=>h ⟨c,hc⟩))
     rw [qcw,if_neg (fun h=>qfl h.2)] at q8q
     exact q0g q8q
    obtain ⟨d,hd⟩:=qfj
    have he1:=q3c qnc d hd
    have he2:=q2u qin c hc
    have qlx:s(z1,d) ≠ s(c,zp1):=by
     intro heq;rw [Sym2.eq_iff] at heq
     rcases heq with ⟨rfl,_⟩ | ⟨_,h2'⟩
     ·exact (Finset.mem_erase.mp hc).1 rfl
     ·exact q02 ((z046 q03 hf1 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1).symm.trans
       (by rw [← h2'];exact z047 q03 hf1 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).1))
    have hle:=Finset.card_le_card (Finset.insert_subset he1 (Finset.singleton_subset_iff.mpr he2))
    rw [Finset.card_pair qlx] at hle;omega
   have qly:R.card ≤ 1:=by
    by_contra hgt;push Not at hgt
    have qnd:R = {z1,zp1}:=Finset.eq_of_subset_of_card_le qas (by rw [Finset.card_pair q2h];omega)
    exact q7u ⟨by rw [qnd];simp,by rw [qnd];simp⟩
   by_cases qc1:MC1 = C1∧ MD1 = D1
   ·simp only [loss1,if_pos qc1]
    by_cases hR0:R.card = 0
    ·omega
    ·
     obtain ⟨v,hvR⟩:=Finset.card_pos.mp (by omega:0 < R.card)
     have qji:1 ≤ U12.card:=by
      have hv:=qas hvR
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with q30 | q30
      ·rw [q30] at hvR
       obtain ⟨d,hd,q1e⟩:=z050 hf1
       have q7s:d ∈ MD1_ns:=Finset.mem_erase.mpr ⟨q1e,by rw [qc1.2];exact hd⟩
       exact Finset.card_pos.mpr ⟨s(z1,d),q3c hvR d q7s⟩
      ·rw [q30] at hvR
       obtain ⟨c,hc,hcz⟩:=z049 hf1
       have q7t:c ∈ MC1_ns:=Finset.mem_erase.mpr ⟨hcz,by rw [qc1.1];exact hc⟩
       exact Finset.card_pos.mpr ⟨s(c,zp1),q2u hvR c q7t⟩
     omega
   ·simp only [loss1,if_neg qc1];omega
  have qfm:=Finset.card_le_card q3e
  have qio:=z019 q3e
  omega
 have qjj:(Znew ∩ {z2,zp2}).card + loss2 ≤ A2.card + (Zconf ∩ {zp2}).card + 1:=by
  have q57:A2 ∪ (Zconf ∩ {zp2}) ⊆ Znew ∩ {z2,zp2}:=by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv;have h1:=(Finset.mem_inter.mp hv).1;have h2:=(Finset.mem_inter.mp hv).2
   rw [Finset.mem_singleton] at h2;subst h2
   exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).1,by simp⟩
  have q1n:Disjoint A2 (Zconf ∩ {zp2}):=by
   rw [Finset.disjoint_left];intro v hv1 hv2
   exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).1).2 (Finset.mem_union_right _ hv1)
  have qfg:(A2 ∪ (Zconf ∩ {zp2})).card = A2.card + (Zconf ∩ {zp2}).card:=
   Finset.card_union_of_disjoint q1n
  set R:=(Znew ∩ {z2,zp2}) \ (A2 ∪ (Zconf ∩ {zp2}))
  have qas:R ⊆ {z2,zp2}:=Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
  have qfn:zp2 ∉ R:=by
   intro hR
   have qip:zp2 ∈ Znew:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1
   have q3l:MC2_ns.Nonempty:=by
    have q8q:(L zp2).Nonempty:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp qip).1).2
    by_contra q0g
    have q3o:e2_to_z2:=Or.inr (Or.inr q0g)
    rw [q6u,if_neg (fun h=>h.2 q3o)] at q8q
    exact q0g q8q
   obtain ⟨c,hc⟩:=q3l
   have q99:=Finset.mem_filter.mp hc
   have q7v:s(c,zp2) ∈ U2 \ E1:=Finset.mem_sdiff.mpr
    ⟨(Finset.mem_sdiff.mp q99.2).1,fun hE1=>(Finset.mem_sdiff.mp q99.2).2
     (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp q99.2).1).1,hE1⟩)⟩
   rcases qaq zp2 (Finset.mem_inter.mpr ⟨qip,by simp⟩) (Or.inr ⟨rfl,c,q99.1,q7v⟩) with hA | hC
   ·exact (Finset.mem_sdiff.mp hR).2 (Finset.mem_union_left _ hA)
   ·exact (Finset.mem_sdiff.mp hR).2 (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hC,by simp⟩))
  have q8i:R ⊆ {z2}:=by
   intro v hv
   have hv':=qas hv;simp only [Finset.mem_insert,Finset.mem_singleton] at hv' ⊢
   exact hv'.resolve_right (fun h=>qfn (h ▸ hv))
  have qly:R.card ≤ 1:=(Finset.card_le_card q8i).trans (by simp)
  have qlz:R.card + loss2 ≤ 1:=by
   by_cases qm0:z2 ∈ R
   ·have qjk:z2 ∈ Znew:=(Finset.mem_inter.mp (Finset.mem_sdiff.mp qm0).1).1
    have q5t:¬ MD2_ns.Nonempty:=by
     rintro ⟨d,hd⟩
     have q98:=Finset.mem_filter.mp hd
     have q7v:s(z2,d) ∈ U2 \ E1:=Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp q98.2).1,fun hE1=>(Finset.mem_sdiff.mp q98.2).2
       (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp q98.2).1).1,hE1⟩)⟩
     rcases qaq z2 (Finset.mem_inter.mpr ⟨qjk,by simp⟩) (Or.inl ⟨rfl,d,q98.1,q7v⟩) with hA | hC
     ·exact (Finset.mem_sdiff.mp qm0).2 (Finset.mem_union_left _ hA)
     ·exact absurd (hsz.trans (Finset.mem_filter.mp hC).2.1) q02
    have qc2:¬ MC2_ns.Nonempty:=by
     intro q3l
     have q8q:(L z2).Nonempty:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp qjk).1).2
     have qfk:¬ isOwn z2:=fun ho=>(Finset.mem_sdiff.mp qjk).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp qjk).1,ho⟩)
     have qfl:¬ e2_to_z2:=fun h=>h.elim q5t (fun h=>h.elim qfk (fun h=>h q3l))
     rw [qcx,if_neg (fun h=>qfl h.2)] at q8q
     exact q5t q8q
    have qne:loss2 = 0:=by
     simp only [loss2,ite_eq_right_iff];rintro ⟨q75,qba⟩
     exfalso
     obtain ⟨c,hc,hcz⟩:=z049 hf2
     obtain ⟨d,hd,q1e⟩:=z050 hf2
     have qnf:s(c,zp2) ∈ U2:=Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp (by rw [q75];exact hc:c ∈ MC2)).2,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)⟩
     have qng:s(z2,d) ∈ U2:=Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp (by rw [qba];exact hd:d ∈ MD2)).2,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd)⟩
     have qm1:s(c,zp2) ∈ U1:=by
      by_contra hnu;exact qc2 ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hcz,hc⟩,Finset.mem_sdiff.mpr ⟨qnf,hnu⟩⟩⟩
     have qm2:s(z2,d) ∈ U1:=by
      by_contra hnu;exact q5t ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨q1e,hd⟩,Finset.mem_sdiff.mpr ⟨qng,hnu⟩⟩⟩
     have qiq:s(c,zp2) ≠ s(z2,d):=by
      intro heq;rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl,_⟩ | ⟨h1',_⟩
      ·exact hcz rfl
      ·exact q03 z2 zp2 hf2.1 ((z046 q03 hf2 hc).symm.trans (by rw [h1'];exact z047 q03 hf2 hd))
     have hle:({s(c,zp2),s(z2,d)}:Finset (Sym2 (Fin n))).card ≤ U12.card:=
      Finset.card_le_card (Finset.insert_subset (Finset.mem_inter.mpr ⟨qm1,qnf⟩)
       (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨qm2,qng⟩)))
     rw [Finset.card_pair qiq] at hle;omega
    omega
   ·have hR0:R = ∅:=by
     ext v;simp only [Finset.notMem_empty,iff_false];intro hv
     exact qm0 ((Finset.mem_singleton.mp (q8i hv)) ▸ hv)
    rw [hR0,Finset.card_empty];simp [loss2];split_ifs <;> omega
  have qfm:=Finset.card_le_card q57
  have qio:R.card = (Znew ∩ {z2,zp2}).card - (A2 ∪ (Zconf ∩ {zp2})).card:=z019 q57
  omega
 have qfo:Znew.card = (Znew ∩ {z1,zp1}).card + (Znew ∩ {z2,zp2}).card:=by
  have hU:Znew = (Znew ∩ {z1,zp1}) ∪ (Znew ∩ {z2,zp2}):=by
   ext v;simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
   constructor
   ·intro hv
    have hv4:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv4
    rcases hv4 with rfl | rfl | rfl | rfl
    ·exact Or.inl ⟨hv,Or.inl rfl⟩
    ·exact Or.inl ⟨hv,Or.inr rfl⟩
    ·exact Or.inr ⟨hv,Or.inl rfl⟩
    ·exact Or.inr ⟨hv,Or.inr rfl⟩
   ·rintro (⟨hv,_⟩ | ⟨hv,_⟩) <;> exact hv
  have hd:Disjoint (Znew ∩ {z1,zp1}) (Znew ∩ {z2,zp2}):=by
   rw [Finset.disjoint_left];intro v h1 h2
   have hv1:=(Finset.mem_inter.mp h1).2;have hv2:=(Finset.mem_inter.mp h2).2
   simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 hv2
   rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
   ·exact q5z h
   ·exact q1z h
   ·exact q20 h.symm
   ·exact q0h h
  conv_lhs=>rw [hU]
  exact Finset.card_union_of_disjoint hd
 have qcy:Zconf.card = (Zconf ∩ {zp1}).card + (Zconf ∩ {zp2}).card:=by
  have q0c:Zconf ⊆ {zp1,zp2}:=by
   intro v hv
   have hvf:=Finset.mem_filter.mp hv
   have hv4:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvf.1).1).1).1
   simp only [Finset.mem_insert,Finset.mem_singleton] at hv4 ⊢
   rcases hv4 with rfl | rfl | rfl | rfl
   ·exact absurd hvf.2.1 q02
   ·exact Or.inl rfl
   ·exact absurd (hsz.trans hvf.2.1) q02
   ·exact Or.inr rfl
  have hU:Zconf = (Zconf ∩ {zp1}) ∪ (Zconf ∩ {zp2}):=by
   ext v;simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_singleton]
   constructor
   ·intro hv
    have:=q0c hv;simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with rfl | rfl
    ·exact Or.inl ⟨hv,rfl⟩
    ·exact Or.inr ⟨hv,rfl⟩
   ·rintro (⟨hv,_⟩ | ⟨hv,_⟩) <;> exact hv
  have hd:Disjoint (Zconf ∩ {zp1}) (Zconf ∩ {zp2}):=by
   rw [Finset.disjoint_left];intro v h1 h2
   have hv1:=Finset.mem_singleton.mp (Finset.mem_inter.mp h1).2
   have hv2:=Finset.mem_singleton.mp (Finset.mem_inter.mp h2).2
   exact q0h (hv1.symm.trans hv2)
  conv_lhs=>rw [hU]
  exact Finset.card_union_of_disjoint hd
 have q7w:2 * (centreless G C).card + Extra.card ≤ A1.card + A2.card + Zconf.card:=by omega
 have q3p:Disjoint A1 A2:=by
  rw [Finset.disjoint_left];intro v h1 h2
  have hv1:=(Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).2
  have hv2:=(Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).2
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv1 hv2
  rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
  ·exact q5z h
  ·exact q1z h
  ·exact q20 h.symm
  ·exact q0h h
 have qc3:Disjoint (A1 ∪ A2) Zconf:=by
  rw [Finset.disjoint_left];intro v hA hZ
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hZ).1).2 hA
 have qjl:A1.card + A2.card + Zconf.card ≤ 4:=by
  have q0c:(A1 ∪ A2) ∪ Zconf ⊆ {z1,zp1,z2,zp2}:=by
   intro v hv
   have hvZ:v ∈ Znew:=by
    rcases Finset.mem_union.mp hv with hA | hZ
    ·rcases Finset.mem_union.mp hA with h1 | h2
     ·exact (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).1
     ·exact (Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).1
    ·exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hZ).1).1
   exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvZ).1).1
  have hle:=Finset.card_le_card q0c
  rw [Finset.card_union_of_disjoint qc3,Finset.card_union_of_disjoint q3p,qbx] at hle
  exact hle
 let mixGate:Fin n→ ℕ:=fun v=>
  if h:∃ mv ∈ Extra,orIn n C (n + mv) = {v} then Classical.choose h else 0
 set SingleMix:=Zconf.image mixGate
 have q12:SingleMix ⊆ Extra:=by
  intro k hk;simp only [SingleMix,Finset.mem_image] at hk
  rcases hk with ⟨v,hv,rfl⟩
  have hex:∃ mv ∈ Extra,orIn n C (n + mv) = {v}:=by
   rcases (Finset.mem_filter.mp hv).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos hex];exact (Classical.choose_spec hex).1
 have q2l:∀ k ∈ SingleMix,∃ v ∈ Zconf,orIn n C (n + k) = {v}:=by
  intro k hk;simp only [SingleMix,Finset.mem_image] at hk
  rcases hk with ⟨v,hv,rfl⟩
  have hex:∃ mv ∈ Extra,orIn n C (n + mv) = {v}:=by
   rcases (Finset.mem_filter.mp hv).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos hex];exact ⟨v,hv,(Classical.choose_spec hex).2⟩
 have q0x:SingleMix.card = Zconf.card:=by
  apply Finset.card_image_of_injOn
  intro v1 hv1 v2 hv2 heq
  have q94:∃ mv ∈ Extra,orIn n C (n + mv) = {v1}:=by
   rcases (Finset.mem_filter.mp hv1).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  have qb2:∃ mv ∈ Extra,orIn n C (n + mv) = {v2}:=by
   rcases (Finset.mem_filter.mp hv2).2.2 with ⟨mv,hmv,hor,_⟩;exact ⟨mv,hmv,hor⟩
  simp only [mixGate,dif_pos q94,dif_pos qb2] at heq
  have h1:=(Classical.choose_spec q94).2
  have h2:=(Classical.choose_spec qb2).2
  rw [heq] at h1
  exact Finset.singleton_injective (h1.symm.trans h2)
 have q8j:∀ a ∈ centreless G C,∀ b:Fin 2,side (n:=n) C a b = ∅→ 
   ∀ A':Finset (Fin n),A'.Nonempty→ A' ⊆ A1 ∪ A2→ A' ⊆ side (n:=n) C a (1 - b)→ 
   let HW:=Extra.filter (fun k=>2 ≤ (orIn n C (n + k)).card)
   A'.card ≤ HW.card + 1:=by
  intro a haC b q0g A' ql1 q6v q4r HW
  have q25:a ∈ tops G C:=(Finset.mem_filter.mp haC).1
  have ha':=z098.mp q25
  have q8k:OrReaches n C (opnd C a b) g1∨ OrReaches n C (opnd C a b) g2:=by
   have qaz:=(z103 hL q01 hne q00 (opnd C a b)
    (by have:=z104 hL.1 ha'.1 b;omega) (z130 hL hne q25 b) (fun _=>true)).mp
    (z138 hL.1 (opnd C a b) (by have:=z104 hL.1 ha'.1 b;omega))
   rcases qaz with ⟨u,hu,_⟩ | ⟨hr,_⟩ | ⟨hr,_⟩
   ·rw [show orIn n C (opnd C a b) = ∅ from q0g] at hu;exact absurd hu (Finset.notMem_empty _)
   ·exact Or.inl hr
   ·exact Or.inr hr
  have q2n:∀ k,OrReaches n C (opnd C a (1 - b)) k→ k ∈ lam G C ∪ FacAll→ 
    (orIn n C (n + k) ∩ A').card ≤ 1:=by
   intro k _ hk
   by_contra hgt;push Not at hgt
   obtain ⟨u,hu,v,hv,huv⟩:=Finset.one_lt_card.mp hgt
   have hu':=Finset.mem_inter.mp hu;have hv':=Finset.mem_inter.mp hv
   have q15:s u = s v:=by
    rcases Finset.mem_union.mp hk with qa5 | q6y
    ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
     obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
     have q0c:=z109 hrt
     have hwm:w ∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
     have hau:G.Adj w u:=by fin_cases btp;exact (z132 hL.1 q2v (q0c hu'.1) hwm).symm;exact z132 hL.1 q2v hwm (q0c hu'.1)
     have hav:G.Adj w v:=by fin_cases btp;exact (z132 hL.1 q2v (q0c hv'.1) hwm).symm;exact z132 hL.1 q2v hwm (q0c hv'.1)
     exact z015 (q03 w u hau).symm (q03 w v hav).symm
    ·simp only [FacAll,Finset.mem_union] at q6y
     rcases q6y with (h | h) | (h | h)
     ·exact (z046 q03 hf1 ((q1j k h).2.2.1 hu'.1)).trans (z046 q03 hf1 ((q1j k h).2.2.1 hv'.1)).symm
     ·exact (z047 q03 hf1 ((q1s k h).2.2.1 hu'.1)).trans (z047 q03 hf1 ((q1s k h).2.2.1 hv'.1)).symm
     ·exact (z046 q03 hf2 ((q22 k h).2.2.1 hu'.1)).trans (z046 q03 hf2 ((q22 k h).2.2.1 hv'.1)).symm
     ·exact (z047 q03 hf2 ((q2j k h).2.2.1 hu'.1)).trans (z047 q03 hf2 ((q2j k h).2.2.1 hv'.1)).symm
   have q7x:((u = z1∧ v = z2)∨ (u = z2∧ v = z1))∨ 
     ((u = zp1∧ v = zp2)∨ (u = zp2∧ v = zp1)):=by
    have qir:∀ x ∈ A',x = z1∨ x = zp1∨ x = z2∨ x = zp2:=fun x hx=>by
     rcases Finset.mem_union.mp (q6v hx) with h1 | h2
     ·have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).2
      simp only [Finset.mem_insert,Finset.mem_singleton] at this
      rcases this with rfl | rfl;exact Or.inl rfl;exact Or.inr (Or.inl rfl)
     ·have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).2
      simp only [Finset.mem_insert,Finset.mem_singleton] at this
      rcases this with rfl | rfl;exact Or.inr (Or.inr (Or.inl rfl));exact Or.inr (Or.inr (Or.inr rfl))
    rcases qir u hu'.2 with rfl | rfl | rfl | rfl <;> rcases qir v hv'.2 with rfl | rfl | rfl | rfl
    ·exact absurd rfl huv
    ·exact absurd q15 q02
    ·exact Or.inl (Or.inl ⟨rfl,rfl⟩)
    ·exact absurd (q15.trans q1l.symm) q02
    ·exact absurd q15.symm q02
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans q15.symm) q02
    ·exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    ·exact Or.inl (Or.inr ⟨rfl,rfl⟩)
    ·exact absurd (hsz.trans q15) q02
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans (q15.trans q1l.symm)) q02
    ·exact absurd (q15.symm.trans q1l.symm) q02
    ·exact Or.inr (Or.inr ⟨rfl,rfl⟩)
    ·exact absurd (hsz.trans (q15.symm.trans q1l.symm)) q02
    ·exact absurd rfl huv
   have qat:z1 ∈ orIn n C (n + k)→ z2 ∈ orIn n C (n + k)→ z1 ∈ A'→ z2 ∈ A'→ False:=by
    intro q7y qau qnh qni
    have qis:z1 ∈ A1:=(Finset.mem_union.mp (q6v qnh)).resolve_right (fun h=>by
     have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2;simp [q5z,q1z] at this)
    have qit:z2 ∈ A2:=(Finset.mem_union.mp (q6v qni)).resolve_left (fun h=>by
     have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2;simp [q5z.symm,q20] at this)
    rcases q8k with qm3 | qm4
    ·
     obtain ⟨d1,hd1,qnj⟩:∃ d1 ∈ D1.erase zp1,s(z1,d1) ∈ U1 \ E2:=by
      rcases (Finset.mem_filter.mp qis).2.1 with ⟨_,h⟩ | ⟨heq,_⟩
      ·exact h
      ·exact absurd heq q2h
     have q6i:d1 ≠ zp1:=(Finset.mem_erase.mp hd1).1
     have qnk:d1 ∈ D1:=Finset.mem_of_mem_erase hd1
     have q3i:=z131 hL.1 q25 b qm3 (q4r qni)
     have q4s:G.Adj z2 d1:=z054 q03 h4 hf1 q3i hsz.symm qnk q6i
     have q4t:G.Adj z1 d1:=(hf1.2.2.2.2.1 d1 qnk).symm
     rcases Finset.mem_union.mp hk with qa5 | q6y
     ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w ∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj z1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q7y) hwm;exact (z132 hL.1 q2v hwm (q0c q7y)).symm
      have qfq:G.Adj z2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c qau) hwm;exact (z132 hL.1 q2v hwm (q0c qau)).symm
      have q8s:w = d1:=z102 h4 q5z qfp qfq q4t q4s
      subst q8s
      have q5g:s(z1,w) ∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp,q2v,(z1,w),⟨q0c q7y,hwm⟩,rfl⟩
       ·exact ⟨atp,q2v,(w,z1),⟨hwm,q0c q7y⟩,Sym2.eq_swap⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp qnj).1).1).2 q5g
     ·simp only [FacAll,Finset.mem_union] at q6y
      rcases q6y with (h | h) | (h | h)
      ·have q0c:=(q1j k h).2.2.1
       have heq:=z102 h4 q5z (hf1.2.2.2.1 z1 (q0c q7y)) (hf1.2.2.2.1 z2 (q0c qau)) q4t q4s
       exact q6i heq.symm
      ·exact q02 (z047 q03 hf1 ((q1s k h).2.2.1 q7y))
      ·have q0c:=(q22 k h).2.2.1
       have heq:=z102 h4 q5z (hf2.2.2.2.1 z1 (q0c q7y)) (hf2.2.2.2.1 z2 (q0c qau)) q4t q4s
       subst heq
       exact (Finset.mem_sdiff.mp qnj).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (q0c q7y)))
      ·exact q02 ((z047 q03 hf2 ((q2j k h).2.2.1 q7y)).trans q1l.symm)
    ·
     obtain ⟨d2,hd2,qnl⟩:∃ d2 ∈ D2.erase zp2,s(z2,d2) ∈ U2 \ E1:=by
      rcases (Finset.mem_filter.mp qit).2.1 with ⟨_,h⟩ | ⟨heq,_⟩
      ·exact h
      ·exact absurd heq q2i
     have q8y:d2 ≠ zp2:=(Finset.mem_erase.mp hd2).1
     have qnm:d2 ∈ D2:=Finset.mem_of_mem_erase hd2
     have q3i:=z131 hL.1 q25 b qm4 (q4r qnh)
     have q4u:G.Adj z1 d2:=z054 q03 h4 hf2 q3i hsz qnm q8y
     have q4v:G.Adj z2 d2:=(hf2.2.2.2.2.1 d2 qnm).symm
     rcases Finset.mem_union.mp hk with qa5 | q6y
     ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w ∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj z1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q7y) hwm;exact (z132 hL.1 q2v hwm (q0c q7y)).symm
      have qfq:G.Adj z2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c qau) hwm;exact (z132 hL.1 q2v hwm (q0c qau)).symm
      have q8s:w = d2:=z102 h4 q5z qfp qfq q4u q4v
      subst q8s
      have q5g:s(z2,w) ∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp,q2v,(z2,w),⟨q0c qau,hwm⟩,rfl⟩
       ·exact ⟨atp,q2v,(w,z2),⟨hwm,q0c qau⟩,Sym2.eq_swap⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp qnl).1).1).2 q5g
     ·simp only [FacAll,Finset.mem_union] at q6y
      rcases q6y with (h | h) | (h | h)
      ·have q0c:=(q1j k h).2.2.1
       have heq:=z102 h4 q5z (hf1.2.2.2.1 z1 (q0c q7y)) (hf1.2.2.2.1 z2 (q0c qau)) q4u q4v
       subst heq
       exact (Finset.mem_sdiff.mp qnl).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (q0c qau)))
      ·exact q02 (z047 q03 hf1 ((q1s k h).2.2.1 q7y))
      ·have q0c:=(q22 k h).2.2.1
       have heq:=z102 h4 q5z (hf2.2.2.2.1 z1 (q0c q7y)) (hf2.2.2.2.1 z2 (q0c qau)) q4u q4v
       exact q8y heq.symm
      ·exact q02 ((z047 q03 hf2 ((q2j k h).2.2.1 q7y)).trans q1l.symm)
   have q8l:zp1 ∈ orIn n C (n + k)→ zp2 ∈ orIn n C (n + k)→ zp1 ∈ A'→ zp2 ∈ A'→ False:=by
    intro q31 q4w qiu qiv
    have qfr:zp1 ∈ A1:=(Finset.mem_union.mp (q6v qiu)).resolve_right (fun h=>by
     have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2;simp [q20.symm,q0h] at this)
    have qfs:zp2 ∈ A2:=(Finset.mem_union.mp (q6v qiv)).resolve_left (fun h=>by
     have:=(Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2;simp [q1z.symm,q0h.symm] at this)
    rcases q8k with qm3 | qm4
    ·obtain ⟨c1,hc1,qiw⟩:∃ c1 ∈ C1.erase z1,s(c1,zp1) ∈ U1 \ E2:=by
      rcases (Finset.mem_filter.mp qfr).2.1 with ⟨heq,_⟩ | ⟨_,h⟩
      ·exact absurd heq q2h.symm
      ·exact h
     have q87:c1 ≠ z1:=(Finset.mem_erase.mp hc1).1
     have qnn:c1 ∈ C1:=Finset.mem_of_mem_erase hc1
     have q3i:=z131 hL.1 q25 b qm3 (q4r qiv)
     have q3q:G.Adj zp2 c1:=z053 q03 h4 hf1 q3i q1l.symm qnn q87
     have q3r:G.Adj zp1 c1:=(hf1.2.2.2.1 c1 qnn).symm
     rcases Finset.mem_union.mp hk with qa5 | q6y
     ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w ∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj zp1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q31) hwm;exact (z132 hL.1 q2v hwm (q0c q31)).symm
      have qfq:G.Adj zp2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q4w) hwm;exact (z132 hL.1 q2v hwm (q0c q4w)).symm
      have q8s:w = c1:=z102 h4 q0h qfp qfq q3r q3q
      subst q8s
      have q5g:s(w,zp1) ∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp,q2v,(zp1,w),⟨q0c q31,hwm⟩,Sym2.eq_swap⟩
       ·exact ⟨atp,q2v,(w,zp1),⟨hwm,q0c q31⟩,rfl⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp qiw).1).1).2 q5g
     ·simp only [FacAll,Finset.mem_union] at q6y
      rcases q6y with (h | h) | (h | h)
      ·exact q02.symm (z046 q03 hf1 ((q1j k h).2.2.1 q31))
      ·have q0c:=(q1s k h).2.2.1
       have heq:=z102 h4 q0h (hf1.2.2.2.2.1 zp1 (q0c q31)) (hf1.2.2.2.2.1 zp2 (q0c q4w)) q3r q3q
       exact q87 heq.symm
      ·exact q02.symm ((z046 q03 hf2 ((q22 k h).2.2.1 q31)).trans hsz.symm)
      ·have q0c:=(q2j k h).2.2.1
       have heq:=z102 h4 q0h (hf2.2.2.2.2.1 zp1 (q0c q31)) (hf2.2.2.2.2.1 zp2 (q0c q4w)) q3r q3q
       subst heq
       exact (Finset.mem_sdiff.mp qiw).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (q0c q31)))
    ·obtain ⟨c2,hc2,qix⟩:∃ c2 ∈ C2.erase z2,s(c2,zp2) ∈ U2 \ E1:=by
      rcases (Finset.mem_filter.mp qfs).2.1 with ⟨heq,_⟩ | ⟨_,h⟩
      ·exact absurd heq q2i.symm
      ·exact h
     have q6x:c2 ≠ z2:=(Finset.mem_erase.mp hc2).1
     have qno:c2 ∈ C2:=Finset.mem_of_mem_erase hc2
     have q3i:=z131 hL.1 q25 b qm4 (q4r qiu)
     have q3s:G.Adj zp1 c2:=z053 q03 h4 hf2 q3i q1l qno q6x
     have q3t:G.Adj zp2 c2:=(hf2.2.2.2.1 c2 qno).symm
     rcases Finset.mem_union.mp hk with qa5 | q6y
     ·rcases (Finset.mem_filter.mp qa5).2.2.2 with ⟨atp,q2v,btp,q0t,hrt⟩
      obtain ⟨w,hw⟩:=Finset.card_eq_one.mp q0t
      have q0c:=z109 hrt
      have hwm:w ∈ side (n:=n) C atp (1 - btp):=by rw [hw];simp
      have qfp:G.Adj zp1 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q31) hwm;exact (z132 hL.1 q2v hwm (q0c q31)).symm
      have qfq:G.Adj zp2 w:=by fin_cases btp;exact z132 hL.1 q2v (q0c q4w) hwm;exact (z132 hL.1 q2v hwm (q0c q4w)).symm
      have q8s:w = c2:=z102 h4 q0h qfp qfq q3s q3t
      subst q8s
      have q5g:s(w,zp2) ∈ starEdges G C:=by
       simp only [starEdges,Finset.mem_biUnion,Finset.mem_image,Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp,q2v,(zp2,w),⟨q0c q4w,hwm⟩,Sym2.eq_swap⟩
       ·exact ⟨atp,q2v,(w,zp2),⟨hwm,q0c q4w⟩,rfl⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp qix).1).1).2 q5g
     ·simp only [FacAll,Finset.mem_union] at q6y
      rcases q6y with (h | h) | (h | h)
      ·exact q02.symm (z046 q03 hf1 ((q1j k h).2.2.1 q31))
      ·have q0c:=(q1s k h).2.2.1
       have heq:=z102 h4 q0h (hf1.2.2.2.2.1 zp1 (q0c q31)) (hf1.2.2.2.2.1 zp2 (q0c q4w)) q3s q3t
       subst heq
       exact (Finset.mem_sdiff.mp qix).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (q0c q4w)))
      ·exact q02.symm ((z046 q03 hf2 ((q22 k h).2.2.1 q31)).trans hsz.symm)
      ·have q0c:=(q2j k h).2.2.1
       have heq:=z102 h4 q0h (hf2.2.2.2.2.1 zp1 (q0c q31)) (hf2.2.2.2.2.1 zp2 (q0c q4w)) q3s q3t
       exact q6x heq.symm
   rcases q7x with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
   ·exact qat hu'.1 hv'.1 hu'.2 hv'.2
   ·exact qat hv'.1 hu'.1 hv'.2 hu'.2
   ·exact q8l hu'.1 hv'.1 hu'.2 hv'.2
   ·exact q8l hv'.1 hu'.1 hv'.2 hu'.2
  have hwb:=z136 hL q01 hne q00
   (by have:=z104 hL.1 ha'.1 (1 - b);omega) (z130 hL hne q25 (1 - b))
   A' ql1 q4r FacAll q2n
  have qft:(orN G C \ lam G C).filter (fun k=>
    OrReaches n C (opnd C a (1 - b)) k∧ k ∉ FacAll∧ 2 ≤ (orIn n C (n + k) ∩ A').card) ⊆ HW:=by
   intro k hk
   have hkf:=Finset.mem_filter.mp hk
   exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hkf.1,hkf.2.2.1⟩,
    le_trans hkf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
  have qnp:=Finset.card_le_card qft
  omega
 by_cases qnq:3 ≤ (centreless G C).card
 ·omega
 ·by_cases q0m:(centreless G C).card = 0
  ·have q29:centreless G C = ∅:=Finset.card_eq_zero.mp q0m
   have qfu:A1 = ∅:=by
    ext v;simp only [Finset.notMem_empty,iff_false];intro hv
    rcases (Finset.mem_filter.mp hv).2.2 with ⟨a,haC,_⟩
    rw [q29] at haC;exact Finset.notMem_empty _ haC
   have qfv:A2 = ∅:=by
    ext v;simp only [Finset.notMem_empty,iff_false];intro hv
    rcases (Finset.mem_filter.mp hv).2.2 with ⟨a,haC,_⟩
    rw [q29] at haC;exact Finset.notMem_empty _ haC
   rw [qfu,qfv,Finset.card_empty] at q7w
   by_cases qnr:Zconf = ∅
   ·obtain ⟨m0,hm0,qcn⟩:=z037 hL q01 hne q0y q00 q29
    have qm5:m0 ∈ Extra:=Finset.mem_sdiff.mpr ⟨hm0,fun hkf=>by
     have:m0 < g2:=by
      simp only [FacAll,Finset.mem_union] at hkf
      rcases hkf with (h | h) | (h | h)
      ·have:=z113 (Finset.mem_filter.mp h).2;have:=z104 hL.1 q5x.1 b1;omega
      ·have:=z113 (Finset.mem_filter.mp h).2;have:=z104 hL.1 q5x.1 (1 - b1);omega
      ·have:=z113 (Finset.mem_filter.mp h).2;have:=z104 hL.1 q2p.1 b2;omega
      ·have:=z113 (Finset.mem_filter.mp h).2;have:=z104 hL.1 q2p.1 (1 - b2);omega
     omega⟩
    have qpc:1 ≤ Extra.card:=Finset.card_pos.mpr ⟨m0,qm5⟩
    rw [qnr,Finset.card_empty] at q7w;omega
   ·obtain ⟨v0,hv0⟩:=Finset.nonempty_iff_ne_empty.mpr qnr
    obtain ⟨_,_,_,u',q24,mu,qap,q06⟩:=(Finset.mem_filter.mp hv0).2.2
    have qfw:mu ∉ SingleMix:=by
     intro hsm
     obtain ⟨v,hv,hor⟩:=q2l mu hsm
     rw [q06] at hor
     have qm6:u' = v:=Finset.singleton_injective hor
     have hsv:=(Finset.mem_filter.mp hv).2.1
     exact q02 (q24.symm.trans ((congrArg s qm6).trans hsv))
    have hle:=Finset.card_le_card (Finset.insert_subset qap q12)
    rw [Finset.card_insert_of_notMem qfw,q0x] at hle
    omega
  ·by_cases q6l:(centreless G C).card = 1
   ·obtain ⟨a0,ha0⟩:=Finset.card_eq_one.mp q6l
    have qpd:a0 ∈ centreless G C:=by rw [ha0];simp
    by_cases qav:A1 ∪ A2 = ∅
    ·have qfu:A1 = ∅:=(Finset.union_eq_empty.mp qav).1
     have qfv:A2 = ∅:=(Finset.union_eq_empty.mp qav).2
     have hle:=Finset.card_le_card q12
     rw [q0x] at hle
     rw [qfu,qfv,Finset.card_empty] at q7w
     omega
    ·obtain ⟨v0,hv0⟩:=Finset.nonempty_iff_ne_empty.mpr qav
     obtain ⟨b0,q6o,qcz⟩:∃ b0:Fin 2,side (n:=n) C a0 b0 = ∅∧ v0 ∈ side (n:=n) C a0 (1 - b0):=by
      rcases Finset.mem_union.mp hv0 with h1 | h2
      ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
       have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
       exact ⟨b,q0g,hvs⟩
      ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
       have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
       exact ⟨b,q0g,hvs⟩
     have qfx:A1 ∪ A2 ⊆ side (n:=n) C a0 (1 - b0):=by
      intro v hv
      obtain ⟨b,q0g,hvs⟩:∃ b:Fin 2,side (n:=n) C a0 b = ∅∧ v ∈ side (n:=n) C a0 (1 - b):=by
       rcases Finset.mem_union.mp hv with h1 | h2
       ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
        have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
        exact ⟨b,q0g,hvs⟩
       ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩
        have q3z:a = a0:=Finset.mem_singleton.mp (ha0 ▸ haC);subst q3z
        exact ⟨b,q0g,hvs⟩
      have hbe:b = b0:=by
       by_contra q2e
       have q51:1 - b0 = b:=z044 (Ne.symm q2e)
       rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
      rwa [← hbe]
     set HW:=Extra.filter (fun k=>2 ≤ (orIn n C (n + k)).card)
     have qiy:=q8j a0 qpd b0 q6o (A1 ∪ A2) ⟨v0,hv0⟩ (Finset.Subset.refl _) qfx
     have q7z:Disjoint SingleMix HW:=by
      rw [Finset.disjoint_left];intro k hk1 hk2
      obtain ⟨v,_,hor⟩:=q2l k hk1
      have hc:=(Finset.mem_filter.mp hk2).2
      rw [hor,Finset.card_singleton] at hc;omega
     have qiz:=Finset.card_le_card (Finset.union_subset q12 (Finset.filter_subset _ _:HW ⊆ Extra))
     rw [Finset.card_union_of_disjoint q7z,q0x] at qiz
     rw [Finset.card_union_of_disjoint q3p] at qiy
     omega
   ·
    have qaa:(centreless G C).card = 2:=by omega
    by_cases qpe:1 ≤ Zconf.card
    ·have hle:=Finset.card_le_card q12
     rw [q0x] at hle
     omega
    ·by_cases qpf:A1.card + A2.card + Zconf.card ≤ 3
     ·omega
     ·
      have qjm:(A1 ∪ A2).card = 4:=by
       rw [Finset.card_union_of_disjoint q3p];omega
      obtain ⟨a1,a2,qpn,q5u⟩:=Finset.card_eq_two.mp qaa
      have qeh:a1 ∈ centreless G C:=by rw [q5u];simp
      have qhz:a2 ∈ centreless G C:=by rw [q5u];simp
      let S1:=(A1 ∪ A2).filter (fun v=>∃ b:Fin 2,side (n:=n) C a1 b = ∅∧ v ∈ side (n:=n) C a1 (1 - b))
      let S2:=(A1 ∪ A2).filter (fun v=>∃ b:Fin 2,side (n:=n) C a2 b = ∅∧ v ∈ side (n:=n) C a2 (1 - b))
      have qj0:A1 ∪ A2 ⊆ S1 ∪ S2:=by
       intro v hv
       obtain ⟨a,haC,b,q0g,hvs⟩:∃ a ∈ centreless G C,∃ b:Fin 2,side (n:=n) C a b = ∅∧ v ∈ side (n:=n) C a (1 - b):=by
        rcases Finset.mem_union.mp hv with h1 | h2
        ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a,haC,b,q0g,_,hvs⟩;exact ⟨a,haC,b,q0g,hvs⟩
        ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a,haC,b,q0g,_,hvs⟩;exact ⟨a,haC,b,q0g,hvs⟩
       rw [q5u,Finset.mem_insert,Finset.mem_singleton] at haC
       rcases haC with rfl | rfl
       ·exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,b,q0g,hvs⟩)
       ·exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,b,q0g,hvs⟩)
      have qm7:4 ≤ S1.card + S2.card:=by
       have h1:=Finset.card_le_card qj0
       have h2:=Finset.card_union_le S1 S2
       omega
      have qm8:∃ a ∈ centreless G C,∃ S':Finset (Fin n),2 ≤ S'.card∧ S' ⊆ A1 ∪ A2∧ 
        ∃ b:Fin 2,side (n:=n) C a b = ∅∧ S' ⊆ side (n:=n) C a (1 - b):=by
       by_cases hS1:2 ≤ S1.card
       ·obtain ⟨v0,hv0⟩:=Finset.card_pos.mp (by omega:0 < S1.card)
        obtain ⟨b0,q6o,qcz⟩:=(Finset.mem_filter.mp hv0).2
        refine ⟨a1,qeh,S1,hS1,Finset.filter_subset _ _,b0,q6o,fun v hv=>?_⟩
        obtain ⟨b,q0g,hvs⟩:=(Finset.mem_filter.mp hv).2
        have hbe:b = b0:=by
         by_contra q2e
         have q51:1 - b0 = b:=z044 (Ne.symm q2e)
         rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
        rwa [← hbe]
       ·have hS2:2 ≤ S2.card:=by omega
        obtain ⟨v0,hv0⟩:=Finset.card_pos.mp (by omega:0 < S2.card)
        obtain ⟨b0,q6o,qcz⟩:=(Finset.mem_filter.mp hv0).2
        refine ⟨a2,qhz,S2,hS2,Finset.filter_subset _ _,b0,q6o,fun v hv=>?_⟩
        obtain ⟨b,q0g,hvs⟩:=(Finset.mem_filter.mp hv).2
        have hbe:b = b0:=by
         by_contra q2e
         have q51:1 - b0 = b:=z044 (Ne.symm q2e)
         rw [q51,q0g] at qcz;exact Finset.notMem_empty _ qcz
        rwa [← hbe]
      obtain ⟨a,haC,S',qpo,qj1,b,q0g,qfy⟩:=qm8
      set HW:=Extra.filter (fun k=>2 ≤ (orIn n C (n + k)).card)
      have qiy:S'.card ≤ HW.card + 1:=q8j a haC b q0g S' (Finset.card_pos.mp (by omega)) qj1 qfy
      have qiz:HW.card ≤ Extra.card:=Finset.card_le_card (Finset.filter_subset _ _)
      omega
lemma main (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (s:Fin n→ Bool)
  (q03:∀ u v:Fin n,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (q01:IsLiftFixedPoint G C):
  ¬ ∃ g1 g2:ℕ,g1 ≠ g2∧ (∀ k:ℕ,k ∈ junk G C↔ k = g1∨ k = g2)∧ 
   (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z ∈ Ci∧ zp ∈ Di∧ 
    (∀ c ∈ Ci,G.Adj c zp)∧ (∀ d ∈ Di,G.Adj d z)∧ 2 ≤ Ci.card∧ 2 ≤ Di.card∧ 
    ∀ x:Fin n→ Bool,gateVal n C g1 x = (decide (∃ c ∈ Ci,x c = true) && decide (∃ d ∈ Di,x d = true)))∧ 
   (∃ (Ci Di:Finset (Fin n)) (z zp:Fin n),G.Adj z zp∧ z ∈ Ci∧ zp ∈ Di∧ 
    (∀ c ∈ Ci,G.Adj c zp)∧ (∀ d ∈ Di,G.Adj d z)∧ 2 ≤ Ci.card∧ 2 ≤ Di.card∧ 
    ∀ x:Fin n→ Bool,gateVal n C g2 x = (decide (∃ c ∈ Ci,x c = true) && decide (∃ d ∈ Di,x d = true))):=by
 have q3u:∀ g Ci Di z zp,z000 G C g Ci Di z zp→ z000 G C g Di Ci zp z:=by
  intro g Ci Di z zp hf
  refine ⟨hf.1.symm,hf.2.2.1,hf.2.1,hf.2.2.2.2.1,hf.2.2.2.1,hf.2.2.2.2.2.2.1,hf.2.2.2.2.2.1,fun x=>?_⟩
  rw [hf.2.2.2.2.2.2.2 x,Bool.and_comm]
 have q8m:∀ g1 g2,g1 < g2→ (∀ k,k ∈ junk G C↔ k = g1∨ k = g2)→ 
   ∀ C1 D1 z1 zp1 C2 D2 z2 zp2,
   z000 G C g1 C1 D1 z1 zp1→ z000 G C g2 C2 D2 z2 zp2→ False:=by
  intro g1 g2 q0y q00 C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
  have q8n:∀ C2' D2' z2' zp2',z000 G C g2 C2' D2' z2' zp2'→ 
    s z1 = s z2'→ s zp1 = s zp2'→ False:=by
   intro C2' D2' z2' zp2' qjn hsz q1l
   by_cases hz:z1 = z2'
   ·subst hz
    by_cases hzp:zp1 = zp2'
    ·subst hzp;exact z022 q03 h4 hL q01 q0y q00 hf1 qjn
    ·exact z021 q03 h4 hL q01 q0y q00 hzp hf1 qjn
   ·by_cases hzp:zp1 = zp2'
    ·subst hzp
     exact z021 q03 h4 hL q01 q0y q00 hz
      (q3u g1 C1 D1 z1 zp1 hf1) (q3u g2 C2' D2' z2' zp1 qjn)
    ·exact z020 q03 h4 hL q01 q0y q00 hz hzp hsz q1l hf1 qjn
  by_cases hsz:s z1 = s z2
  ·have q1l:s zp1 = s zp2:=
    z015 (q03 z1 zp1 hf1.1).symm (by rw [hsz];exact (q03 z2 zp2 hf2.1).symm)
   exact q8n C2 D2 z2 zp2 hf2 hsz q1l
  ·have qpg:s z1 = s zp2:=z015 hsz (q03 z2 zp2 hf2.1).symm
   have qm9:s zp1 = s z2:=z015 (q03 z1 zp1 hf1.1).symm (Ne.symm hsz)
   exact q8n D2 C2 zp2 z2 (q3u g2 C2 D2 z2 zp2 hf2) qpg qm9
 rintro ⟨g1,g2,qma,q00,⟨C1,D1,z1,zp1,hf1⟩,⟨C2,D2,z2,zp2,hf2⟩⟩
 rcases Nat.lt_or_gt_of_ne qma with hlt | hgt
 ·exact q8m g1 g2 hlt q00 C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
 ·exact q8m g2 g1 hgt (fun k=>by rw [q00 k,or_comm]) C2 D2 z2 zp2 C1 D1 z1 zp1 hf2 hf1
end FlagsSupport

end PEqualNP.Outside.L_meta_5012
