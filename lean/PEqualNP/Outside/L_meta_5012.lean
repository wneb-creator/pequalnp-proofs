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

lemma nonclean_reaches_and_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hnb : ¬ BelowF G C j) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, OrReaches n C (opnd C a b) j := by
  have main : ∀ d : ℕ, ∀ j < C.gates.length, C.gates.length - j = d →
      ¬ BelowF G C j → ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
        ∃ b : Fin 2, OrReaches n C (opnd C a b) j := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro j hj hd hnb
      have hout : C.output ≠ n + j := by
        intro heq
        apply hnb
        intro x hx
        have hf : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
        rw [heq] at hf
        exact hf.symm.trans hx
      obtain ⟨k, hk, hin⟩ := PureTopPatch.least_gate_reader hL hj hout
      have hjk : j < k := by have := hL.1.2.1 k hk _ hin; omega
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · obtain ⟨b, hb⟩ := inputsAsOpnd hL.1 hk hin
        refine ⟨k, hk, hand, b, ?_⟩
        rw [← hb]
        exact (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩
      · have hnbk : ¬ BelowF G C k := by
          intro hbelow
          apply hnb
          intro x hx
          exact hbelow x ((val_or (n := n) (by simp) hk hor).mpr
            ⟨n + j, hin, by omega, hx⟩)
        obtain ⟨a, ha, haand, b, hr⟩ := ih (C.gates.length - k) (by omega) k hk rfl hnbk
        refine ⟨a, ha, haand, b, ?_⟩
        exact reach_orReaches ((orReaches_reach k _ hr).1.tail
          ⟨k, hk, rfl, hor, hin, by omega⟩) j rfl hj
  exact main _ j hj rfl hnb

lemma nonclean_or_ancestor_and_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) {m j : ℕ}
    (hm : m < C.gates.length) (hnb : ¬ BelowF G C m)
    (hr : OrReaches n C (n + m) j) (hand : (gateAt C j).op = GateOp.and) :
    j ∈ junk G C := by
  obtain ⟨a, ha, haand, b, hrm⟩ := nonclean_reaches_and_reader G C hL hm hnb
  have hrj : OrReaches n C (opnd C a b) j :=
    reach_orReaches ((orReaches_reach m _ hrm).1.trans (orReaches_reach j _ hr).1)
      j rfl (orReaches_reach j _ hr).2
  exact operandOrAndJunk hL.1 hT ha haand hrj hand

lemma nonclean_not_raw_has_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) {m : ℕ}
    (hm : m < C.gates.length) (hnb : ¬ BelowF G C m)
    (hraw : ¬ NoNonLambda.RawWire n C (n + m)) :
    ∃ j ∈ junk G C, OrReaches n C (n + m) j := by
  classical
  simp only [NoNonLambda.RawWire, not_forall] at hraw
  obtain ⟨j, hj⟩ := hraw
  have hr : OrReaches n C (n + m) j := by tauto
  have hnot : (gateAt C j).op ≠ GateOp.or := by tauto
  have hand := (hL.1.1 _ (gateAt_mem (orReaches_reach j _ hr).2)).resolve_right hnot
  exact ⟨j, nonclean_or_ancestor_and_junk G C hL hT hm hnb hr hand, hr⟩

lemma sole_exception_not_raw_reads_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) {m : ℕ}
    (hN : orN G C \ lam G C = {m})
    (hraw : ¬ NoNonLambda.RawWire n C (n + m)) :
    ∃ j ∈ junk G C, m ∈ readers n C j := by
  have hmem : m ∈ orN G C := (Finset.mem_sdiff.mp
    (show m ∈ orN G C \ lam G C by rw [hN]; exact Finset.mem_singleton_self m)).1
  have hm : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hmem
  obtain ⟨j, hj, hr⟩ := nonclean_not_raw_has_junk G C hL hT hm.1 hm.2.2 hraw
  rcases lastOrBefore (orReaches_reach j _ hr).1 with he | ⟨k, hk, hop, hin, _, _⟩
  · have heq : m = j := by omega
    subst j
    rw [(junkData hj).2.1] at hm
    cases hm.2.1
  · have hread : k ∈ readers n C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩
    have heq := sole_junk_or_reader G C hL.1 hN hj hread hop
    exact ⟨j, hj, heq ▸ hread⟩

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

namespace NoNonLambda

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma sole_exception_reads_junk_or_mixed {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    {m : ℕ} (hN : orN G C \ lam G C = {m}) (hJ : (junk G C).Nonempty) :
    (∃ j ∈ junk G C, m ∈ readers n C j) ∨
      ∃ u ∈ orIn n C (n + m), ∃ v ∈ orIn n C (n + m), s u ≠ s v := by
  rcases sole_exception_raw_or_color_obstruction G C s hs h4 hL hT hN hJ with hraw | hmixed
  · exact Or.inl (OneException.sole_exception_not_raw_reads_junk G C hL hT hN hraw)
  · exact Or.inr hmixed

end NoNonLambda

end PEqualNP.Outside.L_meta_5012
