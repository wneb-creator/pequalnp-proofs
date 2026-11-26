import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18011

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- The dead-gate and evaluator primitives follow L_meta_7895, L_meta_1490 and L_meta_4901.
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

private def essential (C : Circuit) : Prop :=
  ∀ i : Fin 10, ∃ x : Fin 9 → Bool,
    C.eval (List.ofFn (i.insertNth false x)) ≠ C.eval (List.ofFn (i.insertNth true x))

private lemma pinOff (i : Fin 10) (x : Fin 9 → Bool) (w : ℕ) (hw : w ≠ i.val) :
    (List.ofFn (i.insertNth false x)).getD w false =
      (List.ofFn (i.insertNth true x)).getD w false := by
  by_cases h : w < 10
  · let j : Fin 10 := ⟨w,h⟩
    have hn : j ≠ i := fun e => hw (congrArg Fin.val e)
    obtain ⟨z,hz⟩ := Fin.exists_succAbove_eq hn
    change (List.ofFn (i.insertNth false x)).getD j false =
      (List.ofFn (i.insertNth true x)).getD j false
    rw [← hz]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (i.succAbove z).isLt,
      Option.getD_some]
    change (@Fin.insertNth 9 (fun _ => Bool) i false x) (i.succAbove z) = (@Fin.insertNth 9 (fun _ => Bool) i true x) (i.succAbove z)
    simp only [Fin.insertNth_apply_succAbove]
  · rw [getD_ge _ _ (by simpa using Nat.le_of_not_lt h), getD_ge _ _ (by simpa using Nat.le_of_not_lt h)]

private lemma foldEqOutside (j : ℕ) (gs : List Gate) (L M : List Bool)
    (hL : L.length = M.length) (hj : j < L.length)
    (hs : ∀ i, i ≠ j → L.getD i false = M.getD i false)
    (hn : ∀ g ∈ gs, j ∉ g.inputs) :
    ∀ i, i ≠ j → (gs.foldl stepWire L).getD i false = (gs.foldl stepWire M).getD i false := by
  induction gs generalizing L M with
  | nil => exact hs
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => L.getD i false) =
        g.op.eval (g.inputs.map fun i => M.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      apply hs
      intro he
      exact hn g (by simp) (he ▸ hi)
    simp only [List.foldl_cons]
    apply ih
    · simp [stepWire, hL]
    · simp [stepWire]; omega
    · intro i hi
      by_cases hlo : i < L.length
      · have hmo : i < M.length := hL ▸ hlo
        simpa only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hlo,
          List.getElem?_append_left hmo] using hs i hi
      · have hmo : M.length ≤ i := by omega
        simp only [List.getD_eq_getElem?_getD] at hv
        simp only [stepWire,List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : L.length ≤ i),
          List.getElem?_append_right hmo, hL,hv]
    · exact fun q hq => hn q (by simp [hq])

private lemma outIsGate (D : Circuit) (he : essential D) :
    10 ≤ D.output ∧ D.output < 10 + D.size := by
  constructor
  · by_contra! h
    let j : Fin 10 := if D.output = 0 then 1 else 0
    have hj : D.output ≠ j.val := by unfold j; split <;> simp_all
    obtain ⟨x,hx⟩ := he j
    apply hx
    change val D _ _ = val D _ _
    rw [val_input (by simp : (List.ofFn (j.insertNth false x)).length = 10) h,
      val_input (by simp : (List.ofFn (j.insertNth true x)).length = 10) h]
    exact pinOff j x D.output hj
  · by_contra! h
    obtain ⟨x,hx⟩ := he 0
    apply hx
    change val D _ _ = val D _ _
    rw [val_ge (by simp : (List.ofFn ((0 : Fin 10).insertNth false x)).length = 10) h,
      val_ge (by simp : (List.ofFn ((0 : Fin 10).insertNth true x)).length = 10) h]

private lemma existsUsed (D : Circuit) (he : essential D) (i : Fin 10) :
    ∃ g ∈ D.gates, i.val ∈ g.inputs := by
  by_contra! hn
  obtain ⟨x,hx⟩ := he i
  apply hx
  change (D.gates.foldl stepWire (List.ofFn (i.insertNth false x))).getD D.output false =
    (D.gates.foldl stepWire (List.ofFn (i.insertNth true x))).getD D.output false
  have h := (outIsGate D he).1
  exact foldEqOutside i.val D.gates _ _ (by simp) (by simp) (pinOff i x) hn _
    (by have := i.isLt; omega)

private lemma countOperandLength (D : Circuit) (hD : IsAO2 10 D) :
    (D.gates.flatMap Gate.inputs).length = 2 * D.size := by
  rw [Circuit.size]
  have aux (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have hh := hgs g (by simp)
      have hi := ih fun q hq => hgs q (by simp [hq])
      rw [List.flatMap_cons, List.length_append, hh,hi,List.length_cons]
      omega
  exact aux D.gates hD.2.2

set_option maxHeartbeats 0 in
private lemma singleRead (D : Circuit) (hD : IsAO2 10 D) (hmin : IsSmallest 10 D)
    (hS : D.size ≤ 18) (he : essential D) :
    ∃ i : Fin 10, ((D.gates.flatMap Gate.inputs).count i.val) = 1 := by
  let W := D.gates.flatMap Gate.inputs
  have ha : ∀ i : Fin 10, i.val ∈ W := by
    intro i
    obtain ⟨g,hg,hi⟩ := existsUsed D he i
    exact List.mem_flatMap.mpr ⟨g,hg,hi⟩
  by_contra! hn
  have hb (i : Fin 10) : 2 ≤ W.count i.val := by
    have h := List.count_pos_iff.mpr (ha i)
    have hh := hn i
    change W.count i.val ≠ 1 at hh
    omega
  have hor := outIsGate D he
  let U := (List.range D.size).filter fun j => decide (10+j ≠ D.output)
  let V := U.map (10+·)
  have hsize : U.length + 1 = D.size := by
    have heq : D.output - 10 ∈ List.range D.size :=
      List.mem_range.mpr (by omega)
    have hform : U = (List.range D.size).erase (D.output - 10) := by
      have hF : (fun j : ℕ => decide (10+j ≠ D.output)) = fun j => j != D.output-10 := by
        funext j
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq, bne_iff_ne]
        have hh := (outIsGate D he).1
        omega
      unfold U
      rw [hF, ← List.Nodup.erase_eq_filter List.nodup_range]
    rw [hform, List.length_erase_of_mem heq, List.length_range]
    have := List.mem_range.mp heq
    omega
  have hV : V.Nodup := (List.nodup_range.filter _).map (fun a b h => by omega)
  have hmV (a : ℕ) (h : a ∈ V) : 10 ≤ a ∧ a ∈ W := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    have ⟨hj',hj''⟩ := List.mem_filter.mp hj
    have hlt : j < D.gates.length := List.mem_range.mp hj'
    have hne : D.output ≠ 10+j := Ne.symm (of_decide_eq_true hj'')
    obtain ⟨r,hr,hin⟩ := reader hD hmin hlt hne
    exact ⟨by omega,List.mem_flatMap.mpr ⟨gateAt D r,gateAt_mem hr,hin⟩⟩
  have hw : (List.range 10 ++ List.range 10 ++ V).Subperm W := by
    apply List.subperm_iff_count.mpr
    intro j
    rw [List.count_append,List.count_append]
    by_cases hj : j < 10
    · have hmiss : j ∉ V := by intro h; have := (hmV j h).1; omega
      rw [List.count_eq_zero_of_not_mem hmiss]
      have h1 : (List.range 10).count j ≤ 1 :=
        List.nodup_iff_count_le_one.mp List.nodup_range j
      have h2 := hb ⟨j,hj⟩
      change 2 ≤ W.count j at h2
      omega
    · have hh : j ∉ List.range 10 := by simpa using hj
      rw [List.count_eq_zero_of_not_mem hh]
      by_cases he : j ∈ V
      · have h1 := List.nodup_iff_count_le_one.mp hV j
        have h2 := List.count_pos_iff.mpr (hmV j he).2
        omega
      · simp [List.count_eq_zero_of_not_mem he]
  have H := hw.length_le
  simp only [List.length_append,List.length_range,V,List.length_map] at H
  have hW := countOperandLength D hD
  change W.length = _ at hW
  omega


private def up (q i : ℕ) : ℕ := if i < q then i else i+1
private def down (q i : ℕ) : ℕ := if i < q then i else i-1
private lemma up_down (q i : ℕ) (h : i ≠ q) : up q (down q i) = i := by
  unfold up down
  split_ifs <;> omega
private lemma down_lt (q i n : ℕ) (hq : q < n) (h : i < n) (hne : i ≠ q) :
    down q i < n - 1 := by unfold down; split_ifs <;> omega
private def mapPin (q : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (down q)⟩

private def PinRel (q : ℕ) (A B : List Bool) : Prop :=
  A.length = B.length + 1 ∧ q ≤ B.length ∧
  ∀ i, A.getD (up q i) false = B.getD i false

private lemma addSame (q : ℕ) (A B : List Bool) (h : PinRel q A B) (b : Bool) :
    PinRel q (A ++ [b]) (B ++ [b]) := by
  rcases h with ⟨hl,hq,hv⟩
  refine ⟨by simp [hl], by simp; omega,?_⟩
  intro i
  by_cases hi : i < B.length
  · have hu : up q i < A.length := by unfold up; split_ifs <;> omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hu,
      List.getElem?_append_left hi] using hv i
  · have he : up q i = i + 1 := by unfold up; rw [if_neg (by omega)]
    rw [he]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : A.length ≤ i+1),
      List.getElem?_append_right (by omega : B.length ≤ i),
      show i+1-A.length = i-B.length by omega]

private lemma foldPin (q : ℕ) (gs : List Gate) (A B : List Bool) (h : PinRel q A B)
    (hno : ∀ g ∈ gs, q ∉ g.inputs) :
    PinRel q (gs.foldl stepWire A) ((gs.map (mapPin q)).foldl stepWire B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map (fun i => A.getD i false)) =
        g.op.eval (g.inputs.map (fun i => B.getD (down q i) false)) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      have hn : i ≠ q := fun hv => hno g (by simp) (hv ▸ hi)
      simpa only [up_down q i hn] using h.2.2 (down q i)
    simp only [List.foldl_cons,List.map_cons]
    apply ih
    · unfold stepWire mapPin
      simp only [List.map_map,Function.comp_apply]
      rw [hv]
      exact addSame _ _ _ h _
    · exact fun k hk => hno k (by simp [hk])

private lemma initPin (q : Fin 10) (b : Bool) (x : Fin 9 → Bool) :
    PinRel q.val (List.ofFn (q.insertNth b x)) (List.ofFn x) := by
  refine ⟨by simp, by simpa using Nat.le_of_lt_succ q.isLt,?_⟩
  intro i
  by_cases hi : i < 9
  · let j : Fin 9 := ⟨i,hi⟩
    have hh : (q.succAbove j).val = up q.val i := by
      unfold Fin.succAbove up
      split <;> split <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, j] at * <;> omega
    rw [← hh]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (q.succAbove j).isLt,
      dif_pos hi,Option.getD_some]
    change (@Fin.insertNth 9 (fun _ => Bool) q b x) (q.succAbove j) = x j
    simp only [Fin.insertNth_apply_succAbove]
  · have h0 : (List.ofFn x).length ≤ i := by simp; omega
    have h1 : (List.ofFn (q.insertNth b x)).length ≤ up q.val i := by
      have hq := q.isLt
      simp only [List.length_ofFn]
      unfold up
      split_ifs <;> omega
    rw [getD_ge _ _ h1,getD_ge _ _ h0]

private lemma segAO (D : Circuit) (h : IsAO2 10 D) (q : Fin 10)
    (P G T : List Gate) (he : D.gates = P ++ G ++ T) (o : ℕ)
    (hn : ∀ g ∈ G, q.val ∉ g.inputs) :
    IsAO2 (9+P.length) ⟨G.map (mapPin q.val),o⟩ := by
  have hm (g : Gate) (hg : g ∈ G) : g ∈ D.gates := by rw [he]; simp [hg]
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨g,hmG,rfl⟩ := List.mem_map.mp hg
    exact h.1 g (hm g hmG)
  · intro j hj w hw
    have hj' : j < G.length := by simpa using hj
    have hD : P.length+j < D.gates.length := by simp [he]; omega
    have H := h.2.1 _ hD
    have hg : gateAt D (P.length+j) = G[j] := by
      rw [gateAt_eq hD]
      simp only [he]
      rw [List.getElem_append_left (by simpa using (show P.length+j < (P++G).length by simp;omega)),
        List.getElem_append_right (by omega)]
      simp
    rw [gateAt_eq hj] at hw
    have hg' : (G.map (mapPin q.val))[j] = mapPin q.val G[j] := by simp
    change w ∈ (G.map (mapPin q.val))[j].inputs at hw
    rw [hg'] at hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
    have hup := H u (by rw [hg];exact hu)
    have hne : u ≠ q.val := fun e => hn G[j] (List.getElem_mem hj') (e ▸ hu)
    have qq := q.isLt
    change down q.val u < 9 + P.length + j
    have hlt := down_lt q.val u (10+(P.length+j)) (by omega) hup hne
    omega
  · intro g hg
    obtain ⟨g,hmG,rfl⟩ := List.mem_map.mp hg
    simp [mapPin,h.2.2 g (hm g hmG)]

private lemma pickRead (D : Circuit) (h : IsAO2 10 D) (q : Fin 10)
    (hs : (D.gates.flatMap Gate.inputs).count q.val = 1) :
    ∃ (P T : List Gate) (g : Gate) (w : ℕ), D.gates = P ++ g :: T ∧
      w ≠ q.val ∧ w < 10 + P.length ∧
      (g.inputs = [q.val,w] ∨ g.inputs = [w,q.val]) ∧
      (∀ a ∈ P, q.val ∉ a.inputs) ∧ (∀ a ∈ T, q.val ∉ a.inputs) := by
  have hpos : q.val ∈ D.gates.flatMap Gate.inputs := List.count_pos_iff.mp (by omega)
  obtain ⟨g,hg,hread⟩ := List.mem_flatMap.mp hpos
  obtain ⟨P,T,e⟩ := List.append_of_mem hg
  have hv : P.length < D.gates.length := by simp [e]
  have hx : gateAt D P.length = g := by
    rw [gateAt_eq hv]
    simp only [e]
    simp [List.getElem_append_right (by omega : P.length ≤ P.length)]
  have hcnt : (P.flatMap Gate.inputs).count q.val + g.inputs.count q.val +
      (T.flatMap Gate.inputs).count q.val = 1 := by
    simpa only [e,List.flatMap_append,List.flatMap_cons,List.count_append,
      Nat.add_assoc] using hs
  have hc : 0 < g.inputs.count q.val := List.count_pos_iff.mpr hread
  have hnP : (P.flatMap Gate.inputs).count q.val = 0 := by omega
  have hnT : (T.flatMap Gate.inputs).count q.val = 0 := by omega
  have hl := h.2.2 g hg
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hl
  have hpair : a = q.val ∨ b = q.val := by simpa [hab,eq_comm] using hread
  have hab' : ¬(a = q.val ∧ b = q.val) := by
    rintro ⟨ha,hb⟩
    simp [hab,ha,hb] at hcnt
    omega
  have ww (w : ℕ) (hw : w ∈ g.inputs) : w < 10+P.length := h.2.1 _ hv _ (hx ▸ hw)
  have noP (a : Gate) (ha : a ∈ P) : q.val ∉ a.inputs := by
    intro hm
    have hp := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨a,ha,hm⟩)
    omega
  have noT (a : Gate) (ha : a ∈ T) : q.val ∉ a.inputs := by
    intro hm
    have ht := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨a,ha,hm⟩)
    omega
  rcases hpair with ha | hb
  · exact ⟨P,T,g,b,e,(fun hb => hab' ⟨ha,hb⟩),ww b (by simp [hab]),Or.inl (by rw [hab,ha]),noP,noT⟩
  · exact ⟨P,T,g,a,e,(fun ha => hab' ⟨ha,hb⟩),ww a (by simp [hab]),Or.inr (by rw [hab,hb]),noP,noT⟩


private lemma splitAtPin (D : Circuit) (hD : IsAO2 10 D) (he : essential D)
    (hB : D.size ≤ 18) (hmin : IsSmallest 10 D) :
    ∃ (q : Fin 10) (A B : Circuit) (isAnd : Bool),
      IsAO2 9 A ∧ IsAO2 (10+A.size) B ∧
        A.size+B.size ≤ 17 ∧ A.output < 9+A.size ∧
      ∀ (x : Fin 9 → Bool) (b : Bool),
        D.eval (List.ofFn (q.insertNth b x)) =
          B.eval (A.wires (List.ofFn x) ++ [if isAnd = true then b && A.eval (List.ofFn x)
            else b || A.eval (List.ofFn x)]) := by
  obtain ⟨q,hq⟩ := singleRead D hD hmin hB he
  obtain ⟨P,T,g,w,hs,hw,hwb,hop,hP,hT⟩ := pickRead D hD q hq
  let A : Circuit := ⟨P.map (mapPin q.val),down q.val w⟩
  let B : Circuit := ⟨T.map (mapPin q.val),down q.val D.output⟩
  have hA : A.size = P.length := by simp [A,Circuit.size]
  have hBs : B.size = T.length := by simp [B,Circuit.size]
  have hS : D.size = P.length + 1 + T.length := by simp [Circuit.size,hs]; omega
  have hg : g ∈ D.gates := by rw [hs]; simp
  have hOp := hD.1 g hg
  let isAnd := match g.op with | .and => true | _ => false
  refine ⟨q,A,B,isAnd,?_,?_,by omega,?_,?_⟩
  · simpa only [List.length_nil,Nat.add_zero] using
      segAO D hD q [] P (g::T) (by simpa only [List.nil_append] using hs) _ hP
  · have h' : D.gates = (P++[g]) ++ T ++ [] := by simpa only [List.append_nil,List.append_assoc,List.singleton_append] using hs
    have hseg := segAO D hD q (P++[g]) T [] h' B.output hT
    have hn : 9+(P++[g]).length = 10+A.size := by simp [hA];omega
    exact hn ▸ hseg
  · change down q.val w < 9+A.size
    have := q.isLt
    have hw' := down_lt q.val w (10+P.length) (by omega) hwb hw
    omega
  · intro x b
    let old := List.ofFn (q.insertNth b x)
    let new := List.ofFn x
    let oldP := P.foldl stepWire old
    let newP := (P.map (mapPin q.val)).foldl stepWire new
    have R : PinRel q.val oldP newP := foldPin q.val P _ _ (initPin q b x) hP
    have hpin : oldP.getD q.val false = b := by
      rw [foldl_getD_lt P old q.val (by simpa [old] using q.isLt)]
      simp only [old,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos q.isLt,
        Option.getD_some,Fin.insertNth_apply_same]
    have hother : oldP.getD w false = A.eval new := by
      have xh := R.2.2 (down q.val w)
      rw [up_down q.val w hw] at xh
      exact xh
    let c := if isAnd = true then b && A.eval new else b || A.eval new
    have first : stepWire oldP g = oldP ++ [c] := by
      rcases hop with hg | hg <;> rcases hOp with hO | hO <;>
        rw [stepWire,hg,hO] <;>
        simp only [List.map_cons,List.map_nil,hpin,hother,GateOp.eval,List.all_cons,
          List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.true_and,Bool.or_false,Bool.false_or,
          c,isAnd,hO,if_true,Bool.false_eq_true,if_false,Bool.and_comm,Bool.or_comm]
    have R' : PinRel q.val (oldP ++ [c]) (newP ++ [c]) := addSame _ _ _ R _
    have H := (foldPin q.val T _ _ R' hT).2.2 (down q.val D.output)
    rw [up_down q.val D.output (by have hq := q.isLt; have ho := (outIsGate D he).1; omega)] at H
    have EE : D.wires old = T.foldl stepWire (oldP ++ [c]) := by
      rw [wires_eq_foldl,hs,List.foldl_append,List.foldl_cons]
      change T.foldl stepWire (stepWire oldP g) = _
      rw [first]
    change (D.wires old).getD D.output false = (B.wires (newP ++ [c])).getD B.output false
    rw [EE]
    exact H

private lemma proveAll (C : Circuit) (hC : IsAO2 10 C) (hB : C.size ≤ 18) (he : essential C) :
    ∃ (q : Fin 10) (A B : Circuit) (isAnd : Bool),
      IsAO2 9 A ∧ IsAO2 (10+A.size) B ∧
        A.size+B.size ≤ 17 ∧ A.output < 9+A.size ∧
      ∀ (x : Fin 9 → Bool) (b : Bool),
        C.eval (List.ofFn (q.insertNth b x)) =
          B.eval (A.wires (List.ofFn x) ++ [if isAnd = true then b && A.eval (List.ofFn x)
            else b || A.eval (List.ofFn x)]) := by
  classical
  have ex : ∃ n : ℕ, ∃ D : Circuit, IsAO2 10 D ∧ circuitFun 10 D = circuitFun 10 C ∧ D.size = n :=
    ⟨C.size,C,hC,rfl,rfl⟩
  obtain ⟨D,hd,hf,hs⟩ := Nat.find_spec ex
  have hle : D.size ≤ C.size := by rw [hs]; exact Nat.find_min' ex ⟨C,hC,rfl,rfl⟩
  have hm : IsSmallest 10 D := by
    intro F hf₁ hf₂
    rw [hs]
    exact Nat.find_min' ex ⟨F,hf₁,hf₂.trans hf,rfl⟩
  have hed : essential D := by
    intro i
    obtain ⟨x,hx⟩ := he i
    refine ⟨x,?_⟩
    change circuitFun 10 D (i.insertNth false x) ≠ circuitFun 10 D (i.insertNth true x)
    rwa [hf]
  obtain ⟨q,A,B,m,ha,hb,hsize,ho,hh⟩ := splitAtPin D hd hed (hle.trans hB) hm
  refine ⟨q,A,B,m,ha,hb,hsize,ho,?_⟩
  intro x b
  have h := hh x b
  change circuitFun 10 D (q.insertNth b x) = _ at h
  rw [hf] at h
  exact h

end PEqualNP.Outside.L_meta_18011

theorem PEqualNP.Outside.L_meta_18011 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ)), ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (x4.insertNth Bool.false x5)) ≠ x1.eval (List.ofFn (x4.insertNth Bool.true x5))) → ∃ (x5 : Fin (10 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool), PEqualNP.TopForm.IsAO2 (9 : ℕ) x6 ∧ PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x6.size) x7 ∧ x6.size + x7.size ≤ (17 : ℕ) ∧ x6.output < (9 : ℕ) + x6.size ∧ ∀ (x9 : Fin (9 : ℕ) → Bool) (x10 : Bool), x1.eval (List.ofFn (x5.insertNth x10 x9)) = x7.eval (x6.wires (List.ofFn x9) ++ [if x8 = Bool.true then x10 && x6.eval (List.ofFn x9) else x10 || x6.eval (List.ofFn x9)]) := PEqualNP.Outside.L_meta_18011.proveAll
