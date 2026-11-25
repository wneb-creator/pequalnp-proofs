namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def BinaryAO (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (g : Gate), C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

def DerivativeTrace (n : ℕ) (C : Circuit) (base seed : Fin n → Bool)
    (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = seed i) ∧
  ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
    (g.op = .and → d (n+j) =
      (((C.wires (List.ofFn base)).getD a false && d b) ||
        (d a && (C.wires (List.ofFn base)).getD b false))) ∧
    (g.op = .or → d (n+j) = (d a || d b))

def directGate (g : Gate) : Bool × ℕ × ℕ :=
  (na_isAnd g.op, g.inputs.getD 0 0, g.inputs.getD 1 0)

def directDag (C : Circuit) : Dag := C.gates.map directGate

lemma directDag_length (C : Circuit) : (directDag C).length = C.size := by
  simp [directDag, Circuit.size]

lemma directDag_ops {C : Circuit} {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) :
    tag (directDag C) j = na_isAnd g.op ∧
    opA (directDag C) j = g.inputs.getD 0 0 ∧
    opB (directDag C) j = g.inputs.getD 1 0 := by
  simp [tag, opA, opB, directDag, directGate,
    List.getD_eq_getElem?_getD, hg]

lemma directDag_strict {n : ℕ} {C : Circuit} (normal : BinaryAO n C) :
    Strict n (directDag C) := by
  intro j hj
  have hj' : j < C.gates.length := by simpa [directDag] using hj
  let g := C.gates[j]
  have atGate : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
  obtain ⟨_,a,b,inputs,different,left,right⟩ := normal j g atGate
  obtain ⟨_,ea,eb⟩ := directDag_ops atGate
  simp only [inputs, List.getD_cons_zero, List.getD_cons_succ] at ea eb
  exact ⟨by simpa only [ea] using left, by simpa only [eb] using right,
    by simpa only [ea,eb] using different⟩

lemma directDag_fold (gs : List Gate)
    (shape : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧
      ∃ a b, g.inputs = [a,b]) (x : List Bool) :
    wl (gs.map directGate) x =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,a,b,inputs⟩ := shape g (by simp)
    have step : wstep x (directGate g) =
        x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] := by
      rcases op with ha | ho
      · simp [wstep, directGate, inputs, ha, na_isAnd, GateOp.eval, gop]
      · simp [wstep, directGate, inputs, ho, na_isAnd, GateOp.eval, gop]
    simp only [List.map_cons, wl, List.foldl_cons]
    rw [step]
    apply ih
    intro q hq
    exact shape q (by simp [hq])

lemma directDag_wires {n : ℕ} {C : Circuit} (normal : BinaryAO n C) (x : List Bool) :
    wl (directDag C) x = C.wires x := by
  apply directDag_fold
  intro g hg
  obtain ⟨j,hj,hg⟩ := List.mem_iff_getElem.mp hg
  have atGate : C.gates[j]? = some g := by rw [← hg]; exact List.getElem?_eq_getElem hj
  obtain ⟨op,a,b,inputs,_⟩ := normal j g atGate
  exact ⟨op,a,b,inputs⟩

lemma directDag_val {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (x : Fin n → Bool) (w : ℕ) :
    val (directDag C) x w = (C.wires (List.ofFn x)).getD w false := by
  rw [val, directDag_wires normal]

lemma directDag_eval {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (x : Fin n → Bool) :
    val (directDag C) x C.output = C.eval (List.ofFn x) :=
  directDag_val normal x C.output

def SingleReaderTrace (n : ℕ) (D : Dag) (base : Fin n → Bool)
    (v : Fin n) (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = decide (i = v)) ∧
  ∀ j, j < D.length →
    d (n + j) = if tag D j then
      (val D base (opA D j) && d (opB D j)) ||
        (d (opA D j) && val D base (opB D j))
    else d (opA D j) || d (opB D j)

lemma directDag_trace {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base : Fin n → Bool) (v : Fin n) (d : ℕ → Bool)
    (trace : DerivativeTrace n C base (single v) d) :
    SingleReaderTrace n (directDag C) base v d := by
  refine ⟨trace.1, ?_⟩
  intro j hj
  have hj' : j < C.gates.length := by simpa [directDag] using hj
  let g := C.gates[j]
  have atGate : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
  obtain ⟨op,a,b,inputs,_⟩ := normal j g atGate
  obtain ⟨et,ea,eb⟩ := directDag_ops atGate
  simp only [inputs, List.getD_cons_zero, List.getD_cons_succ] at ea eb
  rw [et,ea,eb]
  rcases op with ha | ho
  · simp only [ha,na_isAnd,ite_true]
    rw [directDag_val normal, directDag_val normal]
    exact (trace.2 j g a b atGate inputs).1 ha
  · simp only [ho,na_isAnd,ite_false]
    exact (trace.2 j g a b atGate inputs).2 ho

def dagGate (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def dagCircuit (D : Dag) (output : ℕ) : Circuit :=
  ⟨D.map dagGate, output⟩

lemma dagCircuit_size (D : Dag) (output : ℕ) : (dagCircuit D output).size = D.length := by
  simp [dagCircuit, Circuit.size]

lemma dagCircuit_monotone (D : Dag) (output : ℕ) : Monotone2 (dagCircuit D output) := by
  intro g hg
  obtain ⟨⟨t,a,b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases t <;> simp [dagGate]

lemma dagCircuit_fold (D : Dag) (x : List Bool) :
    (D.map dagGate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = wl D x := by
  induction D generalizing x with
  | nil => rfl
  | cons g D ih =>
    obtain ⟨t,a,b⟩ := g
    cases t
    · simpa [dagGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop false (x.getD a false) (x.getD b false)])
    · simpa [dagGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop true (x.getD a false) (x.getD b false)])

lemma dagCircuit_wires (D : Dag) (output : ℕ) (x : List Bool) :
    (dagCircuit D output).wires x = wl D x := dagCircuit_fold D x

lemma dagCircuit_eval (D : Dag) (output : ℕ) {n : ℕ} (x : Fin n → Bool) :
    (dagCircuit D output).eval (List.ofFn x) = val D x output := by
  rw [Circuit.eval, dagCircuit_wires]
  rfl

lemma minimal_circuit_dag_bound {n : ℕ} {C : Circuit}
    (minimal : IsMinimalMonoCircuit n C) (D : Dag) (output : ℕ)
    (same : ∀ x : Fin n → Bool, val D x output = C.eval (List.ofFn x)) :
    C.size ≤ D.length := by
  have eqFun : circuitFun n (dagCircuit D output) = circuitFun n C := by
    funext x
    exact (dagCircuit_eval D output x).trans (same x)
  simpa only [dagCircuit_size] using
    minimal.2 (dagCircuit D output) (dagCircuit_monotone D output) eqFun

lemma directDag_minimal {n : ℕ} {C : Circuit}
    (minimal : IsMinimalMonoCircuit n C) :
    ∀ E : Dag, Strict n E → E ≠ [] →
      (∀ x : Fin n → Bool, val E x (outW n E) = C.eval (List.ofFn x)) →
      (directDag C).length ≤ E.length := by
  intro E _ _ same
  rw [directDag_length]
  exact minimal_circuit_dag_bound minimal E (outW n E) same


theorem minimal_dag_output_last {n : ℕ} (F : (Fin n → Bool) → Bool)
    (D : Dag) (o : ℕ) (hS : Strict n D)
    (hD : ∀ x, val D x o = F x)
    (hnc : ∀ b : Bool, ∃ x, F x ≠ b)
    (hnp : ∀ i : Fin n, ∃ x, F x ≠ x i)
    (hmin : ∀ E : Dag, Strict n E → E ≠ [] →
      (∀ x, val E x (outW n E) = F x) → D.length ≤ E.length) :
    o = outW n D ∧ D ≠ [] := by
  obtain ⟨x, hx⟩ := hnc false
  have ho : o < n + D.length := by
    by_contra hn
    exact hx ((hD x).symm.trans (val_ge D x o (by omega)))
  have hon : n ≤ o := by
    by_contra hn
    have hi : o < n := by omega
    obtain ⟨y, hy⟩ := hnp ⟨o, hi⟩
    exact hy ((hD y).symm.trans (val_input D y o hi))
  have hne : D ≠ [] := by
    intro he
    have hz : D.length = 0 := by rw [he]; rfl
    omega
  let k := o - n + 1
  have hk : k ≤ D.length := by dsimp [k]; omega
  have hlen : (D.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  have hneTake : D.take k ≠ [] := by
    intro he
    have hz : (D.take k).length = 0 := by rw [he]; rfl
    rw [hlen] at hz
    dsimp [k] at hz
    omega
  have hev : ∀ y, val (D.take k) y (outW n (D.take k)) = F y := by
    intro y
    have hout : outW n (D.take k) = o := by
      unfold outW
      rw [hlen]
      dsimp [k]
      omega
    rw [hout, val_take D y k o (by dsimp [k]; omega) hk]
    exact hD y
  have hbound := hmin (D.take k) (na_strict_take hS k) hneTake hev
  rw [hlen] at hbound
  refine ⟨?_, hne⟩
  unfold outW
  dsimp [k] at hbound hk
  omega

theorem minimal_dag_live {n : ℕ} (F : (Fin n → Bool) → Bool)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x, val D x (outW n D) = F x)
    (hess : ∀ i : Fin n, ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (hmin : ∀ E : Dag, Strict n E → E ≠ [] →
      (∀ x, val E x (outW n E) = F x) → D.length ≤ E.length) :
    StrictLive n D := by
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  refine ⟨hS, ?_, hne⟩
  intro w hw
  by_contra hn
  have hf0 : fanout D w = 0 := by omega
  by_cases hwn : w < n
  · obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
    apply hFne
    rw [← hD x, ← hD y]
    have hout : outW n D ≠ w := by unfold outW; omega
    have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
      (fun i hi => by
        by_cases hiw : i = w
        · subst hiw; simp
        · simp only [hiw, ite_false]
          rw [val_input D x i hi]
          exact hxy ⟨i, hi⟩ (fun he => hiw (congrArg Fin.val he)))
      (fun j hj => by
        obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
        have hnj : n + j ≠ w := by omega
        simp only [hnj, ha, hb, ite_false]
        exact val_gate hS x j hj)
      (outW n D) (by unfold outW; omega)
    simp only [hout, ite_false] at key
    exact key.symm
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < D.length := by omega
    have hl := na_del_length n j D hj
    have hs := na_del_strict hS j hj hf0
    have hneDel : na_del n j D ≠ [] := by
      intro he
      rw [he] at hl
      simp only [List.length_nil] at hl
      omega
    have hev : ∀ x, val (na_del n j D) x (outW n (na_del n j D)) = F x := by
      intro x
      have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by
        unfold outW
        rw [hl]
      have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
        unfold na_up outW
        split_ifs <;> omega
      rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
      exact hD x
    have hb := hmin (na_del n j D) hs hneDel hev
    rw [hl] at hb
    omega

theorem minimal_dag_output_live {n : ℕ} (F : (Fin n → Bool) → Bool)
    (D : Dag) (o : ℕ) (hS : Strict n D)
    (hD : ∀ x, val D x o = F x)
    (hnc : ∀ b : Bool, ∃ x, F x ≠ b)
    (hnp : ∀ i : Fin n, ∃ x, F x ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (hmin : ∀ E : Dag, Strict n E → E ≠ [] →
      (∀ x, val E x (outW n E) = F x) → D.length ≤ E.length) :
    o = outW n D ∧ StrictLive n D := by
  obtain ⟨ho, hne⟩ := minimal_dag_output_last F D o hS hD hnc hnp hmin
  exact ⟨ho, minimal_dag_live F D hS hne (by simpa [ho] using hD) hess hmin⟩

theorem minimal_binaryAO_direct_live {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (minimal : IsMinimalMonoCircuit n C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    C.output = outW n (directDag C) ∧ StrictLive n (directDag C) :=
  minimal_dag_output_live (fun x => C.eval (List.ofFn x)) (directDag C) C.output
    (directDag_strict normal) (directDag_eval normal) hnc hnp hess
    (directDag_minimal minimal)

theorem minimal_binaryAO_preserves_traces {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (minimal : IsMinimalMonoCircuit n C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length = C.size ∧ C.output = outW n D ∧
      (∀ x : List Bool, wl D x = C.wires x) ∧
      (∀ base : Fin n → Bool, ∀ v : Fin n, ∀ d : ℕ → Bool,
        DerivativeTrace n C base (single v) d → SingleReaderTrace n D base v d) := by
  obtain ⟨output,live⟩ := minimal_binaryAO_direct_live normal minimal hnc hnp hess
  exact ⟨directDag C,live,directDag_length C,output,directDag_wires normal,
    fun base v d trace => directDag_trace normal base v d trace⟩

def cyclicPerm : Equiv.Perm (Fin 14) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 11, 10, 9, 8]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 11, 10, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cyclicPerm_point : ∀ p : Fin 7,
    cyclicPerm (Fin.castAdd 7 p) = Fin.castAdd 7 p := by decide +kernel

theorem cyclicPerm_line : ∀ l : Fin 7,
    cyclicPerm (Fin.natAdd 7 l) = Fin.natAdd 7 (-l) := by decide +kernel

theorem cyclic_incidence : ∀ p l : Fin 7,
    (p.val, (-l).val + 7) ∈ edgeList ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by
  decide +kernel

theorem cyclic_edge_sides : ∀ u v : Fin 14,
    (u.val, v.val) ∈ edgeList → ∃ p l : Fin 7,
      u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 (-l) ∧
      (p = l ∨ p = l + 1 ∨ p = l + 3) := by decide +kernel

theorem cyclic_Heawood (x : Fin 14 → Bool) :
    HeawoodEdge (x ∘ cyclicPerm) ↔ ∃ p l : Fin 7,
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    obtain ⟨p, l, rfl, rfl, hi⟩ := cyclic_edge_sides u v he
    refine ⟨p, l, hi, ?_, ?_⟩
    · simpa only [Function.comp_apply, cyclicPerm_point] using hu
    · simpa only [Function.comp_apply, cyclicPerm_line, neg_neg] using hv
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨Fin.castAdd 7 p, Fin.natAdd 7 (-l), (by simpa [Nat.add_comm] using (cyclic_incidence p l).mpr hi), ?_, ?_⟩
    · simpa only [Function.comp_apply, cyclicPerm_point] using hp
    · simpa only [Function.comp_apply, cyclicPerm_line, neg_neg] using hl


def MarkedTrace (n : ℕ) (D : Dag) (base : Fin n → Bool)
    (v : Fin n) (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = decide (i = v)) ∧
  ∀ j, j < D.length → d (n + j) = if tag D j then
    (val D base (opA D j) && d (opB D j)) ||
      (d (opA D j) && val D base (opB D j))
    else d (opA D j) || d (opB D j)

theorem relabel_trace {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) {base : Fin n → Bool} {v : Fin n} {d : ℕ → Bool}
    (h : MarkedTrace n D base v d) :
    MarkedTrace n (relabel σ D) (fun i => base (σ.symm i)) (σ v)
      (fun w => d (liftP σ.symm w)) := by
  have hv (w : ℕ) :
      val (relabel σ D) (fun i => base (σ.symm i)) (liftP σ w) = val D base w := by
    simpa using relabel_val σ hS (fun i => base (σ.symm i)) w
  have hinv (w : ℕ) : liftP σ.symm (liftP σ w) = w := liftP_inv σ w
  constructor
  · intro i
    dsimp only
    rw [tr_liftP_lt σ.symm i.isLt, h.1]
    simp
    constructor
    · intro hi
      simpa using congrArg σ hi
    · intro hi
      rw [hi]
      exact σ.symm_apply_apply v
  · intro j hj
    rw [relabel_length] at hj
    dsimp only
    rw [tr_liftP_ge σ.symm (Nat.le_add_right n j), tr_tag σ D j hj,
      tr_opA σ D j hj, tr_opB σ D j hj, hinv, hinv, hv, hv]
    exact h.2 j hj


theorem cyclicPerm_involutive : ∀ i : Fin 14, cyclicPerm (cyclicPerm i) = i := by
  decide +kernel

theorem cyclic_relabel_correct {D : Dag} (hS : Strict 14 D) (hne : D ≠ [])
    (hC : ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ ∃ p l : Fin 7,
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) :
    ∀ x : Fin 14 → Bool,
      val (relabel cyclicPerm D) x (outW 14 (relabel cyclicPerm D)) = true ↔
      HeawoodEdge x := by
  intro x
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have ho : 14 ≤ outW 14 D := by unfold outW; omega
  have hv := relabel_val cyclicPerm hS x (outW 14 D)
  rw [tr_liftP_ge cyclicPerm ho] at hv
  have heq : outW 14 (relabel cyclicPerm D) = outW 14 D := by
    simp [outW, relabel_length]
  rw [heq, hv, hC]
  have hc := cyclic_Heawood (fun i => x (cyclicPerm i))
  have hx : (fun i => x (cyclicPerm i)) ∘ cyclicPerm = x := by
    funext i
    simp only [Function.comp_apply, cyclicPerm_involutive]
  rw [hx] at hc
  exact hc.symm

theorem relabel_single (n : ℕ) (σ : Equiv.Perm (Fin n)) (u : Fin n) :
    (fun i => single u (σ.symm i)) = single (σ u) := by
  funext i
  simp only [single]
  simp
  constructor
  · intro hi
    simpa using congrArg σ hi
  · intro hi
    rw [hi]
    exact σ.symm_apply_apply u

theorem relabel_single_trace {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) {u v : Fin n} {d : ℕ → Bool}
    (h : MarkedTrace n D (single u) v d) :
    MarkedTrace n (relabel σ D) (single (σ u)) (σ v)
      (fun w => d (liftP σ.symm w)) := by
  have ht := relabel_trace σ hS h
  rw [relabel_single] at ht
  exact ht


def CyclicCorrect (C : Circuit) : Prop :=
  ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
    (p = l ∨ p = l+1 ∨ p = l+3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

lemma cyclic_correct_composed {C : Circuit} (correct : CyclicCorrect C)
    (x : Fin 14 → Bool) : C.eval (List.ofFn (x ∘ cyclicPerm)) = true ↔ HeawoodEdge x := by
  have invol : (x ∘ cyclicPerm) ∘ cyclicPerm = x := by
    funext i
    simp only [Function.comp_apply,cyclicPerm_involutive]
  rw [correct,← cyclic_Heawood,invol]

lemma cyclic_nonconstant {C : Circuit} (correct : CyclicCorrect C) :
    ∀ b : Bool, ∃ x : Fin 14 → Bool, C.eval (List.ofFn x) ≠ b := by
  intro b
  cases b
  · let x : Fin 14 → Bool := fun i => decide (i = 0) || decide (i = 7)
    refine ⟨x ∘ cyclicPerm,?_⟩
    rw [Ne,Bool.not_eq_false]
    exact (cyclic_correct_composed correct x).mpr (heawood_pair (by decide : Adj 0 7))
  · refine ⟨(fun _ : Fin 14 => false) ∘ cyclicPerm,?_⟩
    intro ht
    exact heawood_not_empty ((cyclic_correct_composed correct _).mp ht)

lemma cyclic_nonprojection {C : Circuit} (correct : CyclicCorrect C) :
    ∀ i : Fin 14, ∃ x : Fin 14 → Bool, C.eval (List.ofFn x) ≠ x i := by
  intro i
  let x := single (cyclicPerm i)
  refine ⟨x ∘ cyclicPerm,?_⟩
  intro eq
  have value : (x ∘ cyclicPerm) i = true := by simp [x,single]
  have yes : C.eval (List.ofFn (x ∘ cyclicPerm)) = true := eq.trans value
  exact heawood_not_single _ ((cyclic_correct_composed correct x).mp yes)

lemma cyclic_essential {C : Circuit} (correct : CyclicCorrect C) :
    ∀ i : Fin 14, ∃ x y : Fin 14 → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
  intro i
  obtain ⟨x,y,agree,no,yes⟩ := heawood_essential (cyclicPerm i)
  refine ⟨x ∘ cyclicPerm,y ∘ cyclicPerm,?_,?_⟩
  · intro k hk
    exact agree (cyclicPerm k) (fun he => hk (cyclicPerm.injective he))
  · intro equal
    apply no
    apply (cyclic_correct_composed correct x).mp
    rw [equal]
    exact (cyclic_correct_composed correct y).mpr yes

lemma cyclic_lb_27 (C : Circuit) (mono : Monotone2 C) (correct : CyclicCorrect C) :
    27 ≤ C.size := by
  obtain ⟨D,live,length,evaluate⟩ := normalize_strictLive C mono
    (cyclic_nonconstant correct) (cyclic_nonprojection correct) (cyclic_essential correct)
  have cyc : ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ ∃ p l : Fin 7,
      (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x
    rw [evaluate]
    exact correct x
  let E := relabel cyclicPerm D
  have official : Correct E := cyclic_relabel_correct live.1 live.2.2 cyc
  have bound := heawood_lb_27 (dagCircuit E (outW 14 E)) (dagCircuit_monotone _ _)
    (fun x => by rw [dagCircuit_eval]; exact official x)
  rw [dagCircuit_size,relabel_length] at bound
  omega

lemma binaryAO_monotone {n : ℕ} {C : Circuit} (normal : BinaryAO n C) : Monotone2 C := by
  intro g hg
  obtain ⟨j,hj,hg⟩ := List.mem_iff_getElem.mp hg
  have atGate : C.gates[j]? = some g := by rw [← hg]; exact List.getElem?_eq_getElem hj
  obtain ⟨op,a,b,inputs,_⟩ := normal j g atGate
  exact ⟨op,by simp [inputs]⟩

lemma cyclic_minimal {C : Circuit} (normal : BinaryAO 14 C) (size : C.size ≤ 27)
    (correct : CyclicCorrect C) : IsMinimalMonoCircuit 14 C := by
  refine ⟨binaryAO_monotone normal,?_⟩
  intro E mono same
  apply size.trans
  apply cyclic_lb_27 E mono
  intro x
  have equal := congrFun same x
  change E.eval (List.ofFn x) = C.eval (List.ofFn x) at equal
  rw [equal]
  exact correct x

lemma relabel_quiet_trace {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (live : StrictLive n D) {u v : Fin n} {d : ℕ → Bool}
    (trace : MarkedTrace n D (single u) v d) (quiet : d (outW n D) = false) :
    MarkedTrace n (relabel σ D) (single (σ u)) (σ v)
      (fun w => d (liftP σ.symm w)) ∧
    d (liftP σ.symm (outW n (relabel σ D))) = false := by
  refine ⟨relabel_single_trace σ live.1 trace,?_⟩
  have positive : 0 < D.length := List.length_pos_iff.mpr live.2.2
  have bound : n ≤ outW n (relabel σ D) := by simp only [outW,relabel_length]; omega
  rw [tr_liftP_ge σ.symm bound]
  simpa only [outW,relabel_length] using quiet

lemma point_single_values : ∀ p m : Fin 7,
    single (Fin.castAdd 7 p) (Fin.castAdd 7 m) = decide (m = p) ∧
    single (Fin.castAdd 7 p) (Fin.natAdd 7 m) = false := by decide +kernel

lemma line_single_values : ∀ l m : Fin 7,
    single (Fin.natAdd 7 l) (Fin.castAdd 7 m) = false ∧
    single (Fin.natAdd 7 l) (Fin.natAdd 7 m) = decide (m = l) := by decide +kernel

def Posted1479 : Prop :=
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)

lemma posted_to_heawood (posted : Posted1479) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 27 ∧
      ∃ u v : Fin 14, Adj u v ∧ ∃ d e : ℕ → Bool,
        MarkedTrace 14 D (single u) v d ∧ MarkedTrace 14 D (single v) u e ∧
        d (outW 14 D) = false ∧ e (outW 14 D) = false := by
  obtain ⟨C,size,normal,correct,p,l,incident,⟨d,din,dg,dq⟩,⟨e,ein,eg,eq⟩⟩ := posted
  have td : DerivativeTrace 14 C (single (Fin.castAdd 7 p)) (single (Fin.natAdd 7 l)) d := by
    refine ⟨?_,dg⟩
    intro i
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro m
      change d m.val = single (Fin.natAdd 7 l) (Fin.castAdd 7 m)
      rw [(line_single_values l m).1]
      exact (din m).1
    · intro m
      change d (7+m.val) = single (Fin.natAdd 7 l) (Fin.natAdd 7 m)
      rw [(line_single_values l m).2]
      exact (din m).2
  have te : DerivativeTrace 14 C (single (Fin.natAdd 7 l)) (single (Fin.castAdd 7 p)) e := by
    refine ⟨?_,eg⟩
    intro i
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro m
      change e m.val = single (Fin.castAdd 7 p) (Fin.castAdd 7 m)
      rw [(point_single_values p m).1]
      exact (ein m).1
    · intro m
      change e (7+m.val) = single (Fin.castAdd 7 p) (Fin.natAdd 7 m)
      rw [(point_single_values p m).2]
      exact (ein m).2
  have minimal := cyclic_minimal normal size correct
  obtain ⟨output,live⟩ := minimal_binaryAO_direct_live normal minimal
    (cyclic_nonconstant correct) (cyclic_nonprojection correct) (cyclic_essential correct)
  have cyc : ∀ x : Fin 14 → Bool, val (directDag C) x (outW 14 (directDag C)) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x
    rw [← output,directDag_eval normal]
    exact correct x
  have tdD : MarkedTrace 14 (directDag C) (single (Fin.castAdd 7 p)) (Fin.natAdd 7 l) d :=
    directDag_trace normal _ _ _ td
  have teD : MarkedTrace 14 (directDag C) (single (Fin.natAdd 7 l)) (Fin.castAdd 7 p) e :=
    directDag_trace normal _ _ _ te
  have qd : d (outW 14 (directDag C)) = false := by rw [← output]; exact dq
  have qe : e (outW 14 (directDag C)) = false := by rw [← output]; exact eq
  obtain ⟨tdR,qdR⟩ := relabel_quiet_trace cyclicPerm live tdD qd
  obtain ⟨teR,qeR⟩ := relabel_quiet_trace cyclicPerm live teD qe
  have edge : Adj (cyclicPerm (Fin.castAdd 7 p)) (cyclicPerm (Fin.natAdd 7 l)) := by
    left
    rw [cyclicPerm_point,cyclicPerm_line]
    change (p.val,7+(-l).val) ∈ edgeList
    simpa [Nat.add_comm] using (cyclic_incidence p l).mpr incident
  refine ⟨relabel cyclicPerm (directDag C),relabel_strictLive cyclicPerm live,
    cyclic_relabel_correct live.1 live.2.2 cyc,?_,_,_,edge,
    (fun w => d (liftP cyclicPerm.symm w)),(fun w => e (liftP cyclicPerm.symm w)),
    tdR,teR,qdR,qeR⟩
  rw [relabel_length,directDag_length]
  exact size

lemma heawood_quiet_to_canonical {D : Dag} (live : StrictLive 14 D) (correct : Correct D)
    (size : D.length ≤ 27) (u v : Fin 14) (edge : Adj u v) (d e : ℕ → Bool)
    (td : MarkedTrace 14 D (single u) v d) (te : MarkedTrace 14 D (single v) u e)
    (qd : d (outW 14 D) = false) (qe : e (outW 14 D) = false) :
    ∃ E : Dag, StrictLive 14 E ∧ Correct E ∧ E.length ≤ 27 ∧
      (ineligSet 14 E = ∅ ∨ ineligSet 14 E ∈ canonI) ∧
      ∃ a b : Fin 14, Adj a b ∧ ∃ f g : ℕ → Bool,
        MarkedTrace 14 E (single a) b f ∧ MarkedTrace 14 E (single b) a g ∧
        f (outW 14 E) = false ∧ g (outW 14 E) = false := by
  by_cases empty : ineligSet 14 D = ∅
  · exact ⟨D,live,correct,size,Or.inl empty,u,v,edge,d,e,td,te,qd,qe⟩
  · have independent := (heawood_cover_iff_indep D).mp (elig_isCover live correct)
    obtain ⟨σ,aut,canonical⟩ := indep_classification (ineligSet 14 D) independent
      (Finset.nonempty_iff_ne_empty.mpr empty)
    obtain ⟨liveE,correctE,lengthE,_,_,_,_,ineligibleE⟩ := heawood_relabel σ aut live correct
    obtain ⟨tf,qf⟩ := relabel_quiet_trace σ live td qd
    obtain ⟨tg,qg⟩ := relabel_quiet_trace σ live te qe
    refine ⟨relabel σ D,liveE,correctE,by rw [lengthE]; exact size,
      Or.inr (by rw [ineligibleE]; exact canonical),σ u,σ v,(aut u v).mpr edge,
      (fun w => d (liftP σ.symm w)),(fun w => e (liftP σ.symm w)),tf,tg,qf,qg⟩

lemma posted_to_canonical (posted : Posted1479) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 27 ∧
      (ineligSet 14 D = ∅ ∨ ineligSet 14 D ∈ canonI) ∧
      ∃ u v : Fin 14, Adj u v ∧ ∃ d e : ℕ → Bool,
        MarkedTrace 14 D (single u) v d ∧ MarkedTrace 14 D (single v) u e ∧
        d (outW 14 D) = false ∧ e (outW 14 D) = false := by
  obtain ⟨D,live,correct,size,u,v,edge,d,e,td,te,qd,qe⟩ := posted_to_heawood posted
  exact heawood_quiet_to_canonical live correct size u v edge d e td te qd qe

lemma posted_refutation_of_canonical
    (noquiet : ∀ D : Dag, StrictLive 14 D → Correct D → D.length ≤ 27 →
      (ineligSet 14 D = ∅ ∨ ineligSet 14 D ∈ canonI) →
      ∀ u v : Fin 14, Adj u v → ∀ d e : ℕ → Bool,
        MarkedTrace 14 D (single u) v d → MarkedTrace 14 D (single v) u e →
        ¬ (d (outW 14 D) = false ∧ e (outW 14 D) = false)) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  intro posted
  obtain ⟨D,live,correct,size,canonical,u,v,edge,d,e,td,te,qd,qe⟩ := posted_to_canonical posted
  exact noquiet D live correct size canonical u v edge d e td te ⟨qd,qe⟩

lemma posted_refutation_of_universal
    (noquiet : ∀ D : Dag, StrictLive 14 D → Correct D → D.length ≤ 27 →
      ∀ u v : Fin 14, Adj u v → ∀ d e : ℕ → Bool,
        MarkedTrace 14 D (single u) v d → MarkedTrace 14 D (single v) u e →
        ¬ (d (outW 14 D) = false ∧ e (outW 14 D) = false)) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) :=
  posted_refutation_of_canonical (fun D live correct size _ => noquiet D live correct size)

end PEqualNP.Outside.L_meta_6659_aux
