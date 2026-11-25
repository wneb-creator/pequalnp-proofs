import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def clipWire (i : ℕ) : ℕ := min i 29

def clipGate (g : Gate) : Gate := ⟨g.op, g.inputs.map clipWire⟩

def clipCircuit (C : Circuit) : Circuit :=
  ⟨C.gates.map clipGate, clipWire C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma clip_read (w : List Bool) (hw : w.length ≤ 29) (i : ℕ) :
    w.getD (clipWire i) false = w.getD i false := by
  by_cases hi : i ≤ 29
  · simp [clipWire, min_eq_left hi]
  · rw [clipWire, min_eq_right (by omega)]
    rw [List.getD_eq_default _ _ hw, List.getD_eq_default _ _ (by omega)]

lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma clip_run (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 29) :
    (gs.map clipGate).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have he : step w (clipGate g) = step w g := by
      simp only [step, clipGate, List.map_map, Function.comp_def,
        clip_read w (by omega)]
    simp only [List.map_cons, List.foldl_cons, he]
    apply ih
    simp only [step, List.length_append, List.length_singleton]
    simp only [List.length_cons] at hw
    omega

lemma clip_eval (C : Circuit) (w : List Bool) (hw : w.length + C.size ≤ 29) :
    (clipCircuit C).eval w = C.eval w := by
  change ((C.gates.map clipGate).foldl step w).getD (clipWire C.output) false =
    (C.gates.foldl step w).getD C.output false
  rw [clip_run _ _ hw]
  exact clip_read _ (by rw [run_length]; exact hw) _

abbrev GateCode := Fin 3 × Option (Fin 30 × Option (Fin 30))

def decodeOp (o : Fin 3) : GateOp :=
  if o.val = 0 then .and else if o.val = 1 then .or else .not

def encodeOp : GateOp → Fin 3
  | .and => 0
  | .or => 1
  | _ => 2

def encodeWire (i : ℕ) : Fin 30 := ⟨clipWire i, by unfold clipWire; omega⟩

def decodeInputs : Option (Fin 30 × Option (Fin 30)) → List ℕ
  | none => []
  | some (a, none) => [a.val]
  | some (a, some b) => [a.val, b.val]

def encodeInputs : List ℕ → Option (Fin 30 × Option (Fin 30))
  | [] => none
  | [a] => some (encodeWire a, none)
  | a :: b :: _ => some (encodeWire a, some (encodeWire b))

def decodeGate (g : GateCode) : Gate := ⟨decodeOp g.1, decodeInputs g.2⟩

def encodeGate (g : Gate) : GateCode := ⟨encodeOp g.op, encodeInputs g.inputs⟩

lemma decode_encode_inputs (l : List ℕ) (hl : l.length ≤ 2) :
    decodeInputs (encodeInputs l) = l.map clipWire := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l =>
      cases l with
      | nil => rfl
      | cons c l => simp at hl

lemma decode_encode_gate (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) : decodeGate (encodeGate g) = clipGate g := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hin⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  change Gate.mk (decodeOp (encodeOp op)) (decodeInputs (encodeInputs inputs)) = _
  rw [decode_encode_inputs inputs hin]
  rcases hop with rfl | rfl | rfl <;> rfl

lemma decode_gate_legal (g : GateCode) :
    (decodeGate g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (decodeGate g).inputs.length ≤ 2 := by
  constructor
  · change decodeOp g.1 ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
    unfold decodeOp
    split
    · simp
    · split <;> simp
  · rcases g with ⟨o, p⟩
    cases p with
    | none => simp [decodeGate, decodeInputs]
    | some p =>
      rcases p with ⟨a, b⟩
      cases b <;> simp [decodeGate, decodeInputs]

abbrev CircuitCode := (k : Fin 19) × ((Fin k.val → GateCode) × Fin 30)

def decodeCircuit (c : CircuitCode) : Circuit :=
  ⟨List.ofFn (fun i => decodeGate (c.2.1 i)), c.2.2.val⟩

def encodeCircuit (C : Circuit) (hs : C.size ≤ 18) : CircuitCode :=
  ⟨⟨C.size, by omega⟩, (fun i => encodeGate (C.gates.get i)), encodeWire C.output⟩

lemma decode_circuit_fan (c : CircuitCode) : FanInTwo (decodeCircuit c) := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact decode_gate_legal _

lemma decode_circuit_size (c : CircuitCode) : (decodeCircuit c).size = c.1.val := by
  simp [decodeCircuit, Circuit.size]

lemma decode_circuit_bound (c : CircuitCode) : (decodeCircuit c).size ≤ 18 := by
  rw [decode_circuit_size]
  exact Nat.le_of_lt_succ c.1.isLt

lemma decode_encode_circuit (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 18) :
    decodeCircuit (encodeCircuit C hs) = clipCircuit C := by
  apply congrArg₂ Circuit.mk
  · change List.ofFn (fun i : Fin C.gates.length =>
      decodeGate (encodeGate (C.gates.get i))) = C.gates.map clipGate
    have he : (fun i : Fin C.gates.length => decodeGate (encodeGate (C.gates.get i))) =
        (fun i : Fin C.gates.length => clipGate (C.gates.get i)) := by
      funext i
      exact decode_encode_gate _ (hf _ (List.get_mem _ _))
    rw [he]
    change List.ofFn (clipGate ∘ fun i : Fin C.gates.length => C.gates.get i) = _
    rw [← List.map_ofFn]
    simp
  · rfl

lemma finite_encoding_complete (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 18) :
    ∃ c : CircuitCode, (decodeCircuit c).size = C.size ∧
      ∀ w : List Bool, w.length = 11 → (decodeCircuit c).eval w = C.eval w := by
  refine ⟨encodeCircuit C hs, ?_, ?_⟩
  · rw [decode_circuit_size]
    rfl
  · intro w hw
    rw [decode_encode_circuit C hf hs]
    exact clip_eval C w (by omega)

lemma input_transport (n : ℕ) (C : Circuit) (p : Fin n → Fin n) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      ∀ (x : Fin n → Bool) (tail : List Bool),
        D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
  let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
  have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
  have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
  let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
  let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
  · exact List.length_map mapGate
  have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
      (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g rest ih =>
      let b := g.op.eval (g.inputs.map fun i => x.getD i false)
      have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
        simp only [b, mapGate, List.map_map, Function.comp_def, agree]
      change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
        ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
      rw [next]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i < x.length
      · have hy : rename i < y.length := by
          by_cases hn : i < n
          · have := early i hn
            omega
          · rw [late i (by omega)]
            omega
        rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len]
  intro x tail
  apply run C.gates _ _ (by simp) (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
    have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
    rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
        List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
    simp only [List.getElem_ofFn, Function.comp_apply]
    congr 1
    apply Fin.ext
    exact dite_eq_left hi
  · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
        List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
    simp

def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def input (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 && x 2]

lemma finite_exclusion_iff :
    (∀ c : CircuitCode, ∃ x : Fin 10 → Bool, (decodeCircuit c).eval (input x) ≠ edge x) ↔
    (∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C → C.size ≤ 18 →
      ∃ x : Fin 10 → Bool,
        C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) ≠ edge x) := by
  constructor
  · intro h C p hf hs
    obtain ⟨D, hD, sz, hev⟩ := input_transport 10 C p hf
    obtain ⟨c, _, hec⟩ := finite_encoding_complete D hD (sz.le.trans hs)
    obtain ⟨x, hx⟩ := h c
    refine ⟨x, ?_⟩
    rw [hec (input x) (by simp [input]), input, hev] at hx
    exact hx
  · intro h c
    obtain ⟨x, hx⟩ := h (decodeCircuit c) id (decode_circuit_fan c) (decode_circuit_bound c)
    exact ⟨x, by simpa [input, Function.comp_def] using hx⟩

def onSide {n : ℕ} (color : Fin n → Bool) (side : Bool) (x : Fin n → Bool) :
    Fin n → Bool := fun i => if color i = side then x i else false

lemma separator_forces_side {n : ℕ} (color : Fin n → Bool) (side : Bool)
    (g : (Fin n → Bool) → Bool) (hg : Monotone g) (p q : Fin n → Bool) (i : Fin n)
    (hs : ∀ j, j ≠ i → p j ≤ q j)
    (hp : g (onSide color side p) = true) (hq : g (onSide color side q) = false) :
    color i = side := by
  by_contra hi
  have hle : onSide color side p ≤ onSide color side q := by
    intro j
    by_cases hj : color j = side
    · have hji : j ≠ i := by
        intro he
        subst j
        exact hi hj
      simpa only [onSide, ite_eq_left hj] using hs j hji
    · simp [onSide, hj]
  have h := hg hle
  rw [hp, hq] at h
  cases h rfl

lemma or_root_forces_same_side {n : ℕ} (color : Fin n → Bool)
    (a b : (Fin n → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (p q r : Fin n → Bool) (i j : Fin n)
    (hi : ∀ k, k ≠ i → p k ≤ q k) (hj : ∀ k, k ≠ j → p k ≤ r k)
    (hp : (a (onSide color false p) || b (onSide color true p)) = true)
    (hq : (a (onSide color false q) || b (onSide color true q)) = false)
    (hr : (a (onSide color false r) || b (onSide color true r)) = false) :
    color i = color j := by
  obtain ⟨hqa, hqb⟩ := Bool.or_eq_false_iff.mp hq
  obtain ⟨hra, hrb⟩ := Bool.or_eq_false_iff.mp hr
  rcases Bool.or_eq_true_iff.mp hp with hpa | hpb
  · exact (separator_forces_side color false a ha p q i hi hpa hqa).trans
      (separator_forces_side color false a ha p r j hj hpa hra).symm
  · exact (separator_forces_side color true b hb p q i hi hpb hqb).trans
      (separator_forces_side color true b hb p r j hj hpb hrb).symm

lemma and_root_forces_same_side {n : ℕ} (color : Fin n → Bool)
    (a b : (Fin n → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (p q r : Fin n → Bool) (i j : Fin n)
    (hi : ∀ k, k ≠ i → p k ≤ r k) (hj : ∀ k, k ≠ j → q k ≤ r k)
    (hp : (a (onSide color false p) && b (onSide color true p)) = true)
    (hq : (a (onSide color false q) && b (onSide color true q)) = true)
    (hr : (a (onSide color false r) && b (onSide color true r)) = false) :
    color i = color j := by
  obtain ⟨hpa, hpb⟩ := Bool.and_eq_true_iff.mp hp
  obtain ⟨hqa, hqb⟩ := Bool.and_eq_true_iff.mp hq
  rcases Bool.and_eq_false_iff.mp hr with hra | hrb
  · exact (separator_forces_side color false a ha p r i hi hpa hra).trans
      (separator_forces_side color false a ha q r j hj hqa hra).symm
  · exact (separator_forces_side color true b hb p r i hi hpb hrb).trans
      (separator_forces_side color true b hb q r j hj hqb hrb).symm

lemma onSide_empty {n : ℕ} (color : Fin n → Bool) (side : Bool)
    (p : Fin n → Bool) (i j : Fin n)
    (hp : ∀ k, k ≠ i → k ≠ j → p k = false)
    (hi : color i ≠ side) (hj : color j ≠ side) :
    onSide color side p = fun _ => false := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [onSide, hi]
  by_cases hkj : k = j
  · subst k
    simp [onSide, hj]
  simp [onSide, hp k hki hkj]

lemma onSide_full {n : ℕ} (color : Fin n → Bool) (side : Bool)
    (p : Fin n → Bool) (i j : Fin n)
    (hp : ∀ k, k ≠ i → k ≠ j → p k = true)
    (hi : color i ≠ side) (hj : color j ≠ side) :
    onSide color side p = onSide color side (fun _ => true) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [onSide, hi]
  by_cases hkj : k = j
  · subst k
    simp [onSide, hj]
  simp [onSide, hp k hki hkj]

lemma and_root_forces_opposite_side {n : ℕ} (color : Fin n → Bool)
    (a b : (Fin n → Bool) → Bool)
    (ha : a (fun _ => false) = false) (hb : b (fun _ => false) = false)
    (p : Fin n → Bool) (i j : Fin n)
    (hp : ∀ k, k ≠ i → k ≠ j → p k = false)
    (hout : (a (onSide color false p) && b (onSide color true p)) = true) :
    color i ≠ color j := by
  intro he
  obtain ⟨hpa, hpb⟩ := Bool.and_eq_true_iff.mp hout
  cases hi : color i
  · have h := onSide_empty color true p i j hp (by simp [hi]) (by rw [← he, hi]; decide)
    rw [h, hb] at hpb
    contradiction
  · have h := onSide_empty color false p i j hp (by simp [hi]) (by rw [← he, hi]; decide)
    rw [h, ha] at hpa
    contradiction

lemma or_root_forces_opposite_side {n : ℕ} (color : Fin n → Bool)
    (a b : (Fin n → Bool) → Bool)
    (ha : a (onSide color false (fun _ => true)) = true)
    (hb : b (onSide color true (fun _ => true)) = true)
    (p : Fin n → Bool) (i j : Fin n)
    (hp : ∀ k, k ≠ i → k ≠ j → p k = true)
    (hout : (a (onSide color false p) || b (onSide color true p)) = false) :
    color i ≠ color j := by
  intro he
  obtain ⟨hpa, hpb⟩ := Bool.or_eq_false_iff.mp hout
  cases hi : color i
  · have h := onSide_full color true p i j hp (by simp [hi]) (by rw [← he, hi]; decide)
    rw [h, hb] at hpb
    contradiction
  · have h := onSide_full color false p i j hp (by simp [hi]) (by rw [← he, hi]; decide)
    rw [h, ha] at hpa
    contradiction

end PEqualNP.Outside.L_meta_1890_aux
