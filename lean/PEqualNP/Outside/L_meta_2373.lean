import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by simp
lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · change l₁.all id = true → l₂.all id = true
    simp only [List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · change l₁.any id = true → l₂.any id = true
    simp only [List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩
lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj
def rows : List ℕ := [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]
def pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def neg : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def bits (r : ℕ) (i : Fin 10) := r.testBit i.val
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
def below (a b : Fin 10 → Bool) : Bool := (List.finRange 10).all fun i => !(a i) || b i
lemma below_elim {a b} (h : below a b = true) {i : Fin 10} (hi : a i = true) : b i = true := by
  have hh := List.all_eq_true.mp h i (by simp)
  simpa [hi] using hh
set_option maxRecDepth 20000 in
lemma endpoints : ∀ r : Fin 1024,
    (if edge (bits r) then pos.any (fun q => below (bits q) (bits r))
     else neg.any (fun q => below (bits r) (bits q))) = true := by decide +kernel
lemma liftRows (f : (Fin 10 → Bool) → Bool)
    (hm : ∀ a b : Fin 10 → Bool, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hr : ∀ q ∈ rows, f (bits q) = decide (q ∈ pos)) : ∀ x, f x = edge x := by
  intro x
  let w := BitVec.ofBoolListLE (List.ofFn x)
  have hw : w.toNat < 1024 := by
    have h := w.isLt
    simpa [w] using h
  let r : Fin 1024 := ⟨w.toNat, hw⟩
  have eqx : bits r = x := by
    funext i
    change w.getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have coverage := endpoints r
  rw [eqx] at coverage
  have hpRows : ∀ q ∈ pos, q ∈ rows := by decide +kernel
  have hnRows : ∀ q ∈ neg, q ∈ rows ∧ q ∉ pos := by decide +kernel
  cases he : edge x with
  | false =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    have hn := hnRows q hq
    have hval := hr q hn.1
    rw [decide_eq_false hn.2] at hval
    cases hf : f x with
    | false => rfl
    | true =>
      have := hm x (bits q) (fun _ hi => below_elim hle hi) hf
      rw [hval] at this
      contradiction
  | true =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    exact hm (bits q) x (fun _ hi => below_elim hle hi) (by simpa [hq] using hr q (hpRows q hq))
lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length=y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  exact wiresFrom_mono C.gates (fun g hg => by simpa using (hm g hg).1) x y len hle C.output
lemma apply_boundary (C : Circuit) (hm : Monotone2 C)
    (hr : ∀ r ∈ rows, C.eval (List.ofFn (bits r)) = decide (r ∈ pos)) :
    ∀ x, C.eval (List.ofFn x) = edge x := by
  apply liftRows _ _ hr
  intro a b hab
  apply eval_mono C hm _ _ (by simp)
  intro i hi
  by_cases hl : i < 10
  · have ha : i < (List.ofFn a).length := by simpa only [List.length_ofFn] using hl
    have hb : i < (List.ofFn b).length := by simpa only [List.length_ofFn] using hl
    rw [List.getD_eq_getElem _ _ ha, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hb, List.getElem_ofFn]
    exact hab _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma boundary_size : rows.length = 30 ∧ pos.length = 15 ∧ neg.length = 15 := by
  decide +kernel

lemma boundary_values : ∀ r ∈ rows, edge (bits r) = decide (r ∈ pos) := by
  decide +kernel

lemma circuit_boundary_iff (C : Circuit) (hm : Monotone2 C) :
    (∀ r ∈ rows, C.eval (List.ofFn (bits r)) = decide (r ∈ pos)) ↔
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x := by
  constructor
  · exact apply_boundary C hm
  · intro h r hr
    exact (h (bits r)).trans (boundary_values r hr)

namespace Causal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
def clip (n s i : ℕ) : ℕ := if i < n then i else s
def clipGate (n s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (clip n s)⟩
def normalize (n s : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => clipGate n s g :: normalize (n + 1) s gs
def circuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨normalize n (n + C.size) C.gates, C.output⟩
lemma run_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hlen]⟩
    change run gs (w ++ [_]) = _
    rw [ht]
    simp
lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := run_prefix gs w
  simp [ht, hlen]
lemma run_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]
lemma normalize_length (n s : ℕ) (gs : List Gate) :
    (normalize n s gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [normalize, ih]
lemma clip_read (s : ℕ) (w : List Bool) (h : w.length ≤ s) (i : ℕ) :
    w.getD (clip w.length s i) false = w.getD i false := by
  by_cases hi : i < w.length
  · simp only [clip, ite_eq_left hi]
  · simp only [clip, ite_eq_right hi]
    rw [List.getD_eq_default _ _ h, List.getD_eq_default _ _ (by omega)]
lemma clipGate_value (s : ℕ) (w : List Bool) (h : w.length ≤ s) (g : Gate) :
    (clipGate w.length s g).op.eval
      ((clipGate w.length s g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [clipGate, List.map_map, Function.comp_def, clip_read s w h]
lemma normalize_run (s : ℕ) (gs : List Gate) (w : List Bool)
    (h : w.length + gs.length ≤ s) :
    run (normalize w.length s gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hv := clipGate_value s w (by omega) g
    change run (normalize (w.length + 1) s gs)
      (w ++ [(clipGate w.length s g).op.eval
        ((clipGate w.length s g).inputs.map fun i => w.getD i false)]) =
      run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    rw [hv]
    simpa using ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at h; omega)
lemma circuit_size (n : ℕ) (C : Circuit) : (circuit n C).size = C.size := by
  exact normalize_length n (n + C.size) C.gates
lemma circuit_wires (n : ℕ) (C : Circuit) (w : List Bool) (hw : w.length = n) :
    (circuit n C).wires w = C.wires w := by
  change run (normalize n (n + C.size) C.gates) w = run C.gates w
  rw [← hw]
  exact normalize_run _ _ _ (by rfl)
lemma circuit_eval (n : ℕ) (C : Circuit) (w : List Bool) (hw : w.length = n) :
    (circuit n C).eval w = C.eval w := by
  change ((circuit n C).wires w).getD C.output false = _
  rw [circuit_wires n C w hw]
  rfl
lemma normalize_fanIn (n s : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ normalize n s gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [normalize]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ht
    · simpa only [clipGate, List.length_map] using h g List.mem_cons_self
    · exact ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) a ht
lemma circuit_fanIn (n : ℕ) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (circuit n C) := by
  exact normalize_fanIn n (n + C.size) C.gates hC
lemma normalized_gate_value (s : ℕ) (gs : List Gate) (w : List Bool)
    (h : w.length + gs.length ≤ s) (q : ℕ) (g : Gate)
    (hg : (normalize w.length s gs)[q]? = some g) :
    (run (normalize w.length s gs) w).getD (w.length + q) false =
      g.op.eval (g.inputs.map fun i => (run (normalize w.length s gs) w).getD i false) := by
  induction gs generalizing w q with
  | nil => simp [normalize] at hg
  | cons a gs ih =>
    let a' := clipGate w.length s a
    let w' := w ++ [a'.op.eval (a'.inputs.map fun i => w.getD i false)]
    have hw' : w'.length = w.length + 1 := by simp [w']
    have hr : run (normalize w.length s (a :: gs)) w =
        run (normalize w'.length s gs) w' := by rw [hw']; rfl
    cases q with
    | zero =>
      have hga : g = a' := by simpa [normalize, a'] using hg.symm
      subst g
      rw [hr]
      have hold (i : ℕ) (hi : i < w.length) :
          (run (normalize w'.length s gs) w').getD i false = w.getD i false := by
        rw [run_getD _ _ _ (by omega), List.getD_append _ _ _ _ hi]
      have hs : (run (normalize w'.length s gs) w').getD s false = false := by
        apply List.getD_eq_default
        rw [run_length, normalize_length, hw']
        simp only [List.length_cons] at h
        omega
      have hread (i : ℕ) :
          (run (normalize w'.length s gs) w').getD (clip w.length s i) false =
            w.getD i false := by
        by_cases hi : i < w.length
        · simpa [clip, hi] using hold i hi
        · simp only [clip, ite_eq_right hi, hs]
          rw [List.getD_eq_default _ _ (by omega)]
      have hhead : (run (normalize w'.length s gs) w').getD w.length false =
          a'.op.eval (a'.inputs.map fun i => w.getD i false) := by
        rw [run_getD _ _ _ (by omega)]
        simp [w']
      simp only [Nat.add_zero]
      rw [hhead]
      change (clipGate w.length s a).op.eval
        ((clipGate w.length s a).inputs.map fun i => w.getD i false) = _
      rw [clipGate_value s w (by omega)]
      simp only [a', clipGate, List.map_map, Function.comp_def, hread]
    | succ q =>
      rw [hr]
      have hgt : (normalize w'.length s gs)[q]? = some g := by
        simpa [normalize, hw'] using hg
      have he := ih w' (by
        rw [hw']; simp only [List.length_cons] at h; omega) q hgt
      simpa only [hw', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
lemma circuit_gate_values (n : ℕ) (C : Circuit) (w : List Bool) (hw : w.length = n)
    (q : ℕ) (g : Gate) (hg : (circuit n C).gates[q]? = some g) :
    ((circuit n C).wires w).getD (n + q) false =
      g.op.eval (g.inputs.map fun i => ((circuit n C).wires w).getD i false) := by
  subst n
  exact normalized_gate_value (w.length + C.size) C.gates w (by rfl) q g hg
def effectiveInputs (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs
def readerCount (v : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if v ∈ effectiveInputs g then 1 else 0) + readerCount v gs
lemma effectiveInputs_clipGate (n s : ℕ) (g : Gate) :
    effectiveInputs (clipGate n s g) = (effectiveInputs g).map (clip n s) := by
  cases g with
  | mk op inputs => cases op <;> cases inputs <;> rfl
lemma clip_eq_raw (n s v i : ℕ) (hv : v < n) (hns : n ≤ s) :
    clip n s i = v ↔ i = v := by
  by_cases hi : i < n
  · simp only [clip, ite_eq_left hi]
  · simp only [clip, ite_eq_right hi]
    constructor <;> intro he <;> omega
lemma raw_mem_clipped (n s v : ℕ) (ins : List ℕ) (hv : v < n) (hns : n ≤ s) :
    v ∈ ins.map (clip n s) ↔ v ∈ ins := by
  simp only [List.mem_map, clip_eq_raw n s v _ hv hns]
  simp
lemma raw_reader_clipGate (n s v : ℕ) (g : Gate) (hv : v < n) (hns : n ≤ s) :
    v ∈ effectiveInputs (clipGate n s g) ↔ v ∈ effectiveInputs g := by
  rw [effectiveInputs_clipGate]
  exact raw_mem_clipped n s v _ hv hns
lemma normalize_readerCount (n s v : ℕ) (gs : List Gate)
    (hv : v < n) (hns : n + gs.length ≤ s) :
    readerCount v (normalize n s gs) = readerCount v gs := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    simp only [normalize, readerCount]
    simp only [raw_reader_clipGate n s v g hv (by omega)]
    rw [ih (n + 1) (by omega) (by simp only [List.length_cons] at hns; omega)]
lemma circuit_readerCount (n v : ℕ) (C : Circuit) (hv : v < n) :
    readerCount v (circuit n C).gates = readerCount v C.gates := by
  exact normalize_readerCount n (n + C.size) v C.gates hv (by rfl)
lemma circuit_gate_values_ofFn (n : ℕ) (C : Circuit) (q : ℕ) (g : Gate)
    (hg : (circuit n C).gates[q]? = some g) (x : Fin n → Bool) :
    ((circuit n C).wires (List.ofFn x)).getD (n + q) false =
      g.op.eval (g.inputs.map fun i => ((circuit n C).wires (List.ofFn x)).getD i false) := by
  exact circuit_gate_values n C (List.ofFn x) (by simp) q g hg
lemma circuit_gate_values_original (n : ℕ) (C : Circuit) (q : ℕ) (g : Gate)
    (hg : (circuit n C).gates[q]? = some g) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + q) false =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have h := circuit_gate_values_ofFn n C q g hg x
  rw [circuit_wires n C (List.ofFn x) (by simp)] at h
  exact h
lemma normalize_ops (n s : ℕ) (gs : List Gate) :
    (normalize n s gs).map Gate.op = gs.map Gate.op := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [normalize, clipGate, ih]
lemma normalize_inputs (n s : ℕ) (gs : List Gate) (q : ℕ) (g : Gate)
    (hg : (normalize n s gs)[q]? = some g) :
    ∀ i ∈ g.inputs, i < n + q ∨ i = s := by
  induction gs generalizing n q with
  | nil => simp [normalize] at hg
  | cons a gs ih =>
    cases q with
    | zero =>
      have hga : g = clipGate n s a := by simpa [normalize] using hg.symm
      subst g
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      by_cases hji : j < n
      · exact Or.inl (by simp [clip, hji])
      · exact Or.inr (by simp [clip, hji])
    | succ q =>
      have hgt : (normalize (n + 1) s gs)[q]? = some g := by simpa [normalize] using hg
      intro i hi
      have hr := ih (n + 1) q hgt i hi
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
lemma circuit_inputs (n : ℕ) (C : Circuit) (q : ℕ) (g : Gate)
    (hg : (circuit n C).gates[q]? = some g) :
    ∀ i ∈ g.inputs, i < n + q ∨ i = n + C.size := by
  exact normalize_inputs n (n + C.size) C.gates q g hg
lemma normalize_notCount (n s : ℕ) (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨normalize n s gs, 0⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  classical
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    simp only [PEqualNP.NotBracket.notCount] at ih ⊢
    by_cases h : g.op = GateOp.not <;> simp [normalize, clipGate, h, ih]
lemma circuit_notCount (n : ℕ) (C : Circuit) :
    PEqualNP.NotBracket.notCount (circuit n C) = PEqualNP.NotBracket.notCount C := by
  exact normalize_notCount n (n + C.size) C.gates
lemma normalize_monotone (n s : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ normalize n s gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [normalize]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ht
    · simpa only [clipGate, List.length_map] using h g List.mem_cons_self
    · exact ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) a ht
lemma circuit_monotone2 (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (circuit n C) := by
  exact normalize_monotone n (n + C.size) C.gates hC

end Causal

end PEqualNP.Outside.L_meta_2373_aux
