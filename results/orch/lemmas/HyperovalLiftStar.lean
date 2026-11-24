import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.HyperovalLift

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def renameWire {n m : ℕ} (ρ : Fin n → Fin m) (r : ℕ) : ℕ :=
  if h : r < n then (ρ ⟨r, h⟩).val else m + (r - n)

def renameGate {n m : ℕ} (ρ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire ρ)⟩

def renameCircuit {n m : ℕ} (ρ : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate ρ), renameWire ρ C.output⟩

lemma renameWire_lt {n m : ℕ} (ρ : Fin n → Fin m) (r k : ℕ) :
    renameWire ρ r < m + k ↔ r < n + k := by
  unfold renameWire
  split_ifs with h
  · have hm := (ρ ⟨r, h⟩).isLt
    omega
  · omega

lemma renameWire_eq {n m : ℕ} (ρ : Fin n → Fin m) (r k : ℕ) :
    renameWire ρ r = m + k ↔ r = n + k := by
  unfold renameWire
  split_ifs with h
  · have hm := (ρ ⟨r, h⟩).isLt
    omega
  · omega

lemma append_read {n m k : ℕ} (ρ : Fin n → Fin m) (u v : List Bool)
    (hu : u.length = n + k) (hv : v.length = m + k)
    (hread : ∀ r, v.getD (renameWire ρ r) false = u.getD r false) (b : Bool) :
    ∀ r, (v ++ [b]).getD (renameWire ρ r) false = (u ++ [b]).getD r false := by
  intro r
  by_cases hr : r < n + k
  · rw [List.getD_append _ _ _ _ (by rw [hv]; exact (renameWire_lt ρ r k).mpr hr),
      List.getD_append _ _ _ _ (by omega)]
    exact hread r
  · by_cases he : r = n + k
    · have hre : renameWire ρ r = m + k := (renameWire_eq ρ r k).mpr he
      rw [hre, ← hv, he, ← hu]
      simp
    · rw [List.getD_eq_default, List.getD_eq_default]
      · simp; omega
      · have hlt := renameWire_lt ρ r k
        have heq := renameWire_eq ρ r k
        simp; omega

lemma run_rename {n m : ℕ} (ρ : Fin n → Fin m) (gs : List Gate) :
    ∀ (k : ℕ) (u v : List Bool), u.length = n + k → v.length = m + k →
      (∀ r, v.getD (renameWire ρ r) false = u.getD r false) →
      ∀ r, (run (gs.map (renameGate ρ)) v).getD (renameWire ρ r) false =
        (run gs u).getD r false := by
  induction gs with
  | nil =>
    intro k u v hu hv hread r
    exact hread r
  | cons g gs ih =>
    intro k u v hu hv hread r
    let b := g.op.eval (g.inputs.map fun i => u.getD i false)
    have hb : (renameGate ρ g).op.eval
        ((renameGate ρ g).inputs.map fun i => v.getD i false) = b := by
      simp only [renameGate, List.map_map, Function.comp_def, hread]
      rfl
    change (run (gs.map (renameGate ρ))
      (v ++ [(renameGate ρ g).op.eval
        ((renameGate ρ g).inputs.map fun i => v.getD i false)])).getD
          (renameWire ρ r) false =
      (run gs (u ++ [b])).getD r false
    rw [hb]
    exact ih (k + 1) (u ++ [b]) (v ++ [b]) (by simp [hu]; omega)
      (by simp [hv]; omega) (append_read ρ u v hu hv hread b) r

lemma initial_read {n m : ℕ} (ρ : Fin n → Fin m) (x : Fin m → Bool) (r : ℕ) :
    (List.ofFn x).getD (renameWire ρ r) false =
      (List.ofFn (fun i => x (ρ i))).getD r false := by
  by_cases hr : r < n
  · have hmap : renameWire ρ r = (ρ ⟨r, hr⟩).val := by simp [renameWire, hr]
    rw [hmap, List.getD_eq_getElem _ _ (by simp),
      List.getD_eq_getElem _ _ (by simpa using hr)]
    simp
  · have hm : m ≤ renameWire ρ r := by simp [renameWire, hr]
    rw [List.getD_eq_default _ _ (by simpa using hm),
      List.getD_eq_default _ _ (by simp; omega)]

lemma renameCircuit_eval {n m : ℕ} (ρ : Fin n → Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (renameCircuit ρ C).eval (List.ofFn x) =
      C.eval (List.ofFn (fun i => x (ρ i))) := by
  exact run_rename ρ C.gates 0 (List.ofFn (fun i => x (ρ i))) (List.ofFn x)
    (by simp) (by simp) (initial_read ρ x) C.output

lemma renameCircuit_size {n m : ℕ} (ρ : Fin n → Fin m) (C : Circuit) :
    (renameCircuit ρ C).size = C.size := by
  simp [renameCircuit, Circuit.size]

lemma renameCircuit_monotone {n m : ℕ} (ρ : Fin n → Fin m) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (renameCircuit ρ C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using hC a ha

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma run_old_read (gs : List Gate) (x : List Bool) (r : ℕ) (hr : r < x.length) :
    (run gs x).getD r false = x.getD r false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD r false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hr]

lemma circuit_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  change (run C.gates (List.ofFn x)).getD i false = _
  rw [run_old_read _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma output_lt_of_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = true) : C.output < n + C.size := by
  by_contra! h
  change (run C.gates (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using h)] at hx
  contradiction

def appendGate (n : ℕ) (C : Circuit) (op : GateOp) (inputs : List ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, inputs⟩], n + C.size⟩

lemma appendGate_size (n : ℕ) (C : Circuit) (op : GateOp) (inputs : List ℕ) :
    (appendGate n C op inputs).size = C.size + 1 := by
  simp [appendGate, Circuit.size]

lemma appendGate_wires (n : ℕ) (C : Circuit) (op : GateOp) (inputs : List ℕ)
    (x : List Bool) :
    (appendGate n C op inputs).wires x =
      C.wires x ++ [op.eval (inputs.map fun i => (C.wires x).getD i false)] := by
  simp [appendGate, Circuit.wires, List.foldl_append]

lemma appendGate_eval {n : ℕ} (C : Circuit) (op : GateOp) (inputs : List ℕ)
    (x : Fin n → Bool) :
    (appendGate n C op inputs).eval (List.ofFn x) =
      op.eval (inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hl : (C.wires (List.ofFn x)).length = n + C.size := by
    exact (run_length C.gates (List.ofFn x)).trans (by simp [Circuit.size])
  change ((appendGate n C op inputs).wires (List.ofFn x)).getD (n + C.size) false = _
  rw [appendGate_wires, ← hl]
  simp

lemma appendGate_old_wire {n : ℕ} (C : Circuit) (op : GateOp) (inputs : List ℕ)
    (x : Fin n → Bool) (r : ℕ) (hr : r < n + C.size) :
    ((appendGate n C op inputs).wires (List.ofFn x)).getD r false =
      (C.wires (List.ofFn x)).getD r false := by
  rw [appendGate_wires, List.getD_append]
  change r < (run C.gates (List.ofFn x)).length
  simpa [run_length, Circuit.size] using hr

lemma appendGate_monotone (n : ℕ) (C : Circuit) (op : GateOp) (inputs : List ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 (appendGate n C op inputs) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · have hg : g = ⟨op, inputs⟩ := List.mem_singleton.mp hg
    subst g
    exact ⟨by simpa using hop, hlen⟩

def appendStar {n : ℕ} (C : Circuit) (p : Fin n) (a : Fin 5 → Fin n) : Circuit :=
  let g1 := appendGate n C GateOp.or [a 0, a 1]
  let g2 := appendGate n g1 GateOp.or [g1.output, a 2]
  let g3 := appendGate n g2 GateOp.or [g2.output, a 3]
  let g4 := appendGate n g3 GateOp.or [g3.output, a 4]
  let g5 := appendGate n g4 GateOp.and [p, g4.output]
  appendGate n g5 GateOp.or [C.output, g5.output]

lemma appendStar_size {n : ℕ} (C : Circuit) (p : Fin n) (a : Fin 5 → Fin n) :
    (appendStar C p a).size = C.size + 6 := by
  simp [appendStar, appendGate_size]

lemma appendStar_output_lt {n : ℕ} (C : Circuit) (p : Fin n) (a : Fin 5 → Fin n) :
    (appendStar C p a).output < n + (appendStar C p a).size := by
  simp only [appendStar, appendGate, Circuit.size, List.length_append, List.length_cons,
    List.length_nil]
  omega

lemma appendStar_monotone {n : ℕ} (C : Circuit) (p : Fin n) (a : Fin 5 → Fin n)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (appendStar C p a) := by
  unfold appendStar
  apply appendGate_monotone
  · apply appendGate_monotone
    · apply appendGate_monotone
      · apply appendGate_monotone
        · apply appendGate_monotone
          · exact appendGate_monotone n C GateOp.or [a 0, a 1] hC (Or.inr rfl) (by simp)
          · exact Or.inr rfl
          · simp
        · exact Or.inr rfl
        · simp
      · exact Or.inr rfl
      · simp
    · exact Or.inl rfl
    · simp
  · exact Or.inr rfl
  · simp

lemma appendStar_eval {n : ℕ} (C : Circuit) (p : Fin n) (a : Fin 5 → Fin n)
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (appendStar C p a).eval (List.ofFn x) = (C.eval (List.ofFn x) ||
      (x p && ((((x (a 0) || x (a 1)) || x (a 2)) || x (a 3)) || x (a 4)))) := by
  let g1 := appendGate n C GateOp.or [a 0, a 1]
  let g2 := appendGate n g1 GateOp.or [g1.output, a 2]
  let g3 := appendGate n g2 GateOp.or [g2.output, a 3]
  let g4 := appendGate n g3 GateOp.or [g3.output, a 4]
  let g5 := appendGate n g4 GateOp.and [p, g4.output]
  have h1 : g1.eval (List.ofFn x) = (x (a 0) || x (a 1)) := by
    rw [appendGate_eval]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, circuit_input]
  have h2 : g2.eval (List.ofFn x) = (g1.eval (List.ofFn x) || x (a 2)) := by
    rw [appendGate_eval]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, circuit_input, Circuit.eval]
  have h3 : g3.eval (List.ofFn x) = (g2.eval (List.ofFn x) || x (a 3)) := by
    rw [appendGate_eval]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, circuit_input, Circuit.eval]
  have h4 : g4.eval (List.ofFn x) = (g3.eval (List.ofFn x) || x (a 4)) := by
    rw [appendGate_eval]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, circuit_input, Circuit.eval]
  have h5 : g5.eval (List.ofFn x) = (x p && g4.eval (List.ofFn x)) := by
    rw [appendGate_eval]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, circuit_input, Circuit.eval]
  have old : (g5.wires (List.ofFn x)).getD C.output false = C.eval (List.ofFn x) := by
    rw [appendGate_old_wire g4 GateOp.and [p, g4.output] x C.output (by
      simp only [g4, g3, g2, g1, appendGate_size]; omega)]
    rw [appendGate_old_wire g3 GateOp.or [g3.output, a 4] x C.output (by
      simp only [g3, g2, g1, appendGate_size]; omega)]
    rw [appendGate_old_wire g2 GateOp.or [g2.output, a 3] x C.output (by
      simp only [g2, g1, appendGate_size]; omega)]
    rw [appendGate_old_wire g1 GateOp.or [g1.output, a 2] x C.output (by
      simp only [g1, appendGate_size]; omega)]
    exact appendGate_old_wire C GateOp.or [a 0, a 1] x C.output hout
  change (appendGate n g5 GateOp.or [C.output, g5.output]).eval (List.ofFn x) = _
  rw [appendGate_eval]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, old]
  change (C.eval (List.ofFn x) || g5.eval (List.ofFn x)) = _
  rw [h5, h4, h3, h2, h1]

end PEqualNP.Outside.L_meta_1477.HyperovalLift
