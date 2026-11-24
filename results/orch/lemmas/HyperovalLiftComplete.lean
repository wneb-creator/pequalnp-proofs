import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.Hyperoval

def incidenceEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def pointMap : Fin 6 → Fin 42 := ![0, 1, 2, 3, 10, 19]

def lineMap : Fin 15 → Fin 42 :=
  ![21, 28, 41, 38, 26, 22, 29, 27, 39, 23, 30, 40, 31, 24, 36]

def pairEnds : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

lemma pointMap_injective : Function.Injective pointMap := by decide

lemma lineMap_injective : Function.Injective lineMap := by decide

lemma pairEnds_distinct (j : Fin 15) : (pairEnds j).1 ≠ (pairEnds j).2 := by
  fin_cases j <;> decide

lemma pairEnds_exhaust (i j : Fin 6) (hij : i < j) :
    ∃ k : Fin 15, pairEnds k = (i, j) := by
  revert j
  fin_cases i <;> decide

lemma incidence_iff (i : Fin 6) (j : Fin 15) :
    ((pointMap i).val, (lineMap j).val) ∈ incidenceEdges ↔
      i = (pairEnds j).1 ∨ i = (pairEnds j).2 := by
  fin_cases i <;> fin_cases j <;> decide

lemma incidence_no_extra_line (i : Fin 6) (j : Fin 42)
    (h : ((pointMap i).val, j.val) ∈ incidenceEdges) :
    ∃ k : Fin 15, lineMap k = j := by
  revert j
  fin_cases i <;> decide

def points : Finset (Fin 21) := {0, 1, 2, 3, 10, 19}

def secants : Finset (Fin 21) := {0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 15, 17, 18, 19, 20}

def incidentPoints (j : Fin 21) : Finset (Fin 21) :=
  points.filter (fun i => (i.val, j.val + 21) ∈ incidenceEdges)

lemma points_card : points.card = 6 := by decide

lemma secants_card : secants.card = 15 := by decide

lemma incidentPoints_card (j : Fin 21) :
    (incidentPoints j).card = if j ∈ secants then 2 else 0 := by
  fin_cases j <;> decide

end PEqualNP.Outside.L_meta_1477.Hyperoval

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

def starValue {n : ℕ} (s : Fin n × (Fin 5 → Fin n)) (x : Fin n → Bool) : Bool :=
  x s.1 && ((((x (s.2 0) || x (s.2 1)) || x (s.2 2)) || x (s.2 3)) || x (s.2 4))

def starsValue {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (x : Fin n → Bool) : Bool :=
  s.any (fun a => starValue a x)

def appendStars {n : ℕ} (C : Circuit) : List (Fin n × (Fin 5 → Fin n)) → Circuit
  | [] => C
  | s :: rest => appendStars (appendStar C s.1 s.2) rest

lemma appendStars_size {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (C : Circuit) :
    (appendStars C s).size = C.size + 6 * s.length := by
  induction s generalizing C with
  | nil => simp [appendStars]
  | cons s rest ih =>
    rw [appendStars, ih, appendStar_size]
    simp only [List.length_cons]
    omega

lemma appendStars_monotone {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (appendStars C s) := by
  induction s generalizing C with
  | nil => exact hC
  | cons s rest ih => exact ih _ (appendStar_monotone C s.1 s.2 hC)

lemma appendStars_output_lt {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (C : Circuit)
    (hout : C.output < n + C.size) :
    (appendStars C s).output < n + (appendStars C s).size := by
  induction s generalizing C with
  | nil => exact hout
  | cons s rest ih => exact ih _ (appendStar_output_lt C s.1 s.2)

lemma appendStars_eval {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (C : Circuit)
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (appendStars C s).eval (List.ofFn x) = (C.eval (List.ofFn x) || starsValue s x) := by
  induction s generalizing C with
  | nil => simp [appendStars, starsValue]
  | cons s rest ih =>
    rw [appendStars, ih _ (appendStar_output_lt C s.1 s.2), appendStar_eval C s.1 s.2 hout]
    simp only [starsValue, List.any_cons, starValue, Bool.or_assoc]

lemma five_or_iff (f : Fin 5 → Bool) :
    ((((f 0 || f 1) || f 2) || f 3) || f 4) = true ↔ ∃ i : Fin 5, f i = true := by
  simp only [Bool.or_eq_true]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all

lemma starValue_iff {n : ℕ} (s : Fin n × (Fin 5 → Fin n)) (x : Fin n → Bool) :
    starValue s x = true ↔ x s.1 = true ∧ ∃ i : Fin 5, x (s.2 i) = true := by
  simp only [starValue, Bool.and_eq_true]
  exact and_congr_right fun _ => five_or_iff (fun i => x (s.2 i))


def inputMap : Fin 21 → Fin 42 := ![0, 1, 2, 3, 10, 19, 21, 28, 41, 38, 26, 22, 29, 27, 39, 23, 30, 40, 31, 24, 36]

def localPairs : List (Fin 21 × Fin 21) :=
  [(0, 6), (1, 6), (0, 7), (2, 7), (0, 8), (3, 8), (0, 9), (4, 9), (0, 10), (5, 10), (1, 11), (2, 11), (1, 12), (3, 12), (1, 13), (4, 13), (1, 14), (5, 14), (2, 15), (3, 15), (2, 16), (4, 16), (2, 17), (5, 17), (3, 18), (4, 18), (3, 19), (5, 19), (4, 20), (5, 20)]

def remainingStars : List (Fin 42 × (Fin 5 → Fin 42)) :=
  [
    (4, ![21, 24, 25, 30, 32]),
    (5, ![22, 25, 26, 31, 33]),
    (6, ![23, 26, 27, 32, 34]),
    (7, ![24, 27, 28, 33, 35]),
    (8, ![25, 28, 29, 34, 36]),
    (9, ![26, 29, 30, 35, 37]),
    (11, ![28, 31, 32, 37, 39]),
    (12, ![29, 32, 33, 38, 40]),
    (13, ![30, 33, 34, 39, 41]),
    (14, ![21, 31, 34, 35, 40]),
    (15, ![22, 32, 35, 36, 41]),
    (16, ![21, 23, 33, 36, 37]),
    (17, ![22, 24, 34, 37, 38]),
    (18, ![23, 25, 35, 38, 39]),
    (20, ![25, 27, 37, 40, 41])
  ]

def localValue (x : Fin 21 → Bool) : Bool :=
  localPairs.any (fun e => x e.1 && x e.2)

lemma remainingStars_length : remainingStars.length = 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma edge_decomposition (u v : Fin 42) :
    (u.val, v.val) ∈ PEqualNP.Outside.L_meta_1477.Hyperoval.incidenceEdges ↔
      (∃ e ∈ localPairs, inputMap e.1 = u ∧ inputMap e.2 = v) ∨
      (∃ s ∈ remainingStars, s.1 = u ∧ ∃ i : Fin 5, s.2 i = v) := by
  revert v
  fin_cases u <;> decide

lemma value_decomposition (x : Fin 42 → Bool) :
    (∃ u v : Fin 42,
      (u.val, v.val) ∈ PEqualNP.Outside.L_meta_1477.Hyperoval.incidenceEdges ∧
        x u = true ∧ x v = true) ↔
      localValue (fun i => x (inputMap i)) = true ∨ starsValue remainingStars x = true := by
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    rcases (edge_decomposition u v).mp he with ⟨e, helocal, rfl, rfl⟩ | ⟨s, hs, rfl, i, rfl⟩
    · exact Or.inl (List.any_eq_true.mpr ⟨e, helocal, by simp [hu, hv]⟩)
    · exact Or.inr (List.any_eq_true.mpr ⟨s, hs, (starValue_iff s x).mpr ⟨hu, i, hv⟩⟩)
  · intro h
    rcases h with h | h
    · obtain ⟨e, he, hx⟩ := List.any_eq_true.mp h
      have hx : x (inputMap e.1) = true ∧ x (inputMap e.2) = true := by simpa only [Bool.and_eq_true] using hx
      exact ⟨inputMap e.1, inputMap e.2,
        (edge_decomposition _ _).mpr (Or.inl ⟨e, he, rfl, rfl⟩), hx.1, hx.2⟩
    · obtain ⟨s, hs, hx⟩ := List.any_eq_true.mp h
      obtain ⟨hp, i, hi⟩ := (starValue_iff s x).mp hx
      exact ⟨s.1, s.2 i,
        (edge_decomposition _ _).mpr (Or.inr ⟨s, hs, rfl, i, rfl⟩), hp, hi⟩

def liftCircuit (C : Circuit) : Circuit :=
  appendStars (renameCircuit inputMap C) remainingStars

lemma liftCircuit_size (C : Circuit) : (liftCircuit C).size = C.size + 90 := by
  rw [liftCircuit, appendStars_size, renameCircuit_size, remainingStars_length]

lemma liftCircuit_monotone (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (liftCircuit C) :=
  appendStars_monotone remainingStars _ (renameCircuit_monotone inputMap C hC)

lemma localValue_all_true : localValue (fun _ => true) = true := by decide

lemma liftCircuit_correct (C : Circuit)
    (hC : ∀ x : Fin 21 → Bool, C.eval (List.ofFn x) = localValue x)
    (x : Fin 42 → Bool) :
    (liftCircuit C).eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42,
        (u.val, v.val) ∈ PEqualNP.Outside.L_meta_1477.Hyperoval.incidenceEdges ∧
          x u = true ∧ x v = true := by
  have hout : C.output < 21 + C.size :=
    output_lt_of_true C (fun _ : Fin 21 => true) ((hC _).trans localValue_all_true)
  have hrout : (renameCircuit inputMap C).output < 42 + (renameCircuit inputMap C).size := by
    rw [renameCircuit_size]
    exact (renameWire_lt inputMap C.output C.size).mpr hout
  rw [liftCircuit, appendStars_eval _ _ hrout, renameCircuit_eval, hC, Bool.or_eq_true]
  exact (value_decomposition x).symm

lemma local_short_circuit_gives_plane_short_circuit (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hsize : C.size ≤ 34)
    (hC : ∀ x : Fin 21 → Bool, C.eval (List.ofFn x) = localValue x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 124 ∧
      ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42,
          (u.val, v.val) ∈ PEqualNP.Outside.L_meta_1477.Hyperoval.incidenceEdges ∧
            x u = true ∧ x v = true := by
  refine ⟨liftCircuit C, liftCircuit_monotone C hmono, ?_, liftCircuit_correct C hC⟩
  rw [liftCircuit_size]
  omega

end PEqualNP.Outside.L_meta_1477.HyperovalLift
