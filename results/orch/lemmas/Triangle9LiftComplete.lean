import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1477.Triangle9

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def planePairs : List (Fin 42 × Fin 42) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def localPairs : List (Fin 27 × Fin 27) :=
  [(0, 9), (1, 9), (4, 9), (1, 10), (2, 10), (5, 10), (2, 11), (3, 11), (3, 12), (4, 12), (8, 12), (4, 13), (5, 13), (0, 14), (5, 14), (8, 14), (1, 15), (6, 15), (0, 16), (2, 16), (1, 17), (3, 17), (7, 17), (2, 18), (4, 18), (6, 18), (3, 19), (5, 19), (6, 19), (4, 20), (7, 20), (5, 21), (7, 21), (6, 22), (8, 22), (0, 23), (6, 23), (7, 23), (1, 24), (8, 24), (2, 25), (7, 25), (8, 25), (0, 26), (3, 26)]

def inputMap : Fin 27 → Fin 42 :=
  ![0, 1, 2, 3, 4, 5, 10, 12, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 36, 38, 39, 40, 41]

def coreInput (x : Fin 42 → Bool) : Fin 27 → Bool :=
  fun i => x (inputMap i)

def remainingStars : List (Fin 42 × (Fin 5 → Fin 42)) :=
  [(6, ![23, 26, 27, 32, 34]),
   (7, ![24, 27, 28, 33, 35]),
   (8, ![25, 28, 29, 34, 36]),
   (9, ![26, 29, 30, 35, 37]),
   (11, ![28, 31, 32, 37, 39]),
   (13, ![30, 33, 34, 39, 41]),
   (14, ![21, 31, 34, 35, 40]),
   (15, ![22, 32, 35, 36, 41]),
   (16, ![21, 23, 33, 36, 37]),
   (17, ![22, 24, 34, 37, 38]),
   (18, ![23, 25, 35, 38, 39]),
   (20, ![25, 27, 37, 40, 41])]

def edgeValue {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  es.any (fun e => x e.1 && x e.2)

def starValue {n : ℕ} (s : Fin n × (Fin 5 → Fin n)) (x : Fin n → Bool) : Bool :=
  x s.1 && ((((x (s.2 0) || x (s.2 1)) || x (s.2 2)) || x (s.2 3)) || x (s.2 4))

def starsValue {n : ℕ} (s : List (Fin n × (Fin 5 → Fin n))) (x : Fin n → Bool) : Bool :=
  s.any (fun a => starValue a x)

lemma planePairs_map : planePairs.map (fun e => (e.1.val, e.2.val)) = planeEdges := by
  decide

lemma localPairs_length : localPairs.length = 45 := by decide

lemma localPairs_nodup : localPairs.Nodup := by decide

lemma remainingStars_length : remainingStars.length = 12 := by decide

lemma edgeValue_iff {n : ℕ} (es : List (Fin n × Fin n)) (x : Fin n → Bool) :
    edgeValue es x = true ↔ ∃ u v : Fin n, (u, v) ∈ es ∧ x u = true ∧ x v = true := by
  simp only [edgeValue, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    exact ⟨u, v, he, hu, hv⟩
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u, v), he, hu, hv⟩

lemma planeValue_iff (x : Fin 42 → Bool) :
    edgeValue planePairs x = true ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ planeEdges ∧ x u = true ∧ x v = true := by
  rw [edgeValue_iff]
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    refine ⟨u, v, ?_, hu, hv⟩
    rw [← planePairs_map]
    exact List.mem_map.mpr ⟨(u, v), he, rfl⟩
  · rintro ⟨u, v, he, hu, hv⟩
    rw [← planePairs_map] at he
    obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp he
    have hau : a = u := Fin.ext (congrArg Prod.fst heq)
    have hbv : b = v := Fin.ext (congrArg Prod.snd heq)
    subst a
    subst b
    exact ⟨u, v, hab, hu, hv⟩

lemma and_or_dist (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma plane_decomposition (x : Fin 42 → Bool) :
    edgeValue planePairs x =
      (edgeValue localPairs (coreInput x) || starsValue remainingStars x) := by
  simp [edgeValue, planePairs, localPairs, coreInput, inputMap, starsValue, remainingStars, starValue,
    and_or_dist]
  ac_rfl

end PEqualNP.Outside.L_meta_1477.Triangle9

namespace PEqualNP.Outside.L_meta_1477.Triangle9Lift

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

def fullLift (C : Circuit) : Circuit :=
  appendStars (renameCircuit Triangle9.inputMap C) Triangle9.remainingStars

lemma fullLift_size (C : Circuit) : (fullLift C).size = C.size + 72 := by
  rw [fullLift, appendStars_size, renameCircuit_size, Triangle9.remainingStars_length]

lemma fullLift_monotone (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (fullLift C) :=
  appendStars_monotone _ _ (renameCircuit_monotone Triangle9.inputMap C hC)

lemma renamed_output_lt (C : Circuit)
    (hfun : ∀ x : Fin 27 → Bool,
      C.eval (List.ofFn x) = Triangle9.edgeValue Triangle9.localPairs x) :
    (renameCircuit Triangle9.inputMap C).output <
      42 + (renameCircuit Triangle9.inputMap C).size := by
  apply output_lt_of_true (renameCircuit Triangle9.inputMap C) (fun _ => true)
  rw [renameCircuit_eval, hfun]
  decide

lemma fullLift_eval (C : Circuit)
    (hfun : ∀ x : Fin 27 → Bool,
      C.eval (List.ofFn x) = Triangle9.edgeValue Triangle9.localPairs x)
    (x : Fin 42 → Bool) :
    (fullLift C).eval (List.ofFn x) = Triangle9.edgeValue Triangle9.planePairs x := by
  rw [fullLift, appendStars_eval _ _ (renamed_output_lt C hfun), renameCircuit_eval, hfun]
  change (Triangle9.edgeValue Triangle9.localPairs (Triangle9.coreInput x) ||
    Triangle9.starsValue Triangle9.remainingStars x) = _
  exact (Triangle9.plane_decomposition x).symm

lemma local_short_circuit_gives_plane_short_circuit (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hsize : C.size ≤ 52)
    (hfun : ∀ x : Fin 27 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 27, (u, v) ∈ Triangle9.localPairs ∧ x u = true ∧ x v = true) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 124 ∧
      ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ Triangle9.planeEdges ∧
          x u = true ∧ x v = true := by
  have heq (x : Fin 27 → Bool) :
      C.eval (List.ofFn x) = Triangle9.edgeValue Triangle9.localPairs x := by
    apply Bool.eq_iff_iff.mpr
    exact (hfun x).trans (Triangle9.edgeValue_iff Triangle9.localPairs x).symm
  refine ⟨fullLift C, fullLift_monotone C hC, ?_, ?_⟩
  · rw [fullLift_size]
    omega
  · intro x
    rw [fullLift_eval C heq x]
    exact Triangle9.planeValue_iff x

end PEqualNP.Outside.L_meta_1477.Triangle9Lift
