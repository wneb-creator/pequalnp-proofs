import GeneralReaderStandalone

namespace PEqualNP.Outside.L_meta_1884.EightExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GeneralReaderBound

def eight (x : Fin 8 → Bool) : Bool :=
  x 0&&x 1||x 0&&x 4||x 1&&x 5||x 2&&x 7||x 3&&x 5||
  x 5&&x 7||x 7&&x 4||x 4&&x 6||x 6&&x 3

def pins : Fin 8 → Fin 9 := ![4, 0, 6, 7, 3, 5, 2, 8]

def wire (i : Nat) : Nat := if h : i < 8 then (pins ⟨i,h⟩).val else i+1

def remap (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩

lemma wire_lt {i n : Nat} (hn : 8 ≤ n) (hi : i < n) : wire i < n+1 := by
  unfold wire
  split_ifs with h
  · have hp := (pins ⟨i,h⟩).isLt
    omega
  · omega

lemma remap_run (gs : List Gate) (w z : List Bool)
    (hw : 8 ≤ w.length) (hz : z.length = w.length+1)
    (eq : ∀ i, z.getD (wire i) false = w.getD i false) :
    ∀ i, ((gs.map remap).foldl ws z).getD (wire i) false =
      (gs.foldl ws w).getD i false := by
  induction gs generalizing w z with
  | nil => exact eq
  | cons g gs ih =>
    have gateEq : (remap g).op.eval ((remap g).inputs.map (fun i => z.getD i false)) =
        g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
      simp only [remap, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => eq i)
    apply ih (ws w g) (ws z (remap g))
    · simp [ws]; omega
    · simp [ws, hz]
    · intro i
      rcases lt_trichotomy i w.length with hi | rfl | hi
      · rw [ws, ws, gl _ _ _ _ (hz ▸ wire_lt hw hi), gl _ _ _ _ hi]
        exact eq i
      · have wi : wire w.length = z.length := by simp [wire, show ¬w.length < 8 by omega, hz]
        rw [ws, ws, wi, ge, ge]
        exact gateEq
      · have wi : z.length < wire i := by
          simp [wire, show ¬i < 8 by omega]
          omega
        rw [ws, ws, gg _ _ _ _ wi, gg _ _ _ _ hi]

lemma initial_rows (y : Fin 9 → Bool) (i : Nat) :
    (List.ofFn y).getD (wire i) false = (List.ofFn (y ∘ pins)).getD i false := by
  by_cases hi : i < 8
  · interval_cases i <;> simp [wire, pins, List.getD_eq_getElem?_getD, Function.comp_def]
  · have hn : ¬ i+1 < 9 := by omega
    simp [wire, hi, hn, List.getD_eq_getElem?_getD]

def grow (C : Circuit) : Circuit :=
  let b := 9 + C.size
  ⟨C.gates.map remap ++
    [⟨.or,[0,6]⟩,⟨.or,[b,2]⟩,⟨.and,[1,b+1]⟩,⟨.or,[wire C.output,b+2]⟩],b+3⟩

lemma grow_size (C : Circuit) : (grow C).size = C.size+4 := by
  simp [grow, Circuit.size]

lemma grow_legal (C : Circuit) (legal : FanInTwo C) : FanInTwo (grow C) := by
  intro g hg
  simp only [grow, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨g,hg,rfl⟩ | rfl | rfl | rfl | rfl
  · simpa [remap] using legal g hg
  all_goals simp

lemma read_append (w : List Bool) (v : Bool) (i : Nat) :
    (w++[v]).getD i false = if i < w.length then w.getD i false
      else if i = w.length then v else false := by
  rcases lt_trichotomy i w.length with hi | rfl | hi
  · rw [if_pos hi, gl _ _ _ _ hi]
  · simp [ge]
  · rw [if_neg (by omega), if_neg (by omega), gg _ _ _ _ hi]

lemma four_gate_eval (w : List Bool) (o : Nat) (hw : 9 ≤ w.length) (ho : o < w.length) :
    ([⟨.or,[0,6]⟩,⟨.or,[w.length,2]⟩,⟨.and,[1,w.length+1]⟩,
      ⟨.or,[o,w.length+2]⟩].foldl ws w).getD (w.length+3) false =
      (w.getD o false || (w.getD 1 false &&
        (w.getD 0 false || w.getD 6 false || w.getD 2 false))) := by
  have h0 (k : Nat) : 0 < w.length+k := by omega
  have h1 (k : Nat) : 1 < w.length+k := by omega
  have h2 (k : Nat) : 2 < w.length+k := by omega
  have h6 (k : Nat) : 6 < w.length+k := by omega
  have hout (k : Nat) : o < w.length+k := by omega
  simp [List.foldl_cons, ws, GateOp.eval, read_append, h0, h1, h2, h6, hout,
    show 0 < w.length by omega, show 1 < w.length by omega,
    show 2 < w.length by omega, show 6 < w.length by omega, ho]

lemma edge_split : ∀ y : Fin 9 → Bool,
    (eight (y ∘ pins) || (y 1 && (y 0 || y 6 || y 2))) =
      GeneralReaderCertificate.edge y := by decide +kernel

lemma output_valid (C : Circuit)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = eight x) :
    C.output < 8+C.size := by
  by_contra! bad
  have h := correct (fun _ => true)
  have len : (C.wires (List.ofFn (fun _ : Fin 8 => true))).length = 8+C.size := by
    exact (wl C.gates _).trans (by simp [Circuit.size])
  rw [Circuit.eval, List.getD_eq_default _ _ (len ▸ bad)] at h
  change false = true at h
  contradiction

lemma grow_correct (C : Circuit)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = eight x) :
    ∀ y : Fin 9 → Bool, (grow C).eval (List.ofFn y) = GeneralReaderCertificate.edge y := by
  intro y
  let w := (C.gates.map remap).foldl ws (List.ofFn y)
  have len : w.length = 9+C.size := by
    simp [w, wl, Circuit.size]
  have old := remap_run C.gates (List.ofFn (y ∘ pins)) (List.ofFn y)
    (by simp) (by simp) (initial_rows y) C.output
  have oldEq : w.getD (wire C.output) false = eight (y ∘ pins) := by
    exact old.trans (correct _)
  have hv : wire C.output < w.length := by
    rw [len]
    have h := wire_lt (show 8 ≤ 8+C.size by omega) (output_valid C correct)
    omega
  simp only [Circuit.eval, Circuit.wires, grow, List.foldl_append]
  change ([⟨.or,[0,6]⟩,⟨.or,[9+C.size,2]⟩,⟨.and,[1,9+C.size+1]⟩,
    ⟨.or,[wire C.output,9+C.size+2]⟩].foldl ws w).getD (9+C.size+3) false = _
  rw [← len, four_gate_eval w _ (by omega) hv, oldEq]
  have raw (i : Nat) (hi : i < 9) : w.getD i false = (List.ofFn y).getD i false := by
    have all : ∀ gs : List Gate, ∀ z : List Bool, i < z.length →
        (gs.foldl ws z).getD i false = z.getD i false := by
      intro gs
      induction gs with
      | nil => intro z hz; rfl
      | cons g gs ih =>
        intro z hz
        rw [List.foldl_cons, ih _ (by simp [ws]; omega), ws, gl _ _ _ _ hz]
    exact all _ _ (by simp; exact hi)
  rw [raw 0 (by decide), raw 1 (by decide), raw 2 (by decide), raw 6 (by decide)]
  simpa [List.getD_eq_getElem?_getD] using edge_split y

theorem eight_floor (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = eight x) : 12 ≤ C.size := by
  have lower := NineGeneralFloor.nine_circuit_floor (grow C) (grow_legal C legal)
    (grow_correct C correct)
  rw [grow_size] at lower
  omega

end PEqualNP.Outside.L_meta_1884.EightExtension
