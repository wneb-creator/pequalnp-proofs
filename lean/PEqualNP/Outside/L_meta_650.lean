import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def W (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

private lemma W_input (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
    W C (List.ofFn x) w = x ⟨w, hw⟩ := by
  unfold W
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) w (by simp [hw])]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp [hw]), Option.getD_some, List.getElem_ofFn]

private lemma W_gate (C : Circuit) (hrb : ReadsBack 26 C) (x : List Bool) (hx : x.length = 26)
    (k : ℕ) (hk : k < C.gates.length) :
    W C x (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map (W C x)) := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set w0 := (C.gates.take k).foldl stepWire x with hw0
  have hw0_len : w0.length = 26 + k := by
    simp [w0, foldl_stepWire_length, hx, List.length_take]; omega
  have hW : W C x (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map fun i => w0.getD i false) := by
    unfold W
    conv_lhs => rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_cons, ← hw0]
    rw [foldl_stepWire_getD_lt _ _ (26 + k) (by simp [stepWire, hw0_len])]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hW]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < 26 + k := hrb k hk i (by simp [gateAt, List.getD_eq_getElem?_getD, hk, hi])
  unfold W
  conv_rhs => rw [wires_eq_foldl, hsplit, List.foldl_append]
  exact (foldl_stepWire_getD_lt _ w0 i (by omega)).symm


def starCircuit : Circuit :=
  { gates := [
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [16, 22]⟩,
      ⟨GateOp.or, [26, 27]⟩,
      ⟨GateOp.and, [0, 28]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [21, 25]⟩,
      ⟨GateOp.or, [30, 31]⟩,
      ⟨GateOp.and, [1, 32]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [24, 25]⟩,
      ⟨GateOp.or, [34, 35]⟩,
      ⟨GateOp.and, [2, 36]⟩,
      ⟨GateOp.or, [13, 19]⟩,
      ⟨GateOp.or, [23, 24]⟩,
      ⟨GateOp.or, [38, 39]⟩,
      ⟨GateOp.and, [3, 40]⟩,
      ⟨GateOp.or, [18, 22]⟩,
      ⟨GateOp.or, [23, 25]⟩,
      ⟨GateOp.or, [42, 43]⟩,
      ⟨GateOp.and, [4, 44]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.or, [22, 24]⟩,
      ⟨GateOp.or, [46, 47]⟩,
      ⟨GateOp.and, [5, 48]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.or, [21, 23]⟩,
      ⟨GateOp.or, [50, 51]⟩,
      ⟨GateOp.and, [6, 52]⟩,
      ⟨GateOp.or, [15, 19]⟩,
      ⟨GateOp.or, [20, 22]⟩,
      ⟨GateOp.or, [54, 55]⟩,
      ⟨GateOp.and, [7, 56]⟩,
      ⟨GateOp.or, [14, 18]⟩,
      ⟨GateOp.or, [19, 21]⟩,
      ⟨GateOp.or, [58, 59]⟩,
      ⟨GateOp.and, [8, 60]⟩,
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.or, [62, 63]⟩,
      ⟨GateOp.and, [9, 64]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [19, 25]⟩,
      ⟨GateOp.or, [66, 67]⟩,
      ⟨GateOp.and, [10, 68]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [18, 24]⟩,
      ⟨GateOp.or, [70, 71]⟩,
      ⟨GateOp.and, [11, 72]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [17, 23]⟩,
      ⟨GateOp.or, [74, 75]⟩,
      ⟨GateOp.and, [12, 76]⟩,
      ⟨GateOp.or, [29, 33]⟩,
      ⟨GateOp.or, [78, 37]⟩,
      ⟨GateOp.or, [79, 41]⟩,
      ⟨GateOp.or, [80, 45]⟩,
      ⟨GateOp.or, [81, 49]⟩,
      ⟨GateOp.or, [82, 53]⟩,
      ⟨GateOp.or, [83, 57]⟩,
      ⟨GateOp.or, [84, 61]⟩,
      ⟨GateOp.or, [85, 65]⟩,
      ⟨GateOp.or, [86, 69]⟩,
      ⟨GateOp.or, [87, 73]⟩,
      ⟨GateOp.or, [88, 77]⟩
    ]
    output := 89 }

lemma star_size : starCircuit.size = 64 := by decide

lemma star_monotone : Monotone2 starCircuit := by
  simp [Monotone2, starCircuit]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma star_eval (x : Fin 26 → Bool) :
    starCircuit.eval (List.ofFn x) = (((((((((((((x 0 && ((x 13 || x 14) || (x 16 || x 22))) || (x 1 && ((x 13 || x 15) || (x 21 || x 25)))) || (x 2 && ((x 14 || x 20) || (x 24 || x 25)))) || (x 3 && ((x 13 || x 19) || (x 23 || x 24)))) || (x 4 && ((x 18 || x 22) || (x 23 || x 25)))) || (x 5 && ((x 17 || x 21) || (x 22 || x 24)))) || (x 6 && ((x 16 || x 20) || (x 21 || x 23)))) || (x 7 && ((x 15 || x 19) || (x 20 || x 22)))) || (x 8 && ((x 14 || x 18) || (x 19 || x 21)))) || (x 9 && ((x 13 || x 17) || (x 18 || x 20)))) || (x 10 && ((x 16 || x 17) || (x 19 || x 25)))) || (x 11 && ((x 15 || x 16) || (x 18 || x 24)))) || (x 12 && ((x 14 || x 15) || (x 17 || x 23)))) := by
  have back : ReadsBack 26 starCircuit := by decide
  have len : (List.ofFn x).length = 26 := by simp
  have h0 := W_gate starCircuit back (List.ofFn x) len 0 (by decide)
  change W starCircuit (List.ofFn x) 26 =
    GateOp.or.eval ([13, 14].map (W starCircuit (List.ofFn x))) at h0
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h0
  have h1 := W_gate starCircuit back (List.ofFn x) len 1 (by decide)
  change W starCircuit (List.ofFn x) 27 =
    GateOp.or.eval ([16, 22].map (W starCircuit (List.ofFn x))) at h1
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h1
  have h2 := W_gate starCircuit back (List.ofFn x) len 2 (by decide)
  change W starCircuit (List.ofFn x) 28 =
    GateOp.or.eval ([26, 27].map (W starCircuit (List.ofFn x))) at h2
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h2
  have h3 := W_gate starCircuit back (List.ofFn x) len 3 (by decide)
  change W starCircuit (List.ofFn x) 29 =
    GateOp.and.eval ([0, 28].map (W starCircuit (List.ofFn x))) at h3
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h3
  have h4 := W_gate starCircuit back (List.ofFn x) len 4 (by decide)
  change W starCircuit (List.ofFn x) 30 =
    GateOp.or.eval ([13, 15].map (W starCircuit (List.ofFn x))) at h4
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h4
  have h5 := W_gate starCircuit back (List.ofFn x) len 5 (by decide)
  change W starCircuit (List.ofFn x) 31 =
    GateOp.or.eval ([21, 25].map (W starCircuit (List.ofFn x))) at h5
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h5
  have h6 := W_gate starCircuit back (List.ofFn x) len 6 (by decide)
  change W starCircuit (List.ofFn x) 32 =
    GateOp.or.eval ([30, 31].map (W starCircuit (List.ofFn x))) at h6
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h6
  have h7 := W_gate starCircuit back (List.ofFn x) len 7 (by decide)
  change W starCircuit (List.ofFn x) 33 =
    GateOp.and.eval ([1, 32].map (W starCircuit (List.ofFn x))) at h7
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h7
  have h8 := W_gate starCircuit back (List.ofFn x) len 8 (by decide)
  change W starCircuit (List.ofFn x) 34 =
    GateOp.or.eval ([14, 20].map (W starCircuit (List.ofFn x))) at h8
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h8
  have h9 := W_gate starCircuit back (List.ofFn x) len 9 (by decide)
  change W starCircuit (List.ofFn x) 35 =
    GateOp.or.eval ([24, 25].map (W starCircuit (List.ofFn x))) at h9
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h9
  have h10 := W_gate starCircuit back (List.ofFn x) len 10 (by decide)
  change W starCircuit (List.ofFn x) 36 =
    GateOp.or.eval ([34, 35].map (W starCircuit (List.ofFn x))) at h10
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h10
  have h11 := W_gate starCircuit back (List.ofFn x) len 11 (by decide)
  change W starCircuit (List.ofFn x) 37 =
    GateOp.and.eval ([2, 36].map (W starCircuit (List.ofFn x))) at h11
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h11
  have h12 := W_gate starCircuit back (List.ofFn x) len 12 (by decide)
  change W starCircuit (List.ofFn x) 38 =
    GateOp.or.eval ([13, 19].map (W starCircuit (List.ofFn x))) at h12
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h12
  have h13 := W_gate starCircuit back (List.ofFn x) len 13 (by decide)
  change W starCircuit (List.ofFn x) 39 =
    GateOp.or.eval ([23, 24].map (W starCircuit (List.ofFn x))) at h13
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h13
  have h14 := W_gate starCircuit back (List.ofFn x) len 14 (by decide)
  change W starCircuit (List.ofFn x) 40 =
    GateOp.or.eval ([38, 39].map (W starCircuit (List.ofFn x))) at h14
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h14
  have h15 := W_gate starCircuit back (List.ofFn x) len 15 (by decide)
  change W starCircuit (List.ofFn x) 41 =
    GateOp.and.eval ([3, 40].map (W starCircuit (List.ofFn x))) at h15
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h15
  have h16 := W_gate starCircuit back (List.ofFn x) len 16 (by decide)
  change W starCircuit (List.ofFn x) 42 =
    GateOp.or.eval ([18, 22].map (W starCircuit (List.ofFn x))) at h16
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h16
  have h17 := W_gate starCircuit back (List.ofFn x) len 17 (by decide)
  change W starCircuit (List.ofFn x) 43 =
    GateOp.or.eval ([23, 25].map (W starCircuit (List.ofFn x))) at h17
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h17
  have h18 := W_gate starCircuit back (List.ofFn x) len 18 (by decide)
  change W starCircuit (List.ofFn x) 44 =
    GateOp.or.eval ([42, 43].map (W starCircuit (List.ofFn x))) at h18
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h18
  have h19 := W_gate starCircuit back (List.ofFn x) len 19 (by decide)
  change W starCircuit (List.ofFn x) 45 =
    GateOp.and.eval ([4, 44].map (W starCircuit (List.ofFn x))) at h19
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h19
  have h20 := W_gate starCircuit back (List.ofFn x) len 20 (by decide)
  change W starCircuit (List.ofFn x) 46 =
    GateOp.or.eval ([17, 21].map (W starCircuit (List.ofFn x))) at h20
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h20
  have h21 := W_gate starCircuit back (List.ofFn x) len 21 (by decide)
  change W starCircuit (List.ofFn x) 47 =
    GateOp.or.eval ([22, 24].map (W starCircuit (List.ofFn x))) at h21
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h21
  have h22 := W_gate starCircuit back (List.ofFn x) len 22 (by decide)
  change W starCircuit (List.ofFn x) 48 =
    GateOp.or.eval ([46, 47].map (W starCircuit (List.ofFn x))) at h22
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h22
  have h23 := W_gate starCircuit back (List.ofFn x) len 23 (by decide)
  change W starCircuit (List.ofFn x) 49 =
    GateOp.and.eval ([5, 48].map (W starCircuit (List.ofFn x))) at h23
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h23
  have h24 := W_gate starCircuit back (List.ofFn x) len 24 (by decide)
  change W starCircuit (List.ofFn x) 50 =
    GateOp.or.eval ([16, 20].map (W starCircuit (List.ofFn x))) at h24
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h24
  have h25 := W_gate starCircuit back (List.ofFn x) len 25 (by decide)
  change W starCircuit (List.ofFn x) 51 =
    GateOp.or.eval ([21, 23].map (W starCircuit (List.ofFn x))) at h25
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h25
  have h26 := W_gate starCircuit back (List.ofFn x) len 26 (by decide)
  change W starCircuit (List.ofFn x) 52 =
    GateOp.or.eval ([50, 51].map (W starCircuit (List.ofFn x))) at h26
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h26
  have h27 := W_gate starCircuit back (List.ofFn x) len 27 (by decide)
  change W starCircuit (List.ofFn x) 53 =
    GateOp.and.eval ([6, 52].map (W starCircuit (List.ofFn x))) at h27
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h27
  have h28 := W_gate starCircuit back (List.ofFn x) len 28 (by decide)
  change W starCircuit (List.ofFn x) 54 =
    GateOp.or.eval ([15, 19].map (W starCircuit (List.ofFn x))) at h28
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h28
  have h29 := W_gate starCircuit back (List.ofFn x) len 29 (by decide)
  change W starCircuit (List.ofFn x) 55 =
    GateOp.or.eval ([20, 22].map (W starCircuit (List.ofFn x))) at h29
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h29
  have h30 := W_gate starCircuit back (List.ofFn x) len 30 (by decide)
  change W starCircuit (List.ofFn x) 56 =
    GateOp.or.eval ([54, 55].map (W starCircuit (List.ofFn x))) at h30
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h30
  have h31 := W_gate starCircuit back (List.ofFn x) len 31 (by decide)
  change W starCircuit (List.ofFn x) 57 =
    GateOp.and.eval ([7, 56].map (W starCircuit (List.ofFn x))) at h31
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h31
  have h32 := W_gate starCircuit back (List.ofFn x) len 32 (by decide)
  change W starCircuit (List.ofFn x) 58 =
    GateOp.or.eval ([14, 18].map (W starCircuit (List.ofFn x))) at h32
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h32
  have h33 := W_gate starCircuit back (List.ofFn x) len 33 (by decide)
  change W starCircuit (List.ofFn x) 59 =
    GateOp.or.eval ([19, 21].map (W starCircuit (List.ofFn x))) at h33
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h33
  have h34 := W_gate starCircuit back (List.ofFn x) len 34 (by decide)
  change W starCircuit (List.ofFn x) 60 =
    GateOp.or.eval ([58, 59].map (W starCircuit (List.ofFn x))) at h34
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h34
  have h35 := W_gate starCircuit back (List.ofFn x) len 35 (by decide)
  change W starCircuit (List.ofFn x) 61 =
    GateOp.and.eval ([8, 60].map (W starCircuit (List.ofFn x))) at h35
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h35
  have h36 := W_gate starCircuit back (List.ofFn x) len 36 (by decide)
  change W starCircuit (List.ofFn x) 62 =
    GateOp.or.eval ([13, 17].map (W starCircuit (List.ofFn x))) at h36
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h36
  have h37 := W_gate starCircuit back (List.ofFn x) len 37 (by decide)
  change W starCircuit (List.ofFn x) 63 =
    GateOp.or.eval ([18, 20].map (W starCircuit (List.ofFn x))) at h37
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h37
  have h38 := W_gate starCircuit back (List.ofFn x) len 38 (by decide)
  change W starCircuit (List.ofFn x) 64 =
    GateOp.or.eval ([62, 63].map (W starCircuit (List.ofFn x))) at h38
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h38
  have h39 := W_gate starCircuit back (List.ofFn x) len 39 (by decide)
  change W starCircuit (List.ofFn x) 65 =
    GateOp.and.eval ([9, 64].map (W starCircuit (List.ofFn x))) at h39
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h39
  have h40 := W_gate starCircuit back (List.ofFn x) len 40 (by decide)
  change W starCircuit (List.ofFn x) 66 =
    GateOp.or.eval ([16, 17].map (W starCircuit (List.ofFn x))) at h40
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h40
  have h41 := W_gate starCircuit back (List.ofFn x) len 41 (by decide)
  change W starCircuit (List.ofFn x) 67 =
    GateOp.or.eval ([19, 25].map (W starCircuit (List.ofFn x))) at h41
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h41
  have h42 := W_gate starCircuit back (List.ofFn x) len 42 (by decide)
  change W starCircuit (List.ofFn x) 68 =
    GateOp.or.eval ([66, 67].map (W starCircuit (List.ofFn x))) at h42
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h42
  have h43 := W_gate starCircuit back (List.ofFn x) len 43 (by decide)
  change W starCircuit (List.ofFn x) 69 =
    GateOp.and.eval ([10, 68].map (W starCircuit (List.ofFn x))) at h43
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h43
  have h44 := W_gate starCircuit back (List.ofFn x) len 44 (by decide)
  change W starCircuit (List.ofFn x) 70 =
    GateOp.or.eval ([15, 16].map (W starCircuit (List.ofFn x))) at h44
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h44
  have h45 := W_gate starCircuit back (List.ofFn x) len 45 (by decide)
  change W starCircuit (List.ofFn x) 71 =
    GateOp.or.eval ([18, 24].map (W starCircuit (List.ofFn x))) at h45
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h45
  have h46 := W_gate starCircuit back (List.ofFn x) len 46 (by decide)
  change W starCircuit (List.ofFn x) 72 =
    GateOp.or.eval ([70, 71].map (W starCircuit (List.ofFn x))) at h46
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h46
  have h47 := W_gate starCircuit back (List.ofFn x) len 47 (by decide)
  change W starCircuit (List.ofFn x) 73 =
    GateOp.and.eval ([11, 72].map (W starCircuit (List.ofFn x))) at h47
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h47
  have h48 := W_gate starCircuit back (List.ofFn x) len 48 (by decide)
  change W starCircuit (List.ofFn x) 74 =
    GateOp.or.eval ([14, 15].map (W starCircuit (List.ofFn x))) at h48
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h48
  have h49 := W_gate starCircuit back (List.ofFn x) len 49 (by decide)
  change W starCircuit (List.ofFn x) 75 =
    GateOp.or.eval ([17, 23].map (W starCircuit (List.ofFn x))) at h49
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h49
  have h50 := W_gate starCircuit back (List.ofFn x) len 50 (by decide)
  change W starCircuit (List.ofFn x) 76 =
    GateOp.or.eval ([74, 75].map (W starCircuit (List.ofFn x))) at h50
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h50
  have h51 := W_gate starCircuit back (List.ofFn x) len 51 (by decide)
  change W starCircuit (List.ofFn x) 77 =
    GateOp.and.eval ([12, 76].map (W starCircuit (List.ofFn x))) at h51
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq] at h51
  have h52 := W_gate starCircuit back (List.ofFn x) len 52 (by decide)
  change W starCircuit (List.ofFn x) 78 =
    GateOp.or.eval ([29, 33].map (W starCircuit (List.ofFn x))) at h52
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h52
  have h53 := W_gate starCircuit back (List.ofFn x) len 53 (by decide)
  change W starCircuit (List.ofFn x) 79 =
    GateOp.or.eval ([78, 37].map (W starCircuit (List.ofFn x))) at h53
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h53
  have h54 := W_gate starCircuit back (List.ofFn x) len 54 (by decide)
  change W starCircuit (List.ofFn x) 80 =
    GateOp.or.eval ([79, 41].map (W starCircuit (List.ofFn x))) at h54
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h54
  have h55 := W_gate starCircuit back (List.ofFn x) len 55 (by decide)
  change W starCircuit (List.ofFn x) 81 =
    GateOp.or.eval ([80, 45].map (W starCircuit (List.ofFn x))) at h55
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h55
  have h56 := W_gate starCircuit back (List.ofFn x) len 56 (by decide)
  change W starCircuit (List.ofFn x) 82 =
    GateOp.or.eval ([81, 49].map (W starCircuit (List.ofFn x))) at h56
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h56
  have h57 := W_gate starCircuit back (List.ofFn x) len 57 (by decide)
  change W starCircuit (List.ofFn x) 83 =
    GateOp.or.eval ([82, 53].map (W starCircuit (List.ofFn x))) at h57
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h57
  have h58 := W_gate starCircuit back (List.ofFn x) len 58 (by decide)
  change W starCircuit (List.ofFn x) 84 =
    GateOp.or.eval ([83, 57].map (W starCircuit (List.ofFn x))) at h58
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h58
  have h59 := W_gate starCircuit back (List.ofFn x) len 59 (by decide)
  change W starCircuit (List.ofFn x) 85 =
    GateOp.or.eval ([84, 61].map (W starCircuit (List.ofFn x))) at h59
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h59
  have h60 := W_gate starCircuit back (List.ofFn x) len 60 (by decide)
  change W starCircuit (List.ofFn x) 86 =
    GateOp.or.eval ([85, 65].map (W starCircuit (List.ofFn x))) at h60
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h60
  have h61 := W_gate starCircuit back (List.ofFn x) len 61 (by decide)
  change W starCircuit (List.ofFn x) 87 =
    GateOp.or.eval ([86, 69].map (W starCircuit (List.ofFn x))) at h61
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h61
  have h62 := W_gate starCircuit back (List.ofFn x) len 62 (by decide)
  change W starCircuit (List.ofFn x) 88 =
    GateOp.or.eval ([87, 73].map (W starCircuit (List.ofFn x))) at h62
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h62
  have h63 := W_gate starCircuit back (List.ofFn x) len 63 (by decide)
  change W starCircuit (List.ofFn x) 89 =
    GateOp.or.eval ([88, 77].map (W starCircuit (List.ofFn x))) at h63
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at h63
  change W starCircuit (List.ofFn x) 89 = _
  rw [h63, h62, h61, h60, h59, h58, h57, h56, h55, h54, h53, h52, h51, h50, h49, h48, h47, h46, h45, h44, h43, h42, h41, h40, h39, h38, h37, h36, h35, h34, h33, h32, h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  simp only [W_input starCircuit x 0 (by decide), W_input starCircuit x 1 (by decide), W_input starCircuit x 2 (by decide), W_input starCircuit x 3 (by decide), W_input starCircuit x 4 (by decide), W_input starCircuit x 5 (by decide), W_input starCircuit x 6 (by decide), W_input starCircuit x 7 (by decide), W_input starCircuit x 8 (by decide), W_input starCircuit x 9 (by decide), W_input starCircuit x 10 (by decide), W_input starCircuit x 11 (by decide), W_input starCircuit x 12 (by decide), W_input starCircuit x 13 (by decide), W_input starCircuit x 14 (by decide), W_input starCircuit x 15 (by decide), W_input starCircuit x 16 (by decide), W_input starCircuit x 17 (by decide), W_input starCircuit x 18 (by decide), W_input starCircuit x 19 (by decide), W_input starCircuit x 20 (by decide), W_input starCircuit x 21 (by decide), W_input starCircuit x 22 (by decide), W_input starCircuit x 23 (by decide), W_input starCircuit x 24 (by decide), W_input starCircuit x 25 (by decide)]
  rfl

def edges : List (ℕ × ℕ) :=
  [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
lemma edges_iff : ∀ u v : Fin 26,
    (u.val, v.val) ∈ edges ↔
      (u = 0 ∧ v = 13) ∨
      (u = 0 ∧ v = 14) ∨
      (u = 0 ∧ v = 16) ∨
      (u = 0 ∧ v = 22) ∨
      (u = 1 ∧ v = 13) ∨
      (u = 1 ∧ v = 15) ∨
      (u = 1 ∧ v = 21) ∨
      (u = 1 ∧ v = 25) ∨
      (u = 2 ∧ v = 14) ∨
      (u = 2 ∧ v = 20) ∨
      (u = 2 ∧ v = 24) ∨
      (u = 2 ∧ v = 25) ∨
      (u = 3 ∧ v = 13) ∨
      (u = 3 ∧ v = 19) ∨
      (u = 3 ∧ v = 23) ∨
      (u = 3 ∧ v = 24) ∨
      (u = 4 ∧ v = 18) ∨
      (u = 4 ∧ v = 22) ∨
      (u = 4 ∧ v = 23) ∨
      (u = 4 ∧ v = 25) ∨
      (u = 5 ∧ v = 17) ∨
      (u = 5 ∧ v = 21) ∨
      (u = 5 ∧ v = 22) ∨
      (u = 5 ∧ v = 24) ∨
      (u = 6 ∧ v = 16) ∨
      (u = 6 ∧ v = 20) ∨
      (u = 6 ∧ v = 21) ∨
      (u = 6 ∧ v = 23) ∨
      (u = 7 ∧ v = 15) ∨
      (u = 7 ∧ v = 19) ∨
      (u = 7 ∧ v = 20) ∨
      (u = 7 ∧ v = 22) ∨
      (u = 8 ∧ v = 14) ∨
      (u = 8 ∧ v = 18) ∨
      (u = 8 ∧ v = 19) ∨
      (u = 8 ∧ v = 21) ∨
      (u = 9 ∧ v = 13) ∨
      (u = 9 ∧ v = 17) ∨
      (u = 9 ∧ v = 18) ∨
      (u = 9 ∧ v = 20) ∨
      (u = 10 ∧ v = 16) ∨
      (u = 10 ∧ v = 17) ∨
      (u = 10 ∧ v = 19) ∨
      (u = 10 ∧ v = 25) ∨
      (u = 11 ∧ v = 15) ∨
      (u = 11 ∧ v = 16) ∨
      (u = 11 ∧ v = 18) ∨
      (u = 11 ∧ v = 24) ∨
      (u = 12 ∧ v = 14) ∨
      (u = 12 ∧ v = 15) ∨
      (u = 12 ∧ v = 17) ∨
      (u = 12 ∧ v = 23) := by
  intro u v
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Fin.ext_iff]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma star_correct (x : Fin 26 → Bool) :
    starCircuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  rw [star_eval]
  simp_rw [edges_iff, or_and_right, exists_or]
  simp only [and_assoc, exists_and_left, exists_eq_left, Bool.and_eq_true, Bool.or_eq_true]
  simp only [and_or_left, or_assoc]

lemma size64 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 64 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  exact ⟨starCircuit, star_monotone, star_size.le, star_correct⟩

end PEqualNP.Outside.L_meta_650
