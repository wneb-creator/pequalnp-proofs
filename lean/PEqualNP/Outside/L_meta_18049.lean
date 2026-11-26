import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18049

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]

private def stepLP (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  w ++ [match g.op with
    | GateOp.or => (ins.any (·.1), ins.any (·.2))
    | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
    | _ => (false, false)]

private lemma foldl_stepWire_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepWire init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    simp [ih]; omega

private lemma foldl_stepLP_len (gs : List Gate) (init : List (Bool × Bool)) :
    (gs.foldl stepLP init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepLP]
    simp [ih]; omega

private lemma getD_append_left_b (l : List Bool) (b : Bool) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k false = l.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma getD_append_last_b (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_append_left_p (l : List (Bool × Bool)) (b : Bool × Bool) (k : ℕ) (hk : k < l.length) :
    (l ++ [b]).getD k (false, false) = l.getD k (false, false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma getD_append_last_p (l : List (Bool × Bool)) (b : Bool × Bool) :
    (l ++ [b]).getD l.length (false, false) = b := by
  simp [List.getD_eq_getElem?_getD]

private lemma foldl_stepWire_getD_of_lt (gs : List Gate) (init : List Bool) (w : ℕ) (hw : w < init.length) :
    (gs.foldl stepWire init).getD w false = init.getD w false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire, getD_append_left_b]
    · exact ih
    · rw [foldl_stepWire_len]; omega

private lemma foldl_stepLP_getD_of_lt (gs : List Gate) (init : List (Bool × Bool)) (w : ℕ) (hw : w < init.length) :
    (gs.foldl stepLP init).getD w (false, false) = init.getD w (false, false) := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepLP, getD_append_left_p]
    · exact ih
    · rw [foldl_stepLP_len]; omega

private lemma list_split_at (l : List Gate) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ [l[j]] ++ l.drop (j + 1) := by
  calc l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
    _ = l.take j ++ (l[j] :: l.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
    _ = l.take j ++ [l[j]] ++ l.drop (j + 1) := by simp [List.append_assoc]

private lemma wires_gate_val (C : Circuit) (hRB : ReadsBack 26 C) (init : List Bool) (hinit : init.length = 26)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires init).getD (26 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires init).getD i false) := by
  have hsplit := list_split_at C.gates j hj
  change (C.gates.foldl stepWire init).getD (26 + j) false = _
  conv_lhs => rw [hsplit]
  rw [List.foldl_append]
  have hlen1 : ((C.gates.take j ++ [C.gates[j]]).foldl stepWire init).length = 26 + j + 1 := by
    rw [foldl_stepWire_len, hinit]; simp; omega
  rw [foldl_stepWire_getD_of_lt _ _ _ (by omega)]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
  have hlen0 : ((C.gates.take j).foldl stepWire init).length = 26 + j := by
    rw [foldl_stepWire_len, hinit]; simp; omega
  rw [← hlen0, getD_append_last_b]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hgat : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hilt : i < 26 + j := hRB j hj i (hgat ▸ hi)
  have hfull : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  change _ = (C.gates.foldl stepWire init).getD i false
  conv_rhs => rw [hfull, List.foldl_append]
  exact (foldl_stepWire_getD_of_lt (C.gates.drop j) _ i (by omega)).symm

private lemma lp_gate_val (C : Circuit) (hRB : ReadsBack 26 C) (init : List (Bool × Bool)) (hinit : init.length = 26)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl stepLP init).getD (26 + j) (false, false) =
      let ins := C.gates[j].inputs.map fun i => (C.gates.foldl stepLP init).getD i (false, false)
      match C.gates[j].op with
      | GateOp.or => (ins.any (·.1), ins.any (·.2))
      | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
            (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
      | _ => (false, false) := by
  have hsplit := list_split_at C.gates j hj
  conv_lhs => rw [hsplit]
  rw [List.foldl_append]
  have hlen1 : ((C.gates.take j ++ [C.gates[j]]).foldl stepLP init).length = 26 + j + 1 := by
    rw [foldl_stepLP_len, hinit]; simp; omega
  rw [foldl_stepLP_getD_of_lt _ _ _ (by omega)]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepLP]
  have hlen0 : ((C.gates.take j).foldl stepLP init).length = 26 + j := by
    rw [foldl_stepLP_len, hinit]; simp; omega
  rw [← hlen0, getD_append_last_p]
  have hmaps : (C.gates[j].inputs.map fun i => ((C.gates.take j).foldl stepLP init).getD i (false, false)) =
      (C.gates[j].inputs.map fun i => (C.gates.foldl stepLP init).getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    have hgat : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
    have hilt : i < 26 + j := hRB j hj i (hgat ▸ hi)
    have hfull : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hfull, List.foldl_append]
    exact (foldl_stepLP_getD_of_lt (C.gates.drop j) _ i (by omega)).symm
  dsimp only
  rw [hmaps]

end PEqualNP.Outside.L_meta_18049

theorem PEqualNP.Outside.L_meta_18049 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x2 < (26 : ℕ) → x3 < (26 : ℕ) → PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = x3)) x2 x3 = Bool.true → Relation.ReflTransGen (fun (x8 x9 : ℕ) => ∃ (x10 : ℕ) (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x9 = (26 : ℕ) + x10 ∧ x1.gates[x10]? = Option.some x12 ∧ (x12.inputs = [x8, x11] ∨ x12.inputs = [x11, x8]) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ (x1.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = x2))).getD x11 Bool.false = Bool.true)) x3 x1.output := by
  intro x1 x2 x3 hAO hx2 hx3 hls
  let isLine : ℕ → Bool := fun x7 => decide (x7 = x3)
  let xIn : List Bool := (List.range 26).map fun i => i == x2 || i == x3
  let initLP : List (Bool × Bool) := (xIn.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)
  let initW : List Bool := List.ofFn fun (k : Fin 26) => decide (k.val = x2)
  have hlenLP : initLP.length = 26 := by simp [initLP, xIn]
  have hlenW : initW.length = 26 := by simp [initW]
  let LP := x1.gates.foldl PEqualNP.Outside.L_meta_18049.stepLP initLP
  let W := x1.wires initW
  let stepRel : ℕ → ℕ → Prop := fun x8 x9 =>
    ∃ (x10 : ℕ) (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate),
      x9 = 26 + x10 ∧ x1.gates[x10]? = Option.some x12 ∧
      (x12.inputs = [x8, x11] ∨ x12.inputs = [x11, x8]) ∧
      (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ W.getD x11 Bool.false = Bool.true)
  have hinv : ∀ w : ℕ,
      ((LP.getD w (false, false)).1 = true → W.getD w false = true) ∧
      ((LP.getD w (false, false)).2 = true → Relation.ReflTransGen stepRel x3 w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw26 : w < 26
      · have hLPw : LP.getD w (false, false) = initLP.getD w (false, false) :=
          PEqualNP.Outside.L_meta_18049.foldl_stepLP_getD_of_lt x1.gates initLP w (by omega)
        have hWw : W.getD w false = initW.getD w false :=
          PEqualNP.Outside.L_meta_18049.foldl_stepWire_getD_of_lt x1.gates initW w (by omega)
        have hinitLP_w : initLP.getD w (false, false) =
            if isLine w then (false, (w == x2 || w == x3)) else ((w == x2 || w == x3), false) := by
          simp [initLP, xIn, List.getD_eq_getElem?_getD, hw26]
        have hinitW_w : initW.getD w false = decide (w = x2) := by
          dsimp only [initW]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw26]
          rfl
        rw [hLPw, hWw, hinitLP_w, hinitW_w]
        by_cases hwx3 : w = x3
        · have hisL : isLine w = true := by simp [isLine, hwx3]
          rw [hisL]; simp [hwx3]; exact Relation.ReflTransGen.refl
        · have hisL : isLine w = false := by simp [isLine, hwx3]
          rw [hisL]; simp [hwx3]
      · by_cases hwlt : w < 26 + x1.gates.length
        · let j := w - 26
          have hj : j < x1.gates.length := by omega
          have hw_eq : w = 26 + j := by omega
          have hgmem : x1.gates[j] ∈ x1.gates := List.getElem_mem hj
          have hgop := hAO.1 x1.gates[j] hgmem
          have hglen := hAO.2.2 x1.gates[j] hgmem
          rcases hgins : x1.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          · simp [hgins] at hglen
          · simp [hgins] at hglen
          · have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt x1 j = x1.gates[j] := by
              simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
            have ha_lt : a < 26 + j := hAO.2.1 j hj a (by rw [hgat, hgins]; simp)
            have hb_lt : b < 26 + j := hAO.2.1 j hj b (by rw [hgat, hgins]; simp)
            have iha := ih a (by omega)
            have ihb := ih b (by omega)
            have hLPj := PEqualNP.Outside.L_meta_18049.lp_gate_val x1 hAO.2.1 initLP hlenLP j hj
            have hWj := PEqualNP.Outside.L_meta_18049.wires_gate_val x1 hAO.2.1 initW hlenW j hj
            rw [hw_eq, hLPj, hWj]
            dsimp only
            rw [hgins]
            have hget_some : x1.gates[j]? = Option.some x1.gates[j] := by simp [hj]
            rcases hgop with hand | hor
            · rw [hand]
              simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
                Bool.true_and, Bool.false_and, Bool.or_false,
                PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              constructor
              · intro h1
                rw [Bool.and_eq_true] at h1 ⊢
                exact ⟨iha.1 h1.1, ihb.1 h1.2⟩
              · intro h2
                rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
                rcases h2 with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
                · exact Relation.ReflTransGen.tail (ihb.2 hb2)
                    ⟨j, a, x1.gates[j], rfl, hget_some, Or.inr hgins, Or.inr (iha.1 ha1)⟩
                · exact Relation.ReflTransGen.tail (iha.2 ha2)
                    ⟨j, b, x1.gates[j], rfl, hget_some, Or.inl hgins, Or.inr (ihb.1 hb1)⟩
            · rw [hor]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false,
                PEqualNP.CircuitLowerBounds.GateOp.eval, id_eq]
              constructor
              · intro h1
                rw [Bool.or_eq_true] at h1 ⊢
                rcases h1 with ha1 | hb1
                · exact Or.inl (iha.1 ha1)
                · exact Or.inr (ihb.1 hb1)
              · intro h2
                rw [Bool.or_eq_true] at h2
                rcases h2 with ha2 | hb2
                · exact Relation.ReflTransGen.tail (iha.2 ha2)
                    ⟨j, b, x1.gates[j], rfl, hget_some, Or.inl hgins, Or.inl hor⟩
                · exact Relation.ReflTransGen.tail (ihb.2 hb2)
                    ⟨j, a, x1.gates[j], rfl, hget_some, Or.inr hgins, Or.inl hor⟩
          · simp [hgins] at hglen
        · have hge : LP.length ≤ w := by
            dsimp only [LP]; rw [PEqualNP.Outside.L_meta_18049.foldl_stepLP_len, hlenLP]; omega
          have hnone : LP.getD w (false, false) = (false, false) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
          rw [hnone]
          simp
  exact (hinv x1.output).2 hls
