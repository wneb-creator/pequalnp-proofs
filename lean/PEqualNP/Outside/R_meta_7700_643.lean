import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_7700_643
    (edgeCases : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (∃ p ∈ ([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)), gateAt C 0 = ⟨GateOp.and, [p.1,p.2]⟩) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      (∃ g < C.size, ∃ h < C.size,
        (gateAt C g).op = GateOp.and ∧ (gateAt C h).op = GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal 14 C g (PEqualNP.SplitCount.unitInput 7) = true ∧
        PEqualNP.EdgeOwnership.gateVal 14 C g (PEqualNP.SplitCount.unitInput 0) = false ∧
        PEqualNP.EdgeOwnership.gateVal 14 C h (PEqualNP.SplitCount.unitInput 0) = true ∧
        PEqualNP.EdgeOwnership.gateVal 14 C h (PEqualNP.SplitCount.unitInput 7) = false) → False)
    (nonedgeCases : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (∃ p ∈ ([(0, 1), (0, 2), (0, 8), (1, 2), (1, 3), (1, 9), (1, 11), (2, 4), (2, 6), (2, 10)] : List (ℕ × ℕ)), gateAt C 0 = ⟨GateOp.and, [p.1,p.2]⟩) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      (∃ g < C.size, ∃ h < C.size,
        (gateAt C g).op = GateOp.and ∧ (gateAt C h).op = GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal 14 C g (PEqualNP.SplitCount.unitInput 7) = true ∧
        PEqualNP.EdgeOwnership.gateVal 14 C g (PEqualNP.SplitCount.unitInput 0) = false ∧
        PEqualNP.EdgeOwnership.gateVal 14 C h (PEqualNP.SplitCount.unitInput 0) = true ∧
        PEqualNP.EdgeOwnership.gateVal 14 C h (PEqualNP.SplitCount.unitInput 7) = false) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∃ x7 < x1.size,                 ∃ x8 < x1.size,                   (0 : ℕ) < x7 ∧                     (0 : ℕ) < x8 ∧                       x7 ≠ x8 ∧                         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                           (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                             have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = (0 : Fin (14 : ℕ))));                             have x10 : List Bool := x1.wires (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = (7 : Fin (14 : ℕ))));                             x10.getD ((14 : ℕ) + x7) Bool.false = Bool.true ∧ x9.getD ((14 : ℕ) + x7) Bool.false = Bool.false ∧ x9.getD ((14 : ℕ) + x8) Bool.false = Bool.true ∧ x10.getD ((14 : ℕ) + x8) Bool.false = Bool.false) →               False := by
  intro C hSize hAO hDist hFirst hFano hPair
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have gate_inputs2 : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.size,
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
      ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧
      opnd D j 0 < 14 + j ∧ opnd D j 1 < 14 + j := by
    intro D hD j hj
    have hmem : gateAt D j ∈ D.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hlen : (gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt D j).inputs = [a, b] := by
      cases h : (gateAt D j).inputs with
      | nil => simp [h] at hlen
      | cons a l1 =>
        cases l1 with
        | nil => simp [h] at hlen
        | cons b l2 =>
          cases l2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [h] at hlen
    have ha : opnd D j 0 = a := by unfold opnd; rw [hab]; rfl
    have hb : opnd D j 1 = b := by unfold opnd; rw [hab]; rfl
    refine ⟨by rw [hab, ha, hb], hD.1 _ hmem, ?_, ?_⟩
    · rw [ha]; exact hD.2.1 j hj a (by simp [hab])
    · rw [hb]; exact hD.2.1 j hj b (by simp [hab])
  have wire_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      (D.wires (List.ofFn x)).getD r false = x ⟨r, hr⟩ := by
    intro D x r hr
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt _ _ r (by simpa using hr), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wire_gate : ∀ (D : Circuit), IsAO2 14 D → ∀ (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.size),
      (D.wires (List.ofFn x)).getD (14 + j) false =
        (gateAt D j).op.eval
          [(D.wires (List.ofFn x)).getD (opnd D j 0) false,
           (D.wires (List.ofFn x)).getD (opnd D j 1) false] := by
    intro D hD x j hj
    have hj' : j < D.gates.length := hj
    obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 D hD j hj
    have hgj : D.gates[j] = gateAt D j := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj']
    have hsplit : D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
      rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
    let pref := (D.gates.take j).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + j := by
      dsimp only [pref]; rw [wfold_len, List.length_ofFn, List.length_take]; omega
    have hwstep_len : (wstep pref (gateAt D j)).length = 14 + j + 1 := by
      simp only [wstep, List.length_append, List.length_singleton, hpref_len]
    have hwires : D.wires (List.ofFn x) =
        (D.gates.drop (j + 1)).foldl wstep (wstep pref (gateAt D j)) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + j, pref.getD i false = (D.wires (List.ofFn x)).getD i false := by
      intro i hi
      rw [hwires, wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) i (by omega)]
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.length)]
    conv_lhs => rw [hwires]
    rw [wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) (14 + j) (by omega)]
    have hstep_at : (wstep pref (gateAt D j)).getD (14 + j) false =
        (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]; simp
    rw [hstep_at, hinp]
    simp only [List.map_cons, List.map_nil, hpref_get _ ha, hpref_get _ hb]
  have hCsize_pos : 0 < C.size := by
    by_contra h0
    have h0' : ¬ 0 < C.gates.length := h0
    have he : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hop : (gateAt C 0).op = GateOp.or := by unfold gateAt; rw [he]; rfl
    rw [hop] at hFirst
    exact GateOp.noConfusion hFirst
  have hCout : C.output < 14 + C.size := by
    by_contra hge
    have hge' : ¬ C.output < 14 + C.gates.length := hge
    have h07 : C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = true :=
      (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hf : C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false := by
      change (C.gates.foldl wstep (List.ofFn _)).getD C.output false = false
      exact List.getD_eq_default _ _ (by rw [wfold_len, List.length_ofFn]; omega)
    rw [h07] at hf
    exact Bool.noConfusion hf

  obtain ⟨h0inp, _, ha0lt0, hb0lt0⟩ := gate_inputs2 C hAO 0 hCsize_pos
  have ha0ne : opnd C 0 0 ≠ opnd C 0 1 := hDist 0 hCsize_pos
  let a0 : ℕ := opnd C 0 0
  let b0 : ℕ := opnd C 0 1
  have ha0lt : a0 < 14 := ha0lt0
  have hb0lt : b0 < 14 := hb0lt0
  let fanoAdjB : ℕ → ℕ → Bool := fun u v =>
    (decide (u < 7) && decide (7 ≤ v) && decide (v < 14) &&
      decide ((u = v - 7) ∨ (u = (v - 7 + 1) % 7) ∨ (u = (v - 7 + 3) % 7))) ||
    (decide (v < 7) && decide (7 ≤ u) && decide (u < 14) &&
      decide ((v = u - 7) ∨ (v = (u - 7 + 1) % 7) ∨ (v = (u - 7 + 3) % 7)))
  have fanoAdj_iff : ∀ u t : Fin 7,
      fanoAdjB (Fin.castAdd 7 u).val (Fin.natAdd 7 t).val = true ↔
        (u = t ∨ u = t + 1 ∨ u = t + 3) := by
    intro u t; revert u t; decide +kernel
  let perms : List (Bool × List ℕ × List ℕ) := [
    (false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
    (false, [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11], [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11]),
    (false, [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11], [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11]),
    (false, [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13], [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13]),
    (false, [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13], [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13]),
    (false, [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11], [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11]),
    (false, [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11], [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11]),
    (false, [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13], [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13]),
    (true, [7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1], [7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3]),
    (true, [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3], [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3]),
    (true, [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3], [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3]),
    (true, [7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1], [7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3]),
    (true, [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1], [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1]),
    (true, [7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3], [7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1]),
    (true, [7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3], [7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1]),
    (true, [7, 13, 12, 11, 10, 9, 8, 0, 6, 5, 4, 3, 2, 1], [7, 13, 12, 11, 10, 9, 8, 0, 6, 5, 4, 3, 2, 1])
  ]
  have hPermsValid : ∀ entry ∈ perms,
      let isDual := entry.1
      let f := entry.2.1
      let g := entry.2.2
      (∀ i : Fin 14, f.getD i.val 0 < 14 ∧ g.getD i.val 0 < 14 ∧
        g.getD (f.getD i.val 0) 0 = i.val ∧ f.getD (g.getD i.val 0) 0 = i.val) ∧
      f.getD 0 0 = (if isDual then 7 else 0) ∧
      f.getD 7 0 = (if isDual then 0 else 7) ∧
      (∀ u v : Fin 14, fanoAdjB (f.getD u.val 0) (f.getD v.val 0) = fanoAdjB u.val v.val) := by
    decide +kernel
  have hCover : ∀ u v : Fin 14, u ≠ v → ∃ entry ∈ perms,
      let pa := entry.2.1.getD u.val 0
      let pb := entry.2.1.getD v.val 0
      (min pa pb, max pa pb) ∈
        (([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)) ++ [(0, 1), (0, 2), (0, 8), (1, 2), (1, 3), (1, 9), (1, 11), (2, 4), (2, 6), (2, 10)]) := by decide +kernel
  obtain ⟨⟨isDual, fL, gL⟩, hentry, hrep⟩ := hCover ⟨a0, ha0lt⟩ ⟨b0, hb0lt⟩
    (fun h => ha0ne (congrArg Fin.val h))
  obtain ⟨hbij, hf0, hf7, hpres⟩ := hPermsValid (isDual, fL, gL) hentry
  let mapW : ℕ → ℕ := fun w => if w < 14 then fL.getD w 0 else w
  let invW : ℕ → ℕ := fun w => if w < 14 then gL.getD w 0 else w
  have hmapW_lt14 : ∀ w, mapW w < 14 ↔ w < 14 := by
    intro w
    by_cases hw : w < 14
    · dsimp only [mapW]; simp only [hw, ↓reduceIte, iff_true]; exact (hbij ⟨w, hw⟩).1
    · dsimp only [mapW]; simp only [hw, ↓reduceIte]
  have hinvW_mapW : ∀ w, invW (mapW w) = w := by
    intro w
    by_cases hw : w < 14
    · have h1 := (hbij ⟨w, hw⟩).1
      have h2 := (hbij ⟨w, hw⟩).2.2.1
      dsimp only [mapW, invW]; simp only [hw, h1, ↓reduceIte]; exact h2
    · dsimp only [mapW, invW]; simp only [hw, ↓reduceIte]
  have hmapW_invW : ∀ w, mapW (invW w) = w := by
    intro w
    by_cases hw : w < 14
    · have h1 := (hbij ⟨w, hw⟩).2.1
      have h2 := (hbij ⟨w, hw⟩).2.2.2
      dsimp only [mapW, invW]; simp only [hw, h1, ↓reduceIte]; exact h2
    · dsimp only [mapW, invW]; simp only [hw, ↓reduceIte]
  have hmapW_bound : ∀ w j, w < 14 + j → mapW w < 14 + j := by
    intro w j hw
    by_cases h14 : w < 14
    · have := (hmapW_lt14 w).2 h14; omega
    · simpa [mapW, h14] using hw
  have hmapW_inj : ∀ u v, mapW u = mapW v → u = v := by
    intro u v h
    have := congrArg invW h
    rwa [hinvW_mapW, hinvW_mapW] at this
  let pa := fL.getD a0 0
  let pb := fL.getD b0 0
  let swap0 : Gate → Gate := fun g =>
    if pa ≤ pb then g else ⟨g.op, [pb, pa]⟩
  let rawGates : List Gate := C.gates.map fun g => ⟨g.op, g.inputs.map mapW⟩
  let Dgates : List Gate :=
    List.casesOn rawGates [] (fun g0 rest => swap0 g0 :: rest)
  let D : Circuit := ⟨Dgates, mapW C.output⟩
  have hraw_len : rawGates.length = C.gates.length := List.length_map _
  have hDsize : D.size = C.size := by
    change Dgates.length = C.gates.length
    cases hr : rawGates with
    | nil => rw [← hraw_len]; simp [Dgates, hr]
    | cons g0 rest => rw [← hraw_len]; simp [Dgates, hr]
  have hDg0 : gateAt D 0 = ⟨GateOp.and, [min pa pb, max pa pb]⟩ := by
    have h0 : 0 < C.gates.length := hCsize_pos
    have hCg0 : C.gates[0] = gateAt C 0 := by unfold gateAt; rw [List.getD_eq_getElem _ _ h0]
    cases hCg : C.gates with
    | nil => simp [hCg] at h0
    | cons g0 rest =>
      have hg0eq : g0 = gateAt C 0 := by unfold gateAt; simp [hCg]
      have hg0op : g0.op = GateOp.and := hg0eq ▸ hFirst
      have hg0inp : g0.inputs = [a0, b0] := hg0eq ▸ h0inp
      have hmap0 : g0.inputs.map mapW = [pa, pb] := by
        rw [hg0inp]; simp only [List.map_cons, List.map_nil, mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
      have hDg : Dgates = swap0 ⟨g0.op, [pa, pb]⟩ :: rest.map (fun g => ⟨g.op, g.inputs.map mapW⟩) := by
        simp [Dgates, rawGates, hCg, hmap0]
      unfold gateAt
      change Dgates.getD 0 _ = _
      rw [hDg]
      simp only [List.getD_cons_zero, swap0, hg0op]
      by_cases hle : pa ≤ pb
      · simp [hle]
      · simp [hle, Nat.min_eq_right (Nat.le_of_not_ge hle), Nat.max_eq_left (Nat.le_of_not_ge hle)]
  have hDgate_pos : ∀ j, 0 < j → j < C.size →
      gateAt D j = ⟨(gateAt C j).op, (gateAt C j).inputs.map mapW⟩ := by
    intro j hjpos hjlt
    cases hCg : C.gates with
    | nil => change j < C.gates.length at hjlt; simp [hCg] at hjlt
    | cons g0 rest =>
      have hDg : Dgates = swap0 ⟨g0.op, g0.inputs.map mapW⟩ :: rest.map (fun g => ⟨g.op, g.inputs.map mapW⟩) := by
        simp [Dgates, rawGates, hCg]
      unfold gateAt
      change Dgates.getD j _ = ⟨(C.gates.getD j _).op, (C.gates.getD j _).inputs.map mapW⟩
      rw [hDg, hCg]
      cases j with
      | zero => omega
      | succ k =>
        have hk : k < rest.length := by change k + 1 < C.gates.length at hjlt; simp [hCg] at hjlt; omega
        simp [List.getD_eq_getElem?_getD, hk]
  have hDAO : IsAO2 14 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
      have hjlt : j < D.size := (List.getElem?_eq_some_iff.mp hj).1
      have hge : gateAt D j = g := by unfold gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
      rw [← hge]
      by_cases hj0 : j = 0
      · subst hj0; rw [hDg0]; exact Or.inl rfl
      · rw [hDgate_pos j (by omega) (hDsize ▸ hjlt)]
        exact (gate_inputs2 C hAO j (hDsize ▸ hjlt)).2.1
    · intro j hj i hi
      by_cases hj0 : j = 0
      · subst hj0; rw [hDg0] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        have hpa : pa < 14 := (hbij ⟨a0, ha0lt⟩).1
        have hpb : pb < 14 := (hbij ⟨b0, hb0lt⟩).1
        rcases hi with rfl | rfl <;> omega
      · have hjC : j < C.size := hDsize ▸ hj
        rw [hDgate_pos j (by omega) hjC] at hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
        exact hmapW_bound i0 j (hAO.2.1 j hjC i0 hi0)
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
      have hjlt : j < D.size := (List.getElem?_eq_some_iff.mp hj).1
      have hge : gateAt D j = g := by unfold gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
      rw [← hge]
      by_cases hj0 : j = 0
      · subst hj0; rw [hDg0]; rfl
      · rw [hDgate_pos j (by omega) (hDsize ▸ hjlt)]
        simp [(gate_inputs2 C hAO j (hDsize ▸ hjlt)).1]
  have hDdist : ∀ j < D.size, opnd D j 0 ≠ opnd D j 1 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have h0 : opnd D 0 0 = min pa pb ∧ opnd D 0 1 = max pa pb := by
        unfold opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
      rw [h0.1, h0.2]
      have hne : pa ≠ pb := by
        intro he
        have : mapW a0 = mapW b0 := by
          dsimp only [mapW]; simp only [ha0lt, hb0lt, ↓reduceIte]; exact he
        exact ha0ne (hmapW_inj a0 b0 this)
      omega
    · have hg := hDgate_pos j (by omega) (hDsize ▸ hj)
      obtain ⟨hinp, _, _, _⟩ := gate_inputs2 C hAO j (hDsize ▸ hj)
      have h0 : opnd D j 0 = mapW (opnd C j 0) ∧ opnd D j 1 = mapW (opnd C j 1) := by
        unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
      rw [h0.1, h0.2]
      intro he
      exact hDist j (hDsize ▸ hj) (hmapW_inj _ _ he)

  let finPerm : Fin 14 → Fin 14 := fun i => ⟨fL.getD i.val 0, (hbij i).1⟩
  let finInv : Fin 14 → Fin 14 := fun i => ⟨gL.getD i.val 0, (hbij i).2.1⟩
  have hDwire : ∀ (x : Fin 14 → Bool) (r : ℕ), r < 14 + C.size →
      (D.wires (List.ofFn x)).getD (mapW r) false =
        (C.wires (List.ofFn (fun i => x (finPerm i)))).getD r false := by
    intro x r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr
      by_cases h14 : r < 14
      · have hmr : mapW r < 14 := (hmapW_lt14 r).2 h14
        rw [wire_input D x (mapW r) hmr, wire_input C _ r h14]
        congr 1; ext; simp [mapW, finPerm, h14]
      · let j := r - 14
        have hj : j < C.size := by omega
        have hrj : r = 14 + j := by omega
        have hmr : mapW r = 14 + j := by simp [mapW, hrj]
        rw [hmr, hrj]
        rw [wire_gate D hDAO x j (hDsize.symm ▸ hj), wire_gate C hAO _ j hj]
        by_cases hj0 : j = 0
        · rw [hj0]
          have hd0 : opnd D 0 0 = min pa pb ∧ opnd D 0 1 = max pa pb := by
            unfold opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
          rw [hDg0, hFirst, hd0.1, hd0.2, eval_and, eval_and]
          have hpa_eq : min pa pb = mapW a0 ∧ max pa pb = mapW b0 ∨
              min pa pb = mapW b0 ∧ max pa pb = mapW a0 := by
            simp only [mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
            by_cases hle : fL.getD a0 0 ≤ fL.getD b0 0
            · exact Or.inl ⟨Nat.min_eq_left hle, Nat.max_eq_right hle⟩
            · exact Or.inr ⟨Nat.min_eq_right (Nat.le_of_not_ge hle), Nat.max_eq_left (Nat.le_of_not_ge hle)⟩
          rcases hpa_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2, ih a0 (by omega) (by omega), ih b0 (by omega) (by omega)]
          · rw [e1, e2, ih b0 (by omega) (by omega), ih a0 (by omega) (by omega), Bool.and_comm]
        · have hg := hDgate_pos j (by omega) hj
          obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 C hAO j hj
          have h0 : opnd D j 0 = mapW (opnd C j 0) ∧ opnd D j 1 = mapW (opnd C j 1) := by
            unfold opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
          rw [hg, h0.1, h0.2, ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
  have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    intro x
    have hev : D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (finPerm i))) :=
      hDwire x C.output hCout
    rw [hev, hFano]
    have hiff : ∀ y : Fin 14 → Bool,
        (∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          y (Fin.castAdd 7 u) = true ∧ y (Fin.natAdd 7 t) = true) ↔
        (∃ p q : Fin 14, fanoAdjB p.val q.val = true ∧ y p = true ∧ y q = true) := by
      intro y
      constructor
      · rintro ⟨u, t, hut, hu, ht⟩
        exact ⟨Fin.castAdd 7 u, Fin.natAdd 7 t, (fanoAdj_iff u t).2 hut, hu, ht⟩
      · rintro ⟨p, q, hpq, hp, hq⟩
        have hdisj : ∀ a b : Fin 14, fanoAdjB a.val b.val = true →
            (a.val < 7 ∧ 7 ≤ b.val) ∨ (b.val < 7 ∧ 7 ≤ a.val) := by decide +kernel
        rcases hdisj p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · let u : Fin 7 := ⟨p.val, h1⟩
          let t : Fin 7 := ⟨q.val - 7, by omega⟩
          have ep : p = Fin.castAdd 7 u := Fin.ext rfl
          have eq : q = Fin.natAdd 7 t := Fin.ext (by show q.val = 7 + (q.val - 7); omega)
          rw [ep] at hp; rw [eq] at hq; rw [ep, eq] at hpq
          exact ⟨u, t, (fanoAdj_iff u t).1 hpq, hp, hq⟩
        · let u : Fin 7 := ⟨q.val, h1⟩
          let t : Fin 7 := ⟨p.val - 7, by omega⟩
          have eq : q = Fin.castAdd 7 u := Fin.ext rfl
          have ep : p = Fin.natAdd 7 t := Fin.ext (by show p.val = 7 + (p.val - 7); omega)
          have hsym : ∀ a b : Fin 14, fanoAdjB a.val b.val = fanoAdjB b.val a.val := by decide +kernel
          rw [hsym, eq, ep] at hpq
          rw [eq] at hq; rw [ep] at hp
          exact ⟨u, t, (fanoAdj_iff u t).1 hpq, hq, hp⟩
    rw [hiff (fun i => x (finPerm i)), hiff x]
    constructor
    · rintro ⟨p, q, hpq, hp, hq⟩
      exact ⟨finPerm p, finPerm q, (hpres p q).trans hpq, hp, hq⟩
    · rintro ⟨p, q, hpq, hp, hq⟩
      have hinvP : finPerm (finInv p) = p := Fin.ext (hbij p).2.2.2
      have hinvQ : finPerm (finInv q) = q := Fin.ext (hbij q).2.2.2
      refine ⟨finInv p, finInv q, ?_, by simpa [hinvP] using hp, by simpa [hinvQ] using hq⟩
      have hpr := hpres (finInv p) (finInv q)
      have e1 : fL.getD (finInv p).val 0 = p.val := (hbij p).2.2.2
      have e2 : fL.getD (finInv q).val 0 = q.val := (hbij q).2.2.2
      rw [e1, e2] at hpr
      exact hpr.symm.trans hpq
  have single : ∀ (s : Bool) (k : ℕ), k < C.size →
      PEqualNP.EdgeOwnership.gateVal 14 D k (PEqualNP.SplitCount.unitInput (if s then 0 else 7)) =
      PEqualNP.EdgeOwnership.gateVal 14 C k
        (PEqualNP.SplitCount.unitInput (if (if isDual then !s else s) then 0 else 7)) := by
    intro s k hk
    let s' : Bool := if isDual then !s else s
    have hunit : (fun i : Fin 14 => decide (finPerm i = if s then 0 else 7)) =
        (fun i : Fin 14 => decide (i = if s' then 0 else 7)) := by
      funext i
      apply Bool.decide_congr
      have h0eq : finPerm 0 = (if isDual then 7 else 0) := by
        apply Fin.ext; change fL.getD 0 0 = _; rw [hf0]; cases isDual <;> rfl
      have h7eq : finPerm 7 = (if isDual then 0 else 7) := by
        apply Fin.ext; change fL.getD 7 0 = _; rw [hf7]; cases isDual <;> rfl
      have htarget : finPerm (if s' then 0 else 7) = (if s then 0 else 7) := by
        dsimp only [s']
        cases isDual <;> cases s <;> simp at h0eq h7eq ⊢ <;> first | exact h0eq | exact h7eq
      rw [← htarget]
      constructor
      · intro h
        have := congrArg finInv h
        have hi1 : finInv (finPerm i) = i := Fin.ext (hbij i).2.2.1
        have hi2 : finInv (finPerm (if s' then 0 else 7)) = (if s' then 0 else 7) :=
          Fin.ext (hbij _).2.2.1
        rwa [hi1, hi2] at this
      · intro h; rw [h]
    change (D.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))).getD (14+k) false =
      (C.wires (List.ofFn fun i : Fin 14 => decide (i = if s' then 0 else 7))).getD (14+k) false
    have hm : mapW (14+k) = 14+k := by simp [mapW]
    conv_lhs => rw [← hm]
    rw [hDwire _ (14+k) (by omega), hunit]
  have tr0 (k : ℕ) (hk : k < C.size) :
      PEqualNP.EdgeOwnership.gateVal 14 D k (PEqualNP.SplitCount.unitInput 0) =
      PEqualNP.EdgeOwnership.gateVal 14 C k (PEqualNP.SplitCount.unitInput (if isDual then 7 else 0)) := by
    have e := single true k hk
    cases isDual <;> simpa using e
  have tr7 (k : ℕ) (hk : k < C.size) :
      PEqualNP.EdgeOwnership.gateVal 14 D k (PEqualNP.SplitCount.unitInput 7) =
      PEqualNP.EdgeOwnership.gateVal 14 C k (PEqualNP.SplitCount.unitInput (if isDual then 0 else 7)) := by
    have e := single false k hk
    cases isDual <;> simpa using e
  obtain ⟨g,hg,h,hh,hgp,hhp,hne,hgop,hhop,hg7,hg0,hh0,hh7⟩ := hPair
  have hgopD : (gateAt D g).op = GateOp.and := by rw [hDgate_pos g hgp hg]; exact hgop
  have hhopD : (gateAt D h).op = GateOp.and := by rw [hDgate_pos h hhp hh]; exact hhop
  have dg0 := tr0 g hg
  have dg7 := tr7 g hg
  have dh0 := tr0 h hh
  have dh7 := tr7 h hh
  have hDpair : ∃ g < D.size, ∃ h < D.size,
      (gateAt D g).op = GateOp.and ∧ (gateAt D h).op = GateOp.and ∧
      PEqualNP.EdgeOwnership.gateVal 14 D g (PEqualNP.SplitCount.unitInput 7) = true ∧
      PEqualNP.EdgeOwnership.gateVal 14 D g (PEqualNP.SplitCount.unitInput 0) = false ∧
      PEqualNP.EdgeOwnership.gateVal 14 D h (PEqualNP.SplitCount.unitInput 0) = true ∧
      PEqualNP.EdgeOwnership.gateVal 14 D h (PEqualNP.SplitCount.unitInput 7) = false := by
    cases hd : isDual
    · simp only [hd, Bool.false_eq_true, ite_false] at dg0 dg7 dh0 dh7
      exact ⟨g, hDsize.symm ▸ hg, h, hDsize.symm ▸ hh, hgopD, hhopD,
        dg7.trans hg7, dg0.trans hg0, dh0.trans hh0, dh7.trans hh7⟩
    · simp only [hd, ite_true] at dg0 dg7 dh0 dh7
      exact ⟨h, hDsize.symm ▸ hh, g, hDsize.symm ▸ hg, hhopD, hgopD,
        dh7.trans hh0, dh0.trans hh7, dg0.trans hg7, dg7.trans hg0⟩
  rcases List.mem_append.mp hrep with he | hn
  · exact edgeCases D (hDsize.symm ▸ hSize) hDAO hDdist
      ⟨(min pa pb,max pa pb),he,hDg0⟩ hDFano hDpair
  · exact nonedgeCases D (hDsize.symm ▸ hSize) hDAO hDdist
      ⟨(min pa pb,max pa pb),hn,hDg0⟩ hDFano hDpair
