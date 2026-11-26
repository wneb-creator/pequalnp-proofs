import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_7698_3
    (lower : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) ∧ x (Fin.natAdd 7 l)) →
      27 ≤ C.size)
    (tailCase : ∀ e ∈ ([(0,7), (0,11), (1,8), (2,8)] : List (ℕ × ℕ)),
      ∀ T : Circuit, T.size = 26 → IsAO2 15 T →
      (∀ k < T.size, opnd T k 0 ≠ opnd T k 1) →
      let extend := fun x : Fin 14 → Bool =>
        let w := List.ofFn x
        w ++ [w.getD e.1 false && w.getD e.2 false]
      (∀ x, T.eval (extend x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) ∧ x (Fin.natAdd 7 l)) →
      ∀ j < T.size, (gateAt T j).op = GateOp.and →
      let v := fun (a b : Fin 14) (k : Fin 2) =>
        (T.wires (extend (pairInput a b))).getD (opnd T j k) false
      (∀ k, v 0 7 k = true) →
      (∃ a ∈ ([0,7] : List (Fin 14)), ∀ k, v a a k = false) →
      (∃ k, v 0 0 k = false ∧ v 7 7 k = false) → False) :
    ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = GateOp.and →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      (∃ j < C.size, 0 < j ∧ (gateAt C j).op = GateOp.and ∧
        let u := C.wires (List.ofFn fun i : Fin 14 => decide (i = 0))
        let v := C.wires (List.ofFn fun i : Fin 14 => decide (i = 7))
        let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7))
        let a := opnd C j 0
        let b := opnd C j 1
        w.getD a false = true ∧ w.getD b false = true ∧
          ((u.getD a false = false ∧ u.getD b false = false) ∨
           (v.getD a false = false ∧ v.getD b false = false)) ∧
          ((u.getD a false = false ∧ v.getD a false = false) ∨
           (u.getD b false = false ∧ v.getD b false = false))) → False := by
  intro C hSize hAO hDist hFirst hFano hWitness
  have hinc : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by decide +kernel
  have hExact : C.size = 27 := by
    have h := lower C hAO (by simpa only [hinc] using hFano)
    omega
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
      delta gateAt
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
    have ha : opnd D j 0 = a := by delta opnd; rw [hab]; rfl
    have hb : opnd D j 1 = b := by delta opnd; rw [hab]; rfl
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
      delta gateAt; rw [List.getD_eq_getElem _ _ hj']
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
  have eval_mono : ∀ (D : Circuit), IsAO2 14 D → ∀ (x y : Fin 14 → Bool),
      (∀ i, x i = true → y i = true) →
      ∀ r < 14 + D.size, (D.wires (List.ofFn x)).getD r false = true →
        (D.wires (List.ofFn y)).getD r false = true := by
    intro D hD x y hxy r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro hr hx
      by_cases h14 : r < 14
      · rw [wire_input D x r h14] at hx
        rw [wire_input D y r h14]
        exact hxy ⟨r, h14⟩ hx
      · let j := r - 14
        have hj : j < D.size := by omega
        have hrj : r = 14 + j := by omega
        rw [hrj] at hx ⊢
        obtain ⟨_, hop, ha, hb⟩ := gate_inputs2 D hD j hj
        rw [wire_gate D hD x j hj] at hx
        rw [wire_gate D hD y j hj]
        rcases hop with hand | hor
        · rw [hand, eval_and, Bool.and_eq_true] at hx ⊢
          exact ⟨ih _ (by omega) (by omega) hx.1, ih _ (by omega) (by omega) hx.2⟩
        · rw [hor, eval_or, Bool.or_eq_true] at hx ⊢
          rcases hx with h1 | h2
          · exact Or.inl (ih _ (by omega) (by omega) h1)
          · exact Or.inr (ih _ (by omega) (by omega) h2)
  have hCsize_pos : 0 < C.size := by omega
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
  by_cases hedge : fanoAdjB a0 b0 = true
  ·
    let perms : List (Bool × List ℕ × List ℕ) := [
      (false, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
      (false, [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11], [0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11]),
      (false, [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11], [0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11]),
      (false, [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13], [0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13]),
      (false, [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13], [0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13]),
      (false, [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11], [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11]),
      (false, [0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11], [0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11]),
      (false, [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13], [0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13]),
      (true,  [7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1], [7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3]),
      (true,  [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3], [7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3]),
      (true,  [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3], [7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3]),
      (true,  [7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1], [7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3]),
      (true,  [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1], [7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1])
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
    have hCover : ∀ u v : Fin 14, fanoAdjB u.val v.val = true →
        ∃ entry ∈ perms,
          let pa := entry.2.1.getD u.val 0
          let pb := entry.2.1.getD v.val 0
          (min pa pb, max pa pb) ∈ ([(0, 7), (0, 11), (1, 8), (2, 8)] : List (ℕ × ℕ)) := by
      decide +kernel
    obtain ⟨⟨isDual, fL, gL⟩, hentry, hrep⟩ := hCover ⟨a0, ha0lt⟩ ⟨b0, hb0lt⟩ hedge
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
      cases hCg : C.gates with
      | nil => simp [hCg] at h0
      | cons g0 rest =>
        have hg0eq : g0 = gateAt C 0 := by delta gateAt; simp [hCg]
        have hg0op : g0.op = GateOp.and := hg0eq ▸ hFirst
        have hg0inp : g0.inputs = [a0, b0] := hg0eq ▸ h0inp
        have hmap0 : g0.inputs.map mapW = [pa, pb] := by
          rw [hg0inp]; simp only [List.map_cons, List.map_nil, mapW, ha0lt, hb0lt, ↓reduceIte, pa, pb]
        have hDg : Dgates = swap0 ⟨g0.op, [pa, pb]⟩ :: rest.map (fun g => ⟨g.op, g.inputs.map mapW⟩) := by
          simp [Dgates, rawGates, hCg, hmap0]
        delta gateAt
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
        delta gateAt
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
        have hge : gateAt D j = g := by delta gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
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
        have hge : gateAt D j = g := by delta gateAt; rw [List.getD_eq_getElem?_getD, hj]; rfl
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
          delta opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
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
          delta opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
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
              delta opnd; rw [hDg0]; exact ⟨rfl, rfl⟩
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
              delta opnd; rw [hg, hinp]; exact ⟨rfl, rfl⟩
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
    obtain ⟨j, hj, hpos, hand, hwit⟩ := hWitness
    obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 C hAO j hj
    have hOp : ∀ b : Fin 2, opnd D j b = mapW (opnd C j b) := by
      intro b
      fin_cases b <;> delta opnd <;> rw [hDgate_pos j hpos hj, hinp] <;> rfl
    have hinj : Function.Injective finPerm := by
      intro i i' he
      apply Fin.ext
      exact hmapW_inj _ _ (by simpa [mapW, finPerm, i.isLt, i'.isLt] using congrArg Fin.val he)
    have h0 : finPerm 0 = (if isDual then 7 else 0) := by
      apply Fin.ext; change fL.getD 0 0 = _; rw [hf0]; cases isDual <;> rfl
    have h7 : finPerm 7 = (if isDual then 0 else 7) := by
      apply Fin.ext; change fL.getD 7 0 = _; rw [hf7]; cases isDual <;> rfl
    let V (X : Circuit) (a b : Fin 14) (k : Fin 2) :=
      (X.wires (List.ofFn (pairInput a b))).getD (opnd X j k) false
    have hTransport (a b : Fin 14) (k : Fin 2) :
        V D (finPerm a) (finPerm b) k = V C a b k := by
      have hk : opnd C j k < 14 + C.size := by fin_cases k <;> dsimp <;> omega
      have he : (fun i => pairInput (finPerm a) (finPerm b) (finPerm i)) = pairInput a b := by
        funext i
        change decide (finPerm i = finPerm a ∨ finPerm i = finPerm b) = decide (i = a ∨ i = b)
        exact Bool.decide_congr (or_congr hinj.eq_iff hinj.eq_iff)
      unfold V
      rw [hOp, hDwire _ _ hk, he]
    have hSwap (X : Circuit) (a b : Fin 14) (k : Fin 2) : V X a b k = V X b a k := by
      have he : pairInput a b = pairInput b a := by
        funext i
        exact Bool.decide_congr or_comm
      unfold V
      rw [he]
    have hCwit : (∀ k, V C 0 7 k = true) ∧
        ((∀ k, V C 0 0 k = false) ∨ (∀ k, V C 7 7 k = false)) ∧
        (∃ k, V C 0 0 k = false ∧ V C 7 7 k = false) := by
      dsimp only at hwit
      simp only [Fin.forall_fin_two, Fin.exists_fin_two, V]
      exact ⟨⟨hwit.1, hwit.2.1⟩, hwit.2.2⟩
    obtain ⟨hp, hs, ⟨k, hk0, hk7⟩⟩ := hCwit
    have hDw : (∀ b, V D 0 7 b = true) ∧
        (∃ a ∈ ([0,7] : List (Fin 14)), ∀ b, V D a a b = false) ∧
        (∃ b, V D 0 0 b = false ∧ V D 7 7 b = false) := by
      have hP := fun b => (hTransport 0 7 b).trans (hp b)
      have hS := hs.elim
        (fun h => Or.inl (fun b => (hTransport 0 0 b).trans (h b)))
        (fun h => Or.inr (fun b => (hTransport 7 7 b).trans (h b)))
      have hK := And.intro ((hTransport 0 0 k).trans hk0) ((hTransport 7 7 k).trans hk7)
      cases isDual <;> simp only [Bool.false_eq_true, ↓reduceIte] at h0 h7 <;>
        rw [h0, h7] at hP hS hK
      · refine ⟨hP, ?_, k, hK⟩
        rcases hS with h | h
        · exact ⟨0, by simp, h⟩
        · exact ⟨7, by simp, h⟩
      · refine ⟨fun b => (hSwap D 0 7 b).trans (hP b), ?_, k, hK.2, hK.1⟩
        rcases hS with h | h
        · exact ⟨7, by simp, h⟩
        · exact ⟨0, by simp, h⟩
    let e := (min pa pb, max pa pb)
    let T : Circuit := ⟨D.gates.tail, D.output⟩
    have hgs : D.gates = ⟨GateOp.and, [e.1, e.2]⟩ :: T.gates := by
      cases hg : D.gates with
      | nil =>
        have hl : D.gates.length = 27 := hDsize.trans hExact
        simp [hg] at hl
      | cons g gs =>
        have he : g = ⟨GateOp.and, [e.1, e.2]⟩ := by
          delta gateAt at hDg0
          simpa [hg, e] using hDg0
        simp [T, hg, he]
    have hlen : T.size + 1 = D.size := by change _ = D.gates.length; rw [hgs]; rfl
    have hgate (i : ℕ) : gateAt T i = gateAt D (i+1) := by delta gateAt; rw [hgs]; rfl
    have hop (i : ℕ) (b : Fin 2) : opnd T i b = opnd D (i+1) b := by delta opnd; rw [hgate]
    have hsub : ∀ g ∈ T.gates, g ∈ D.gates := by intro g hg; rw [hgs]; exact List.mem_cons_of_mem _ hg
    have hTAO : IsAO2 15 T := by
      refine ⟨fun g hg => hDAO.1 g (hsub _ hg), ?_, fun g hg => hDAO.2.2 g (hsub _ hg)⟩
      intro i hi w hw
      rw [hgate] at hw
      have hi' : i < T.size := hi
      have h := hDAO.2.1 (i+1) (by change i+1 < D.size; omega) w hw
      omega
    let extend (x : Fin 14 → Bool) :=
      let w := List.ofFn x
      w ++ [w.getD e.1 false && w.getD e.2 false]
    have hW (x : Fin 14 → Bool) : T.wires (extend x) = D.wires (List.ofFn x) := by
      unfold Circuit.wires
      rw [hgs, List.foldl_cons]
      simp only [List.map_cons, List.map_nil, eval_and, extend]
    have hCorr (x : Fin 14 → Bool) : T.eval (extend x) = D.eval (List.ofFn x) :=
      congrArg (fun w : List Bool => w.getD D.output false) (hW x)
    have hj' : j-1+1 = j := by omega
    refine tailCase e hrep T (by omega) hTAO
      (fun i hi => by rw [hop, hop]; exact hDdist _ (by omega))
      (fun x => by change T.eval (extend x) = true ↔ _; rw [hCorr, hDFano]; simp only [hinc])
      (j-1) (by omega) (by rw [hgate, hj', hDgate_pos j hpos hj]; exact hand) ?_ ?_ ?_
    all_goals dsimp only; simp only [show ∀ x, T.wires (let w := List.ofFn x; w ++ [w.getD e.1 false && w.getD e.2 false]) = D.wires (List.ofFn x) from hW, hop, hj']
    · exact hDw.1
    · exact hDw.2.1
    · exact hDw.2.2
  ·
    have h0_false_on_edge : ∀ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) →
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t))).getD 14 false = false := by
      intro u t hut
      have hw := wire_gate C hAO (fun i : Fin 14 => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)) 0 hCsize_pos
      rw [hFirst, eval_and, wire_input C _ a0 ha0lt, wire_input C _ b0 hb0lt] at hw
      rw [hw]
      cases h : (decide (⟨a0, ha0lt⟩ = Fin.castAdd 7 u ∨ ⟨a0, ha0lt⟩ = Fin.natAdd 7 t) &&
          decide (⟨b0, hb0lt⟩ = Fin.castAdd 7 u ∨ ⟨b0, hb0lt⟩ = Fin.natAdd 7 t)) with
      | false => rfl
      | true =>
        exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨ha | ha, hb | hb⟩
        · exact ha0ne (congrArg Fin.val (ha.trans hb.symm))
        · have ea : a0 = (Fin.castAdd 7 u).val := congrArg Fin.val ha
          have eb : b0 = (Fin.natAdd 7 t).val := congrArg Fin.val hb
          exact hedge (by rw [ea, eb]; exact (fanoAdj_iff u t).2 hut)
        · have ea : a0 = (Fin.natAdd 7 t).val := congrArg Fin.val ha
          have eb : b0 = (Fin.castAdd 7 u).val := congrArg Fin.val hb
          have hsym : ∀ p q : Fin 14, fanoAdjB p.val q.val = fanoAdjB q.val p.val := by decide +kernel
          exact hedge (by
            change fanoAdjB (⟨a0, ha0lt⟩ : Fin 14).val (⟨b0, hb0lt⟩ : Fin 14).val = true
            rw [hsym]; change fanoAdjB b0 a0 = true
            rw [ea, eb]; exact (fanoAdj_iff u t).2 hut)
        · exact ha0ne (congrArg Fin.val (ha.trans hb.symm))
    let optW (gs : List Gate) (x : Fin 14 → Bool) (o : Option ℕ) : Bool :=
      Option.casesOn o false (fun w => ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false)
    let Built (j : ℕ) :=
      ∃ (gs : List Gate) (rep : ℕ → Option ℕ),
          IsAO2 14 ⟨gs, 0⟩ ∧ gs.length + 1 ≤ j ∧
          (∀ w < 14 + j, ∀ w', rep w = some w' → w' < 14 + gs.length) ∧
          (∀ x : Fin 14 → Bool, ∀ w < 14 + j,
            optW gs x (rep w) = true → (C.wires (List.ofFn x)).getD w false = true) ∧
          (∀ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD 14 false = false →
            ∀ w < 14 + j, optW gs x (rep w) = (C.wires (List.ofFn x)).getD w false)
    have hBuild : ∀ j, 1 ≤ j → j ≤ C.size → Built j := by
      intro j hj1
      induction j with
      | zero => omega
      | succ j ih =>
        intro hjle
        by_cases hj0 : j = 0
        · subst hj0
          refine ⟨[], fun w => if w < 14 then some w else none, ?_, by simp, ?_, ?_, ?_⟩
          · exact ⟨(by intro g hg; cases hg), (by intro k hk; cases hk), (by intro g hg; cases hg)⟩
          · intro w hw w' hrep
            by_cases h14 : w < 14
            · simp [h14] at hrep; subst hrep; omega
            · simp [h14] at hrep
          · intro x w hw hval
            by_cases h14 : w < 14
            · simp only [h14, ↓reduceIte, optW] at hval
              rw [wire_input ⟨[], 0⟩ x w h14] at hval
              rw [wire_input C x w h14]
              exact hval
            · simp [h14, optW] at hval
          · intro x hx14 w hw
            by_cases h14 : w < 14
            · simp only [h14, ↓reduceIte, optW]
              rw [wire_input ⟨[], 0⟩ x w h14, wire_input C x w h14]
            · have ew : w = 14 := by omega
              subst ew
              simp only [Nat.lt_irrefl, ↓reduceIte, optW]
              exact hx14.symm
        · obtain ⟨gs, rep, hgsAO, hlen1, hrepLt, hUpper, hAgree⟩ :=
            ih (by omega) (by omega)
          have hjlt : j < C.size := by omega
          obtain ⟨hjinp, hjop, hja, hjb⟩ := gate_inputs2 C hAO j hjlt
          let a := opnd C j 0
          let b := opnd C j 1
          have noEmit : ∀ res : Option ℕ,
              (∀ w', res = some w' → w' < 14 + gs.length) →
              (∀ x, optW gs x res = true → (C.wires (List.ofFn x)).getD (14 + j) false = true) →
              (∀ x, (C.wires (List.ofFn x)).getD 14 false = false →
                optW gs x res = (C.wires (List.ofFn x)).getD (14 + j) false) →
              Built (j+1) := by
            intro res hresLt hresUp hresAg
            refine ⟨gs, fun w => if w = 14 + j then res else rep w, hgsAO, by omega, ?_, ?_, ?_⟩
            · intro w hw w' hrw
              by_cases hwj : w = 14 + j
              · simp [hwj] at hrw; exact hresLt w' hrw
              · simp [hwj] at hrw; exact hrepLt w (by omega) w' hrw
            · intro x w hw hval
              by_cases hwj : w = 14 + j
              · subst hwj; simp only [↓reduceIte] at hval; exact hresUp x hval
              · simp only [hwj, ↓reduceIte] at hval; exact hUpper x w (by omega) hval
            · intro x hx14 w hw
              by_cases hwj : w = 14 + j
              · subst hwj; simp only [↓reduceIte]; exact hresAg x hx14
              · simp only [hwj, ↓reduceIte]; exact hAgree x hx14 w (by omega)
          have doEmit : ∀ (op : GateOp) (a' b' : ℕ),
              (op = GateOp.and ∨ op = GateOp.or) →
              op = (gateAt C j).op →
              rep a = some a' → rep b = some b' → Built (j+1) := by
            intro op a' b' hop hopEq ha' hb'
            let gnew : Gate := ⟨op, [a', b']⟩
            let gs' : List Gate := gs ++ [gnew]
            have ha'lt : a' < 14 + gs.length := hrepLt a hja a' ha'
            have hb'lt : b' < 14 + gs.length := hrepLt b hjb b' hb'
            have hgs'len : gs'.length = gs.length + 1 := by simp [gs']
            have hgs'AO : IsAO2 14 ⟨gs', 0⟩ := by
              refine ⟨?_, ?_, ?_⟩
              · intro g hg
                simp only [gs', List.mem_append, List.mem_singleton] at hg
                rcases hg with hg | rfl
                · exact hgsAO.1 g hg
                · exact hop
              · intro k hk i hi
                change k < gs'.length at hk
                by_cases hklt : k < gs.length
                · have e : gateAt ⟨gs', 0⟩ k = gateAt ⟨gs, 0⟩ k := by
                    delta gateAt; change gs'.getD k _ = gs.getD k _
                    rw [List.getD_append _ _ _ _ hklt]
                  rw [e] at hi
                  exact hgsAO.2.1 k hklt i hi
                · have ek : k = gs.length := by omega
                  subst ek
                  have e : gateAt ⟨gs', 0⟩ gs.length = gnew := by
                    delta gateAt; change (gs ++ [gnew]).getD gs.length _ = gnew; simp
                  rw [e] at hi
                  simp only [gnew, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> omega
              · intro g hg
                simp only [gs', List.mem_append, List.mem_singleton] at hg
                rcases hg with hg | rfl
                · exact hgsAO.2.2 g hg
                · rfl
            have hWold : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + gs.length →
                ((Circuit.mk gs' 0).wires (List.ofFn x)).getD w false =
                ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false := by
              intro x w hw
              change ((gs ++ [gnew]).foldl wstep (List.ofFn x)).getD w false = _
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              have hl : (gs.foldl wstep (List.ofFn x)).length = 14 + gs.length := by
                rw [wfold_len, List.length_ofFn]
              have hlt : w < (gs.foldl wstep (List.ofFn x)).length := hl ▸ hw
              dsimp only [wstep]
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
              rfl
            have hWnew : ∀ x : Fin 14 → Bool,
                ((Circuit.mk gs' 0).wires (List.ofFn x)).getD (14 + gs.length) false =
                op.eval [((Circuit.mk gs 0).wires (List.ofFn x)).getD a' false,
                         ((Circuit.mk gs 0).wires (List.ofFn x)).getD b' false] := by
              intro x
              have hw := wire_gate ⟨gs', 0⟩ hgs'AO x gs.length (by change gs.length < gs'.length; omega)
              have e : gateAt ⟨gs', 0⟩ gs.length = gnew := by
                delta gateAt; change (gs ++ [gnew]).getD gs.length _ = gnew; simp
              have e0 : opnd ⟨gs', 0⟩ gs.length 0 = a' := by delta opnd; rw [e]; rfl
              have e1 : opnd ⟨gs', 0⟩ gs.length 1 = b' := by delta opnd; rw [e]; rfl
              rw [hw, e, e0, e1, hWold x a' ha'lt, hWold x b' hb'lt]
            have hOptOld : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + j →
                optW gs' x (rep w) = optW gs x (rep w) := by
              intro x w hw
              cases hr : rep w with
              | none => rfl
              | some w' => exact hWold x w' (hrepLt w hw w' hr)
            refine ⟨gs', fun w => if w = 14 + j then some (14 + gs.length) else rep w,
              hgs'AO, by omega, ?_, ?_, ?_⟩
            · intro w hw w' hrw
              by_cases hwj : w = 14 + j
              · simp [hwj] at hrw; subst hrw; omega
              · simp [hwj] at hrw; have := hrepLt w (by omega) w' hrw; omega
            · intro x w hw hval
              by_cases hwj : w = 14 + j
              · subst hwj
                simp only [↓reduceIte, optW, hWnew] at hval
                rw [wire_gate C hAO x j hjlt, ← hopEq]
                have hua := hUpper x a hja
                have hub := hUpper x b hjb
                simp only [ha', hb', optW] at hua hub
                rcases hop with rfl | rfl
                · rw [eval_and, Bool.and_eq_true] at hval ⊢
                  exact ⟨hua hval.1, hub hval.2⟩
                · rw [eval_or, Bool.or_eq_true] at hval ⊢
                  rcases hval with h1 | h2
                  · exact Or.inl (hua h1)
                  · exact Or.inr (hub h2)
              · simp only [hwj, ↓reduceIte] at hval
                rw [hOptOld x w (by omega)] at hval
                exact hUpper x w (by omega) hval
            · intro x hx14 w hw
              by_cases hwj : w = 14 + j
              · subst hwj
                simp only [↓reduceIte, optW, hWnew]
                rw [wire_gate C hAO x j hjlt, ← hopEq]
                have haa := hAgree x hx14 a hja
                have hab := hAgree x hx14 b hjb
                simp only [ha', hb', optW] at haa hab
                rw [haa, hab]
              · simp only [hwj, ↓reduceIte]
                rw [hOptOld x w (by omega)]
                exact hAgree x hx14 w (by omega)
          rcases hjop with hand | hor
          · cases hra : rep a with
            | none =>
              refine noEmit none (by intro _ h; cases h)
                (by intro x h; simp [optW] at h) ?_
              · intro x hx14
                rw [wire_gate C hAO x j hjlt, hand, eval_and]
                have haF := hAgree x hx14 a hja
                simp only [hra, optW] at haF
                rw [← haF]; rfl
            | some a' =>
              cases hrb : rep b with
              | none =>
                refine noEmit none (by intro _ h; cases h)
                  (by intro x h; simp [optW] at h) ?_
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hand, eval_and]
                  have hbF := hAgree x hx14 b hjb
                  simp only [hrb, optW] at hbF
                  rw [← hbF]; simp [optW]
              | some b' => exact doEmit .and a' b' (Or.inl rfl) hand.symm hra hrb
          · cases hra : rep a with
            | none =>
              cases hrb : rep b with
              | none =>
                refine noEmit none (by intro _ h; cases h)
                  (by intro x h; simp [optW] at h) ?_
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; rfl
              | some b' =>
                refine noEmit (some b')
                  (by intro w' h; cases h; exact hrepLt b hjb b' hrb)
                  ?_ ?_
                · intro x hval
                  rw [wire_gate C hAO x j hjlt, hor, eval_or, Bool.or_eq_true]
                  have hub := hUpper x b hjb
                  simp only [hrb] at hub
                  exact Or.inr (hub hval)
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; simp [optW]
            | some a' =>
              cases hrb : rep b with
              | none =>
                refine noEmit (some a')
                  (by intro w' h; cases h; exact hrepLt a hja a' hra)
                  ?_ ?_
                · intro x hval
                  rw [wire_gate C hAO x j hjlt, hor, eval_or, Bool.or_eq_true]
                  have hua := hUpper x a hja
                  simp only [hra] at hua
                  exact Or.inl (hua hval)
                · intro x hx14
                  rw [wire_gate C hAO x j hjlt, hor, eval_or]
                  have haa := hAgree x hx14 a hja
                  have hab := hAgree x hx14 b hjb
                  simp only [hra, hrb, optW] at haa hab
                  rw [← haa, ← hab]; simp [optW]
              | some b' => exact doEmit .or a' b' (Or.inr rfl) hor.symm hra hrb
    obtain ⟨gs, rep, hgsAO, hlen1, hrepLt, hUpper, hAgree⟩ :=
      hBuild C.size hCsize_pos (le_refl _)
    cases hrepOut : rep C.output with
    | none =>
      have h07 : C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7) ∨ i = Fin.natAdd 7 (0 : Fin 7))) = true :=
        (hFano _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
      have hAg := hAgree _ (h0_false_on_edge 0 0 (Or.inl rfl)) C.output hCout
      simp only [hrepOut, optW] at hAg
      exact Bool.noConfusion (hAg.trans h07)
    | some out' =>
      let D : Circuit := ⟨gs, out'⟩
      have hDAO : IsAO2 14 D := hgsAO
      have hDFano : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
        intro x
        constructor
        · intro hx
          have hup := hUpper x C.output hCout
          simp only [hrepOut, optW] at hup
          exact (hFano x).mp (hup hx)
        · rintro ⟨u, t, hut, hu, ht⟩
          let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 t)
          have hCe : C.eval (List.ofFn e) = true := (hFano e).mpr ⟨u, t, hut, by simp [e], by simp [e]⟩
          have hDe : (D.wires (List.ofFn e)).getD out' false = true := by
            have hAg := hAgree e (h0_false_on_edge u t hut) C.output hCout
            simp only [hrepOut, optW] at hAg
            exact hAg.trans hCe
          have houtLt : out' < 14 + D.size := hrepLt C.output hCout out' hrepOut
          refine eval_mono D hDAO e x (fun i hi => ?_) out' houtLt hDe
          simp only [e, decide_eq_true_eq] at hi
          rcases hi with rfl | rfl
          · exact hu
          · exact ht
      have h := lower D hDAO (by simpa only [hinc] using hDFano)
      change 27 ≤ gs.length at h
      omega
