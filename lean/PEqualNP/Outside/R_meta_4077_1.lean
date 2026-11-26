import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4077_1
    (h670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (h1007 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (hAdj : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
      (PEqualNP.MetaComplexity.FanInTwo D ∧ 16 ≤ D.size ∧ D.size ≤ 17 ∧ 14 ≤ u ∧ u < 10 + D.size) →
      let rd := fun (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains i;
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10));
      let w := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x ++ [x 0 || x 1])).getD i false;
      (∀ p ∈ ([(0, 1), (1, 0)] : List (ℕ × ℕ)),
        D.gates.countP (fun g => rd g p.1 || (rd g p.2 && rd g 10)) + 15 ≤ D.size ∧
        ∀ i g, D.gates[i]? = some g → rd g p.1 = true → g.op.eval [true, false] = false →
          D.gates.countP (fun h => rd h p.1 || rd h (11 + i)) + 15 ≤ D.size) →
      D.gates.countP (fun g => rd g 0 || rd g 1 || rd g 10) + 12 ≤ D.size →
      (∀ k < 10, D.gates.countP (fun g => rd g k) + 14 ≤ D.size) →
      (∀ c : Bool, ∃ x, w x u = c ∧ w x (10 + D.size) = !c) →
      ¬ ∀ x : Fin 10 → Bool, (w x u && w x (10 + D.size)) = f x)
    (hNonAdj : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
      (PEqualNP.MetaComplexity.FanInTwo D ∧ 16 ≤ D.size ∧ D.size ≤ 17 ∧ 14 ≤ u ∧ u < 10 + D.size) →
      let rd := fun (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) => (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains i;
      let f := fun x : Fin 10 → Bool => [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10));
      let w := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x ++ [x 0 || x 2])).getD i false;
      (∀ p ∈ ([(0, 2), (2, 0)] : List (ℕ × ℕ)),
        D.gates.countP (fun g => rd g p.1 || (rd g p.2 && rd g 10)) + 15 ≤ D.size ∧
        ∀ i g, D.gates[i]? = some g → rd g p.1 = true → g.op.eval [true, false] = false →
          D.gates.countP (fun h => rd h p.1 || rd h (11 + i)) + 15 ≤ D.size) →
      (∀ k < 10, D.gates.countP (fun g => rd g k) + 14 ≤ D.size) →
      (∀ c : Bool, ∃ x, w x u = c ∧ w x (10 + D.size) = !c) →
      ¬ ∀ x : Fin 10 → Bool, (w x u && w x (10 + D.size)) = f x) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro b C0 a0 b0 hfan0 hsize0 fP w0 H1 H2 H3
  by_contra hneg
  let rd : Gate → ℕ → Bool := fun g i =>
    (g.inputs.take (if g.op.eval [true] = true then 2 else 1)).contains i
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have eval_nil : ∀ (n : ℕ) (x : List Bool), ({ gates := [], output := n } : Circuit).eval x = x.getD n false := fun _ _ => rfl
  have rd_and : ∀ xs i, rd ⟨.and, xs⟩ i = (xs.take 2).contains i := fun _ _ => rfl
  have rd_or : ∀ xs i, rd ⟨.or, xs⟩ i = (xs.take 2).contains i := fun _ _ => rfl
  have rd_not : ∀ xs i, rd ⟨.not, xs⟩ i = (xs.take 1).contains i := fun _ _ => rfl
  let fList : (Fin 10 → Bool) → Bool := fun x =>
    [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ =>
      x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
  have pc10 : ∀ x : Fin 10 → Bool, fList x = fP x := by
    intro x
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 || (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false))))))))))))))) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.or_false, Bool.or_assoc]
  have exactPair0 : ∀ x : Fin 10 → Bool, (w0 x a0 && w0 x b0) = fP x := by
    intro x
    cases h : fP x with
    | true =>
      obtain ⟨h1, h2⟩ := H3 x h
      simp [h1, h2]
    | false =>
      cases h1 : w0 x a0 <;> cases h2 : w0 x b0
      · rfl
      · rfl
      · rfl
      · exact False.elim (hneg ⟨x, h, h1, h2⟩)
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have runLen : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      dsimp only [step]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have retain : ∀ (gs : List Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons, ih (step ws g) i (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact List.getD_append ws _ false i hi
  let pFin : Fin 10 := if b = true then 1 else 2
  let seed : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x pFin]
  have seedEq : ∀ x : Fin 10 → Bool,
      List.ofFn x ++ [x 0 || if b = true then x 1 else x 2] = seed x := by
    intro x
    cases b <;> rfl
  have seedLen : ∀ x : Fin 10 → Bool, (seed x).length = 11 := by
    intro x
    simp [seed]
  have w0Eq : ∀ x i, w0 x i = (C0.gates.foldl step (seed x)).getD i false := by
    intro x i
    change (C0.gates.foldl step _).getD i false = _
    rw [seedEq x]
  have hiBound : ∀ i : ℕ, (∃ x, w0 x i = true) → i < 11 + C0.size := by
    intro i h
    obtain ⟨x, hx⟩ := h
    rw [w0Eq] at hx
    by_contra! hge
    have hlen : (C0.gates.foldl step (seed x)).length = 11 + C0.size := by
      rw [runLen, seedLen]; rfl
    rw [List.getD_eq_default _ _ (by omega)] at hx
    exact Bool.false_ne_true hx
  have haLt : a0 < 11 + C0.size := by
    obtain ⟨x, h1, _⟩ := H1
    exact hiBound a0 ⟨x, h1⟩
  have hbLt : b0 < 11 + C0.size := by
    obtain ⟨x, _, h2⟩ := H2
    exact hiBound b0 ⟨x, h2⟩
  have habNe : a0 ≠ b0 := by
    rintro rfl
    obtain ⟨x, h1, h2⟩ := H1
    rw [h1] at h2
    exact Bool.false_ne_true h2.symm
  let u := min a0 b0
  let v := max a0 b0
  have huv : u < v := by
    rcases lt_or_gt_of_ne habNe with h | h
    · simpa [u, v, min_eq_left h.le, max_eq_right h.le] using h
    · simpa [u, v, min_eq_right h.le, max_eq_left h.le] using h
  have hvLt : v < 11 + C0.size := max_lt haLt hbLt
  have H1u : ∃ x, w0 x u = true ∧ w0 x v = false := by
    rcases le_total a0 b0 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using H1
    · obtain ⟨x, h1, h2⟩ := H2
      exact ⟨x, by simpa [u, v, min_eq_right h] using h2, by simpa [u, v, max_eq_left h] using h1⟩
  have H2u : ∃ x, w0 x u = false ∧ w0 x v = true := by
    rcases le_total a0 b0 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using H2
    · obtain ⟨x, h1, h2⟩ := H1
      exact ⟨x, by simpa [u, v, min_eq_right h] using h2, by simpa [u, v, max_eq_left h] using h1⟩
  have exactUV0 : ∀ x : Fin 10 → Bool, (w0 x u && w0 x v) = fP x := by
    intro x
    rcases le_total a0 b0 with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using exactPair0 x
    · simpa [u, v, min_eq_right h, max_eq_left h, Bool.and_comm] using exactPair0 x
  have coneColor : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
      ∃ (col : Fin 10 → ℕ) (ws : List (Option ℕ)),
        ws.length = 11 + gs.length ∧
        9 ≤ (Finset.univ.image col).card + gs.length ∧
        ∀ i < 11 + gs.length, ∀ x y : Fin 10 → Bool,
          (∀ j : Fin 10, ws.getD i none = some (col j) → x j = y j) →
          (gs.foldl step (seed x)).getD i false = (gs.foldl step (seed y)).getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _
      let col0 : Fin 10 → ℕ := fun j => if j = pFin then 0 else j.val
      let ws0 : List (Option ℕ) := (List.finRange 10).map (fun j => some (col0 j)) ++ [some 0]
      refine ⟨col0, ws0, by simp [ws0], ?_, ?_⟩
      · have hc9 : (Finset.univ.image col0).card = 9 := by
          cases b <;> decide
        simp [hc9]
      · intro i hi x y hxy
        simp only [List.foldl_nil]
        by_cases h10 : i < 10
        · have hwi : ws0.getD i none = some (col0 ⟨i, h10⟩) := by
            have hlt : i < ((List.finRange 10).map (fun j => some (col0 j))).length := by simp [h10]
            dsimp only [ws0]
            rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
            simp
          have hxyi : x ⟨i, h10⟩ = y ⟨i, h10⟩ := hxy ⟨i, h10⟩ hwi
          have hlenx : i < (List.ofFn x).length := by simp [h10]
          have hleny : i < (List.ofFn y).length := by simp [h10]
          simp only [seed]
          rw [List.getD_append _ _ _ _ hlenx, List.getD_append _ _ _ _ hleny,
              List.getD_eq_getElem _ _ hlenx, List.getD_eq_getElem _ _ hleny,
              List.getElem_ofFn, List.getElem_ofFn]
          exact hxyi
        · have hi10 : i = 10 := by simp at hi; omega
          subst hi10
          have hw10 : ws0.getD 10 none = some 0 := by
            have hlen : ((List.finRange 10).map (fun j => some (col0 j))).length = 10 := by simp
            dsimp only [ws0]
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp [hlen]
          have h0 : x 0 = y 0 := hxy 0 (by rw [hw10]; simp [col0])
          have hp : x pFin = y pFin := hxy pFin (by rw [hw10]; simp [col0])
          simp only [seed]
          have lx : (List.ofFn x).length = 10 := by simp
          have ly : (List.ofFn y).length = 10 := by simp
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [h0, hp]
    | append_singleton gs g ih =>
      intro hlen
      obtain ⟨col, ws, hwsLen, hcard, hinv⟩ := ih (fun h hh => hlen h (List.mem_append_left _ hh))
      have hgLen : g.inputs.length ≤ 2 := hlen g (List.mem_append_right _ List.mem_cons_self)
      have readOld : ∀ (a : ℕ) (x y : Fin 10 → Bool),
          (∀ j : Fin 10, (if a < 11 + gs.length then ws.getD a none else none) = some (col j) → x j = y j) →
          (gs.foldl step (seed x)).getD a false = (gs.foldl step (seed y)).getD a false := by
        intro a x y hxy
        by_cases ha : a < 11 + gs.length
        · exact hinv a ha x y (by simpa [ha] using hxy)
        · have lx : (gs.foldl step (seed x)).length = 11 + gs.length := by rw [runLen, seedLen]
          have ly : (gs.foldl step (seed y)).length = 11 + gs.length := by rw [runLen, seedLen]
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have stepEnd : ∀ (x : Fin 10 → Bool),
          ((gs ++ [g]).foldl step (seed x)).getD (11 + gs.length) false =
          g.op.eval (g.inputs.map fun a => (gs.foldl step (seed x)).getD a false) := by
        intro x
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [step]
        have hlx : (gs.foldl step (seed x)).length = 11 + gs.length := by rw [runLen, seedLen]
        rw [List.getD_append_right _ _ _ _ hlx.le, hlx, Nat.sub_self, List.getD_cons_zero]
      have stepPre : ∀ (x : Fin 10 → Bool) (i : ℕ), i < 11 + gs.length →
          ((gs ++ [g]).foldl step (seed x)).getD i false = (gs.foldl step (seed x)).getD i false := by
        intro x i hi
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [step]
        exact List.getD_append _ _ false i (by rw [runLen, seedLen]; exact hi)
      cases hgi : g.inputs with
      | nil =>
        refine ⟨col, ws ++ [none], by simp [hwsLen]; omega, by simp; omega, ?_⟩
        intro i hi x y hxy
        by_cases hilt : i < 11 + gs.length
        · rw [stepPre x i hilt, stepPre y i hilt]
          exact hinv i hilt x y (fun j hj => hxy j (by rw [List.getD_append _ _ _ _ (by omega)]; exact hj))
        · have hiEq : i = 11 + gs.length := by simp at hi; omega
          subst hiEq
          simp only [stepEnd, hgi, List.map_nil]
      | cons a l =>
        cases l with
        | nil =>
          let ca : Option ℕ := if a < 11 + gs.length then ws.getD a none else none
          refine ⟨col, ws ++ [ca], by simp [hwsLen]; omega, by simp; omega, ?_⟩
          intro i hi x y hxy
          by_cases hilt : i < 11 + gs.length
          · rw [stepPre x i hilt, stepPre y i hilt]
            exact hinv i hilt x y (fun j hj => hxy j (by rw [List.getD_append _ _ _ _ (by omega)]; exact hj))
          · have hiEq : i = 11 + gs.length := by simp at hi; omega
            subst hiEq
            have hwa : (ws ++ [ca]).getD (11 + gs.length) none = ca := by
              rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hwsLen]
            have haEq := readOld a x y (fun j hj => hxy j (by rw [hwa]; exact hj))
            simp only [stepEnd, hgi, List.map_cons, List.map_nil, haEq]
        | cons c l2 =>
          cases l2 with
          | nil =>
            let ca : Option ℕ := if a < 11 + gs.length then ws.getD a none else none
            let cb : Option ℕ := if c < 11 + gs.length then ws.getD c none else none
            cases hca : ca with
            | none =>
              refine ⟨col, ws ++ [cb], by simp [hwsLen]; omega, by simp; omega, ?_⟩
              intro i hi x y hxy
              by_cases hilt : i < 11 + gs.length
              · rw [stepPre x i hilt, stepPre y i hilt]
                exact hinv i hilt x y (fun j hj => hxy j (by rw [List.getD_append _ _ _ _ (by omega)]; exact hj))
              · have hiEq : i = 11 + gs.length := by simp at hi; omega
                subst hiEq
                have hwb : (ws ++ [cb]).getD (11 + gs.length) none = cb := by
                  rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hwsLen]
                have haEq := readOld a x y (fun j hj => by change ca = some (col j) at hj; rw [hca] at hj; cases hj)
                have hcEq := readOld c x y (fun j hj => hxy j (by rw [hwb]; exact hj))
                simp only [stepEnd, hgi, List.map_cons, List.map_nil, haEq, hcEq]
            | some r1 =>
              cases hcb : cb with
              | none =>
                refine ⟨col, ws ++ [some r1], by simp [hwsLen]; omega, by simp; omega, ?_⟩
                intro i hi x y hxy
                by_cases hilt : i < 11 + gs.length
                · rw [stepPre x i hilt, stepPre y i hilt]
                  exact hinv i hilt x y (fun j hj => hxy j (by rw [List.getD_append _ _ _ _ (by omega)]; exact hj))
                · have hiEq : i = 11 + gs.length := by simp at hi; omega
                  subst hiEq
                  have hwa : (ws ++ [some r1]).getD (11 + gs.length) none = some r1 := by
                    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hwsLen]
                  have haEq := readOld a x y (fun j hj => hxy j (by rw [hwa]; change ca = some (col j) at hj; rw [hca] at hj; exact hj))
                  have hcEq := readOld c x y (fun j hj => by change cb = some (col j) at hj; rw [hcb] at hj; cases hj)
                  simp only [stepEnd, hgi, List.map_cons, List.map_nil, haEq, hcEq]
              | some r2 =>
                let mf : ℕ → ℕ := fun z => if z = r2 then r1 else z
                let col' : Fin 10 → ℕ := fun j => mf (col j)
                let ws' : List (Option ℕ) := (ws.map fun o => o.map mf) ++ [some r1]
                have hcard' : (Finset.univ.image col).card ≤ (Finset.univ.image col').card + 1 := by
                  have hsub : (Finset.univ.image col).erase r2 ⊆ Finset.univ.image col' := by
                    intro z hz
                    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hz
                    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
                    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
                    simp [col', mf, hne]
                  have hle := Finset.card_le_card hsub
                  have her2 : (Finset.univ.image col).card - 1 ≤ ((Finset.univ.image col).erase r2).card := by
                    by_cases hm : r2 ∈ Finset.univ.image col
                    · rw [Finset.card_erase_of_mem hm]
                    · rw [Finset.erase_eq_of_notMem hm]; omega
                  omega
                refine ⟨col', ws', by simp [ws', hwsLen]; omega, by simp; omega, ?_⟩
                intro i hi x y hxy
                by_cases hilt : i < 11 + gs.length
                · rw [stepPre x i hilt, stepPre y i hilt]
                  apply hinv i hilt x y
                  intro j hj
                  apply hxy j
                  have hmlen : i < (ws.map fun o => o.map mf).length := by simp [hwsLen, hilt]
                  dsimp only [ws']
                  rw [List.getD_append _ _ _ _ hmlen, List.getD_eq_getElem _ _ hmlen, List.getElem_map]
                  have hwi : ws[i]'(by omega) = ws.getD i none := (List.getD_eq_getElem ws none (by omega)).symm
                  rw [hwi, hj]
                  rfl
                · have hiEq : i = 11 + gs.length := by simp at hi; omega
                  subst hiEq
                  have hwlast : ws'.getD (11 + gs.length) none = some r1 := by
                    have hmlen : (ws.map fun o => o.map mf).length = 11 + gs.length := by simp [hwsLen]
                    dsimp only [ws']
                    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hmlen]
                  have haEq := readOld a x y fun j hj => by
                    apply hxy j
                    rw [hwlast]
                    change ca = some (col j) at hj
                    rw [hca] at hj
                    have hcj : r1 = col j := Option.some.inj hj
                    simp [col', mf, ← hcj]
                  have hcEq := readOld c x y fun j hj => by
                    apply hxy j
                    rw [hwlast]
                    change cb = some (col j) at hj
                    rw [hcb] at hj
                    have hcj : r2 = col j := Option.some.inj hj
                    simp [col', mf, ← hcj]
                  simp only [stepEnd, hgi, List.map_cons, List.map_nil, haEq, hcEq]
          | cons _ _ =>
            simp [hgi] at hgLen
  have tau6 : ∀ S : Finset (Fin 10), S.card ≤ 5 →
      ∃ e ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)),
        e.1 ∉ S ∧ e.2 ∉ S := by
    intro S hS
    by_contra hall
    push Not at hall
    have hcov : ∀ a b : Fin 10, (a, b) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)) →
        (decide (a ∈ S) || decide (b ∈ S)) = true := by
      intro a b hab
      by_cases ha : a ∈ S
      · simp [ha]
      · simp [ha, hall (a, b) hab ha]
    have h5 : ∀ p0 p1 p2 p3 p4 : Bool,
        (p0 || p1) = true → (p1 || p2) = true → (p2 || p3) = true → (p3 || p4) = true → (p4 || p0) = true →
        3 ≤ (if p0 then 1 else 0) + (if p1 then 1 else 0) + (if p2 then 1 else 0) + (if p3 then 1 else 0) + (if p4 then 1 else 0) := by
      decide
    have hOut := h5 (decide ((0 : Fin 10) ∈ S)) (decide ((1 : Fin 10) ∈ S)) (decide ((2 : Fin 10) ∈ S)) (decide ((3 : Fin 10) ∈ S)) (decide ((4 : Fin 10) ∈ S))
      (hcov 0 1 (by decide)) (hcov 1 2 (by decide)) (hcov 2 3 (by decide)) (hcov 3 4 (by decide)) (hcov 4 0 (by decide))
    have hIn := h5 (decide ((5 : Fin 10) ∈ S)) (decide ((7 : Fin 10) ∈ S)) (decide ((9 : Fin 10) ∈ S)) (decide ((6 : Fin 10) ∈ S)) (decide ((8 : Fin 10) ∈ S))
      (hcov 5 7 (by decide)) (hcov 7 9 (by decide)) (hcov 9 6 (by decide)) (hcov 6 8 (by decide)) (hcov 8 5 (by decide))
    have hsum : S.card = Finset.univ.sum (fun j : Fin 10 => if decide (j ∈ S) then 1 else 0) := by
      rw [← Finset.sum_filter]
      simp
    have h10 : Finset.univ.sum (fun j : Fin 10 => if decide (j ∈ S) then 1 else 0) =
        (if decide ((0 : Fin 10) ∈ S) then 1 else 0) + (if decide ((1 : Fin 10) ∈ S) then 1 else 0) +
        (if decide ((2 : Fin 10) ∈ S) then 1 else 0) + (if decide ((3 : Fin 10) ∈ S) then 1 else 0) +
        (if decide ((4 : Fin 10) ∈ S) then 1 else 0) + (if decide ((5 : Fin 10) ∈ S) then 1 else 0) +
        (if decide ((6 : Fin 10) ∈ S) then 1 else 0) + (if decide ((7 : Fin 10) ∈ S) then 1 else 0) +
        (if decide ((8 : Fin 10) ∈ S) then 1 else 0) + (if decide ((9 : Fin 10) ∈ S) then 1 else 0) := by
      have huniv : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
      rw [huniv]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
        Fin.reduceEq, or_self, not_false_eq_true]
      omega
    omega
  have lower14 : 14 ≤ u := by
    by_contra! hu14
    let m : ℕ := u - 10
    have hm3 : m ≤ 3 := by omega
    let gs := C0.gates.take m
    have hgsLen : gs.length ≤ 3 := by
      have : gs.length ≤ m := List.length_take_le m C0.gates
      omega
    obtain ⟨col, ws, hwsLen, hcard, hinv⟩ := coneColor gs (fun g hg => (hfan0 g (List.mem_of_mem_take hg)).2)
    have huLen : u < 11 + gs.length := by
      have hmin : gs.length = min m C0.gates.length := List.length_take
      change v < 11 + C0.gates.length at hvLt
      omega
    let c := ws.getD u none
    let S : Finset (Fin 10) := Finset.univ.filter fun j : Fin 10 => some (col j) = c
    have hScard : S.card ≤ 5 := by
      cases hc : c with
      | none =>
        have hSe : S = ∅ := by ext j; simp [S, hc]
        simp [hSe]
      | some r =>
        have himg : (Finset.univ.image col).erase r ⊆ (Finset.univ \ S).image col := by
          intro z hz
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hz
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
          refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
          simp [S, hc, hne]
        have h1 : ((Finset.univ.image col).erase r).card ≤ (Finset.univ \ S).card :=
          (Finset.card_le_card himg).trans Finset.card_image_le
        have h2 : (Finset.univ \ S).card = 10 - S.card := by
          rw [Finset.card_sdiff]
          simp
        have h3 : (Finset.univ.image col).card - 1 ≤ ((Finset.univ.image col).erase r).card := by
          by_cases hm : r ∈ Finset.univ.image col
          · rw [Finset.card_erase_of_mem hm]
          · rw [Finset.erase_eq_of_notMem hm]; omega
        omega
    obtain ⟨e, heMem, he1, he2⟩ := tau6 S hScard
    obtain ⟨x0, hx0u, _⟩ := H2u
    let y0 : Fin 10 → Bool := fun j => if j = e.1 ∨ j = e.2 then true else x0 j
    have hy0f : fP y0 = true := by
      have haux : ∀ e' : Fin 10 × Fin 10,
          e' ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)) →
          ∀ y : Fin 10 → Bool, y e'.1 = true → y e'.2 = true → fP y = true := by
        intro e' he' y h1 h2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [fP, h1, h2, Bool.and_true, Bool.true_or, Bool.or_true]
      exact haux e heMem y0 (by simp [y0]) (by simp [y0])
    have hy0u : w0 y0 u = true := by
      have heq := exactUV0 y0
      rw [hy0f] at heq
      cases hu' : w0 y0 u <;> simp [hu'] at heq ⊢
    have htakeEq : ∀ x : Fin 10 → Bool, (gs.foldl step (seed x)).getD u false = w0 x u := by
      intro x
      rw [w0Eq]
      have hsp : C0.gates = gs ++ C0.gates.drop m := (List.take_append_drop m C0.gates).symm
      rw [hsp, List.foldl_append]
      exact (retain _ _ u (by rw [runLen, seedLen]; exact huLen)).symm
    have hsame : w0 x0 u = w0 y0 u := by
      rw [← htakeEq x0, ← htakeEq y0]
      apply hinv u huLen x0 y0
      intro j hj
      have hjS : j ∈ S := by simp [S, c, hj.symm]
      have hne1 : j ≠ e.1 := fun h => he1 (h ▸ hjS)
      have hne2 : j ≠ e.2 := fun h => he2 (h ▸ hjS)
      simp [y0, hne1, hne2]
    rw [hx0u, hy0u] at hsame
    exact Bool.false_ne_true hsame
  let D : Circuit := ⟨C0.gates.take (v - 10), 0⟩
  have hDsize : D.size = v - 10 := by
    change (C0.gates.take (v - 10)).length = v - 10
    change v < 11 + C0.gates.length at hvLt
    rw [List.length_take]
    omega
  have hDle17 : D.size ≤ 17 := by
    change C0.gates.length ≤ 17 at hsize0
    change v < 11 + C0.gates.length at hvLt
    omega
  have hDfan : FanInTwo D := fun g hg => hfan0 g (List.mem_of_mem_take hg)
  have hvEq : 10 + D.size = v := by omega
  have huLtD : u < 10 + D.size := by omega
  let wD : (Fin 10 → Bool) → ℕ → Bool := fun x i => (D.wires (seed x)).getD i false
  have wDeq : ∀ x i, i ≤ v → wD x i = w0 x i := by
    intro x i hi
    rw [w0Eq]
    have hsp : C0.gates = D.gates ++ C0.gates.drop (v - 10) := (List.take_append_drop (v - 10) C0.gates).symm
    rw [hsp, List.foldl_append]
    exact (retain _ _ i (by change i < (D.gates.foldl step (seed x)).length; rw [runLen, seedLen]; change i < 11 + D.size; omega)).symm
  have H1D : ∃ x, wD x u = true ∧ wD x (10 + D.size) = false := by
    obtain ⟨x, h1, h2⟩ := H1u
    exact ⟨x, (wDeq x u huv.le).trans h1, (wDeq x (10 + D.size) (by omega)).trans (by rwa [hvEq])⟩
  have H2D : ∃ x, wD x u = false ∧ wD x (10 + D.size) = true := by
    obtain ⟨x, h1, h2⟩ := H2u
    exact ⟨x, (wDeq x u huv.le).trans h1, (wDeq x (10 + D.size) (by omega)).trans (by rwa [hvEq])⟩
  have exactD : ∀ x : Fin 10 → Bool, (wD x u && wD x (10 + D.size)) = fP x := by
    intro x
    rw [wDeq x u huv.le, wDeq x (10 + D.size) (by omega), hvEq]
    exact exactUV0 x
  let evalV : List Bool → Sum Bool ℕ → Bool := fun ws s =>
    Sum.casesOn s (fun c => c) (fun j => ws.getD j false)
  let simpGate : ℕ → List (Sum Bool ℕ) → List Gate → Gate → Sum Bool ℕ × List Gate :=
    fun n env acc g =>
      GateOp.casesOn g.op
        (List.casesOn g.inputs (.inl true, acc) fun a l =>
          List.casesOn l (env.getD a (.inl false), acc) fun c l2 =>
            List.casesOn l2
              (Sum.casesOn (env.getD a (.inl false))
                (fun ba => Bool.casesOn ba (.inl false, acc) (env.getD c (.inl false), acc))
                (fun wa => Sum.casesOn (env.getD c (.inl false))
                  (fun bc => Bool.casesOn bc (.inl false, acc) (.inr wa, acc))
                  (fun wc => if wa = wc then (.inr wa, acc) else (.inr (n + acc.length), acc ++ [⟨.and, [wa, wc]⟩]))))
              (fun _ _ => (.inl false, acc)))
        (List.casesOn g.inputs (.inl false, acc) fun a l =>
          List.casesOn l (env.getD a (.inl false), acc) fun c l2 =>
            List.casesOn l2
              (Sum.casesOn (env.getD a (.inl false))
                (fun ba => Bool.casesOn ba (env.getD c (.inl false), acc) (.inl true, acc))
                (fun wa => Sum.casesOn (env.getD c (.inl false))
                  (fun bc => Bool.casesOn bc (.inr wa, acc) (.inl true, acc))
                  (fun wc => if wa = wc then (.inr wa, acc) else (.inr (n + acc.length), acc ++ [⟨.or, [wa, wc]⟩]))))
              (fun _ _ => (.inl false, acc)))
        (List.casesOn g.inputs (.inl true, acc) fun a _ =>
          Sum.casesOn (env.getD a (.inl false))
            (fun c => (.inl (!c), acc))
            (fun wa => (.inr (n + acc.length), acc ++ [⟨.not, [wa]⟩])))
        (fun _ => (.inl false, acc))
        (.inl false, acc)
  let simpStep : ℕ → (List (Sum Bool ℕ) × List Gate) → Gate → (List (Sum Bool ℕ) × List Gate) :=
    fun n st g => (st.1 ++ [(simpGate n st.1 st.2 g).1], (simpGate n st.1 st.2 g).2)
  have simpStep_envLen : ∀ n st g, (simpStep n st g).1.length = st.1.length + 1 := fun _ st _ => by
    simp only [simpStep, List.length_append, List.length_cons, List.length_nil]
  have simpStep_envPrefix : ∀ n st g i, i < st.1.length →
      (simpStep n st g).1.getD i (.inl false) = st.1.getD i (.inl false) := fun _ st _ i hi =>
    List.getD_append st.1 _ (.inl false) i hi
  have simpStep_lenLe : ∀ n st g, (simpStep n st g).2.length ≤ st.2.length + 1 := by
    intro n st g
    rcases g with ⟨op, inputs⟩
    cases op with
    | not =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a _ =>
        dsimp only [simpStep, simpGate]
        cases st.1.getD a (.inl false) with
        | inl _ => exact Nat.le_succ _
        | inr _ => simp only [List.length_append, List.length_cons, List.length_nil]; omega
    | and =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a l =>
        cases l with
        | nil => exact Nat.le_succ _
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact Nat.le_succ _
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact Nat.le_succ _
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact Nat.le_succ _
                · simp only [heq, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
          | cons _ _ => exact Nat.le_succ _
    | or =>
      cases inputs with
      | nil => exact Nat.le_succ _
      | cons a l =>
        cases l with
        | nil => exact Nat.le_succ _
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact Nat.le_succ _
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact Nat.le_succ _
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact Nat.le_succ _
                · simp only [heq, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
          | cons _ _ => exact Nat.le_succ _
    | mod _ => exact Nat.le_succ _
    | maj => exact Nat.le_succ _
  have simpStep_fan : ∀ n st g, FanInTwo ⟨st.2, 0⟩ → FanInTwo ⟨(simpStep n st g).2, 0⟩ := by
    intro n st g hst
    rcases g with ⟨op, inputs⟩
    have hadd : ∀ op' is, op' ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → is.length ≤ 2 →
        FanInTwo ⟨st.2 ++ [⟨op', is⟩], 0⟩ := by
      intro op' is hop his h hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hst h hm
      · obtain rfl := List.mem_singleton.mp hm
        exact ⟨hop, his⟩
    cases op with
    | not =>
      cases inputs with
      | nil => exact hst
      | cons a _ =>
        dsimp only [simpStep, simpGate]
        cases st.1.getD a (.inl false) with
        | inl _ => exact hst
        | inr wa => exact hadd .not [wa] (Or.inr (Or.inr rfl)) (by simp)
    | and =>
      cases inputs with
      | nil => exact hst
      | cons a l =>
        cases l with
        | nil => exact hst
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hst
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hst
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hst
                · simp only [heq, ↓reduceIte]; exact hadd .and [wa, wc] (Or.inl rfl) (by simp)
          | cons _ _ => exact hst
    | or =>
      cases inputs with
      | nil => exact hst
      | cons a l =>
        cases l with
        | nil => exact hst
        | cons c l2 =>
          cases l2 with
          | nil =>
            dsimp only [simpStep, simpGate]
            cases st.1.getD a (.inl false) with
            | inl ba => cases ba <;> exact hst
            | inr wa =>
              cases st.1.getD c (.inl false) with
              | inl bc => cases bc <;> exact hst
              | inr wc =>
                by_cases heq : wa = wc
                · simp only [heq, ↓reduceIte]; exact hst
                · simp only [heq, ↓reduceIte]; exact hadd .or [wa, wc] (Or.inr (Or.inl rfl)) (by simp)
          | cons _ _ => exact hst
    | mod _ => exact hst
    | maj => exact hst
  have simpStep_sound : ∀ (n : ℕ) (st : List (Sum Bool ℕ) × List Gate) (g : Gate)
      (y : Fin n → Bool) (orig : List Bool),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      orig.length = st.1.length →
      (∀ s ∈ st.1, ∀ j, s = .inr j → j < n + st.2.length) →
      (∀ i < st.1.length, evalV (st.2.foldl step (List.ofFn y)) (st.1.getD i (.inl false)) = orig.getD i false) →
      (∀ s ∈ (simpStep n st g).1, ∀ j, s = .inr j → j < n + (simpStep n st g).2.length) ∧
      (∀ i < (simpStep n st g).1.length,
        evalV ((simpStep n st g).2.foldl step (List.ofFn y)) ((simpStep n st g).1.getD i (.inl false)) =
        (step orig g).getD i false) := by
    intro n st g y orig hop hglen hlen hbdd htr
    have htrAll : ∀ a, evalV (st.2.foldl step (List.ofFn y)) (st.1.getD a (.inl false)) = orig.getD a false := by
      intro a
      by_cases ha : a < st.1.length
      · exact htr a ha
      · rw [List.getD_eq_default st.1 _ (by omega), List.getD_eq_default orig _ (by omega)]
    have hwsLen : (st.2.foldl step (List.ofFn y)).length = n + st.2.length := by
      rw [runLen, List.length_ofFn]
    have hvalBdd : ∀ a j, st.1.getD a (.inl false) = .inr j → j < n + st.2.length := by
      intro a j hj
      by_cases ha : a < st.1.length
      · rw [List.getD_eq_getElem _ _ ha] at hj
        exact hbdd _ (List.getElem_mem ha) j hj
      · rw [List.getD_eq_default _ _ (by omega)] at hj; cases hj
    have hpush : ∀ (val : Sum Bool ℕ) (acc' : List Gate)
        (hext : acc' = st.2 ∨ ∃ g', acc' = st.2 ++ [g'])
        (hvb : ∀ j, val = .inr j → j < n + acc'.length)
        (hve : evalV (acc'.foldl step (List.ofFn y)) val = g.op.eval (g.inputs.map fun i => orig.getD i false)),
        (∀ s ∈ st.1 ++ [val], ∀ j, s = .inr j → j < n + acc'.length) ∧
        (∀ i < (st.1 ++ [val]).length,
          evalV (acc'.foldl step (List.ofFn y)) ((st.1 ++ [val]).getD i (.inl false)) = (step orig g).getD i false) := by
      intro val acc' hext hvb hve
      have haccLe : st.2.length ≤ acc'.length := by
        rcases hext with rfl | ⟨g', rfl⟩
        · exact le_rfl
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hkeep : ∀ s, (∀ j, s = .inr j → j < n + st.2.length) →
          evalV (acc'.foldl step (List.ofFn y)) s = evalV (st.2.foldl step (List.ofFn y)) s := by
        intro s hs
        cases s with
        | inl c => rfl
        | inr j =>
          rcases hext with rfl | ⟨g', rfl⟩
          · rfl
          · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            exact List.getD_append _ _ false j (by rw [hwsLen]; exact hs j rfl)
      constructor
      · intro s hs j hj
        rcases List.mem_append.mp hs with hs | hs
        · exact lt_of_lt_of_le (hbdd s hs j hj) (Nat.add_le_add_left haccLe n)
        · obtain rfl := List.mem_singleton.mp hs
          exact hvb j hj
      · intro i hi
        by_cases hilt : i < st.1.length
        · rw [List.getD_append _ _ _ _ hilt, List.getD_append orig _ _ _ (by omega)]
          rw [hkeep _ (hvalBdd i), htr i hilt]
        · have hiEq : i = st.1.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega
          subst hiEq
          rw [List.getD_append_right st.1 _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          dsimp only [step]
          rw [List.getD_append_right orig _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
          exact hve
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil =>
        exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        cases l with
        | nil =>
          exact hpush (st.1.getD a (.inl false)) st.2 (Or.inl rfl) (hvalBdd a)
            (by simpa [eval_and] using htrAll a)
        | cons c l2 =>
          cases l2 with
          | nil =>
            have hgoal : GateOp.and.eval ([a, c].map fun i => orig.getD i false) =
                (evalV (st.2.foldl step (List.ofFn y)) (st.1.getD a (.inl false)) &&
                 evalV (st.2.foldl step (List.ofFn y)) (st.1.getD c (.inl false))) := by
              simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true,
                htrAll a, htrAll c]
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba =>
              cases ba with
              | false =>
                exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h)
                  (by rw [hgoal, ha]; rfl)
              | true =>
                exact hpush (st.1.getD c (.inl false)) st.2 (Or.inl rfl) (hvalBdd c)
                  (by rw [hgoal, ha]; simp only [evalV, Bool.true_and])
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc =>
                cases bc with
                | false =>
                  exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h)
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_false])
                | true =>
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj)) (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_true])
              | inr wc =>
                by_cases heq : wa = wc
                · subst heq; simp only [↓reduceIte]
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj))
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.and_self])
                · simp only [heq, ↓reduceIte]
                  exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.and, [wa, wc]⟩]) (Or.inr ⟨_, rfl⟩)
                    (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                    (by
                      rw [hgoal, ha, hc, List.foldl_append, List.foldl_cons, List.foldl_nil]
                      dsimp only [evalV, step]
                      rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
                      simp only [eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true])
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil =>
        exact hpush (.inl false) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        cases l with
        | nil =>
          exact hpush (st.1.getD a (.inl false)) st.2 (Or.inl rfl) (hvalBdd a)
            (by simpa [eval_or] using htrAll a)
        | cons c l2 =>
          cases l2 with
          | nil =>
            have hgoal : GateOp.or.eval ([a, c].map fun i => orig.getD i false) =
                (evalV (st.2.foldl step (List.ofFn y)) (st.1.getD a (.inl false)) ||
                 evalV (st.2.foldl step (List.ofFn y)) (st.1.getD c (.inl false))) := by
              simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false,
                htrAll a, htrAll c]
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba =>
              cases ba with
              | true =>
                exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h)
                  (by rw [hgoal, ha]; rfl)
              | false =>
                exact hpush (st.1.getD c (.inl false)) st.2 (Or.inl rfl) (hvalBdd c)
                  (by rw [hgoal, ha]; simp only [evalV, Bool.false_or])
            | inr wa =>
              cases hc : st.1.getD c (.inl false) with
              | inl bc =>
                cases bc with
                | true =>
                  exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h)
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_true])
                | false =>
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj)) (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_false])
              | inr wc =>
                by_cases heq : wa = wc
                · subst heq; simp only [↓reduceIte]
                  exact hpush (.inr wa) st.2 (Or.inl rfl)
                    (fun j hj => hvalBdd a j (ha.trans hj))
                    (by rw [hgoal, ha, hc]; simp only [evalV, Bool.or_self])
                · simp only [heq, ↓reduceIte]
                  exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.or, [wa, wc]⟩]) (Or.inr ⟨_, rfl⟩)
                    (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                    (by
                      rw [hgoal, ha, hc, List.foldl_append, List.foldl_cons, List.foldl_nil]
                      dsimp only [evalV, step]
                      rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
                      simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false])
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil =>
        exact hpush (.inl true) st.2 (Or.inl rfl) (fun _ h => by cases h) rfl
      | cons a l =>
        have hgoal : GateOp.not.eval ((a :: l).map fun i => orig.getD i false) =
            !(evalV (st.2.foldl step (List.ofFn y)) (st.1.getD a (.inl false))) := by
          simp only [List.map_cons, eval_not, List.headD_cons, htrAll a]
        dsimp only [simpStep, simpGate]
        cases ha : st.1.getD a (.inl false) with
        | inl ba =>
          exact hpush (.inl (!ba)) st.2 (Or.inl rfl) (fun _ h => by cases h)
            (by rw [hgoal, ha])
        | inr wa =>
          exact hpush (.inr (n + st.2.length)) (st.2 ++ [⟨.not, [wa]⟩]) (Or.inr ⟨_, rfl⟩)
            (fun j hj => by cases hj; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            (by
              rw [hgoal, ha, List.foldl_append, List.foldl_cons, List.foldl_nil]
              dsimp only [evalV, step]
              rw [List.getD_append_right _ _ _ _ hwsLen.le, hwsLen, Nat.sub_self, List.getD_cons_zero]
              simp only [eval_not, List.map_cons, List.headD_cons])
  let isConst : List (Sum Bool ℕ) → ℕ → Bool := fun env i =>
    Sum.casesOn (env.getD i (.inl false)) (fun _ => true) (fun _ => false)
  have simpStep_dropConst : ∀ n st g i,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      rd g i = true → isConst st.1 i = true →
      (simpStep n st g).2.length = st.2.length := by
    intro n st g i hop hglen hrd hc
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_and] at hrd
            dsimp only [simpStep, simpGate]
            rcases hrd with rfl | rfl
            · cases ha : st.1.getD i (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
            · cases ha : st.1.getD a (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ =>
                cases hi : st.1.getD i (.inl false) with
                | inl bi => cases bi <;> rfl
                | inr _ => dsimp only [isConst] at hc; rw [hi] at hc; cases hc
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_or] at hrd
            dsimp only [simpStep, simpGate]
            rcases hrd with rfl | rfl
            · cases ha : st.1.getD i (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
            · cases ha : st.1.getD a (.inl false) with
              | inl ba => cases ba <;> rfl
              | inr _ =>
                cases hi : st.1.getD i (.inl false) with
                | inl bi => cases bi <;> rfl
                | inr _ => dsimp only [isConst] at hc; rw [hi] at hc; cases hc
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        simp [rd_not] at hrd
        subst hrd
        dsimp only [simpStep, simpGate]
        cases ha : st.1.getD i (.inl false) with
        | inl _ => rfl
        | inr _ => dsimp only [isConst] at hc; rw [ha] at hc; cases hc
  have simpStep_dropPair : ∀ n st g i j,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      rd g i = true → rd g j = true → i ≠ j →
      st.1.getD i (.inl false) = st.1.getD j (.inl false) →
      (simpStep n st g).2.length = st.2.length := by
    intro n st g i j hop hglen hrdi hrdj hne hsame
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_and] at hrdi hrdj
            have hac : st.1.getD a (.inl false) = st.1.getD c (.inl false) := by
              rcases hrdi with rfl | rfl <;> rcases hrdj with rfl | rfl
              · exact absurd rfl hne
              · exact hsame
              · exact hsame.symm
              · exact absurd rfl hne
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa =>
              have hc : st.1.getD c (.inl false) = .inr wa := hac.symm.trans ha
              rw [hc]
              simp only [↓reduceIte]
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        cases l with
        | nil => rfl
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_or] at hrdi hrdj
            have hac : st.1.getD a (.inl false) = st.1.getD c (.inl false) := by
              rcases hrdi with rfl | rfl <;> rcases hrdj with rfl | rfl
              · exact absurd rfl hne
              · exact hsame
              · exact hsame.symm
              · exact absurd rfl hne
            dsimp only [simpStep, simpGate]
            cases ha : st.1.getD a (.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa =>
              have hc : st.1.getD c (.inl false) = .inr wa := hac.symm.trans ha
              rw [hc]
              simp only [↓reduceIte]
          | cons _ _ => simp at hglen
    · cases inputs with
      | nil => rfl
      | cons a l =>
        simp [rd_not] at hrdi hrdj
        exact absurd (hrdi.trans hrdj.symm) hne
  have simpStep_makesConst : ∀ n st g i,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      rd g i = true → g.op.eval [true, false] = false →
      st.1.getD i (.inl false) = .inl false →
      isConst (simpStep n st g).1 st.1.length = true := by
    intro n st g i hop hglen hrd handnot hfalse
    have hlast : ∀ v, (st.1 ++ [v]).getD st.1.length (.inl false) = v := fun v => by
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rcases g with ⟨op, inputs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · cases inputs with
      | nil => dsimp only [simpStep, simpGate, isConst]; rw [hlast]
      | cons a l =>
        cases l with
        | nil =>
          simp [rd_and] at hrd
          subst hrd
          dsimp only [simpStep, simpGate, isConst]
          rw [hlast, hfalse]
        | cons c l2 =>
          cases l2 with
          | nil =>
            simp [rd_and] at hrd
            dsimp only [simpStep, simpGate, isConst]
            rw [hlast]
            rcases hrd with rfl | rfl
            · rw [hfalse]
            · cases st.1.getD a (.inl false) with
              | inl ba =>
                cases ba with
                | false => rfl
                | true => rw [hfalse]
              | inr _ => rw [hfalse]
          | cons _ _ => simp at hglen
    · rw [eval_or] at handnot; cases handnot
    · cases inputs with
      | nil => dsimp only [simpStep, simpGate, isConst]; rw [hlast]
      | cons a l =>
        simp [rd_not] at hrd
        subst hrd
        dsimp only [simpStep, simpGate, isConst]
        rw [hlast, hfalse]
  have simpRun_all : ∀ (n : ℕ) (gs : List Gate) (st : List (Sum Bool ℕ) × List Gate)
      (target : (Fin n → Bool) → Bool) (xOf : (Fin n → Bool) → (Fin 10 → Bool)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      FanInTwo ⟨st.2, 0⟩ →
      st.1.length = 11 →
      (∀ s ∈ st.1, ∀ j, s = .inr j → j < n + st.2.length) →
      (∀ y : Fin n → Bool, ∀ i < 11,
        evalV (st.2.foldl step (List.ofFn y)) (st.1.getD i (.inl false)) = (seed (xOf y)).getD i false) →
      (∀ y : Fin n → Bool, fP (xOf y) = target y) →
      target (fun _ => false) = false →
      gs = D.gates →
      let fin := simpStep n (gs.foldl (simpStep n) st) ⟨.and, [u, 10 + D.size]⟩
      HasCircuitSize n target fin.2.length := by
    intro n gs st target xOf hgsfan hstfan hstlen hstbdd hsttr htar htar0 hgsEq
    have hfold : ∀ (ls : List Gate) (s0 : List (Sum Bool ℕ) × List Gate),
        (∀ g ∈ ls, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        FanInTwo ⟨s0.2, 0⟩ →
        (∀ s ∈ s0.1, ∀ j, s = .inr j → j < n + s0.2.length) →
        ∀ (y : Fin n → Bool) (orig : List Bool),
        orig.length = s0.1.length →
        (∀ i < s0.1.length, evalV (s0.2.foldl step (List.ofFn y)) (s0.1.getD i (.inl false)) = orig.getD i false) →
        let sf := ls.foldl (simpStep n) s0
        FanInTwo ⟨sf.2, 0⟩ ∧
        sf.1.length = s0.1.length + ls.length ∧
        (∀ s ∈ sf.1, ∀ j, s = .inr j → j < n + sf.2.length) ∧
        (∀ i < sf.1.length, evalV (sf.2.foldl step (List.ofFn y)) (sf.1.getD i (.inl false)) = (ls.foldl step orig).getD i false) := by
      intro ls
      induction ls with
      | nil =>
        intro s0 _ hf hb y orig _ ht
        exact ⟨hf, by simp, hb, ht⟩
      | cons g ls ih =>
        intro s0 hlf hf hb y orig hlen ht
        obtain ⟨hop, hgl⟩ := hlf g List.mem_cons_self
        have hf1 := simpStep_fan n s0 g hf
        obtain ⟨hb1, ht1⟩ := simpStep_sound n s0 g y orig hop hgl hlen hb ht
        have hlen1 : (step orig g).length = (simpStep n s0 g).1.length := by
          simp [step, simpStep_envLen, hlen]
        obtain ⟨hf2, hlen2, hb2, ht2⟩ :=
          ih (simpStep n s0 g) (fun h hh => hlf h (List.mem_cons_of_mem _ hh)) hf1 hb1 y (step orig g) hlen1 ht1
        refine ⟨hf2, ?_, hb2, ht2⟩
        rw [List.foldl_cons, hlen2, simpStep_envLen]
        simp; omega
    let mid := gs.foldl (simpStep n) st
    let fin := simpStep n mid ⟨.and, [u, 10 + D.size]⟩
    have hmid0 := hfold gs st hgsfan hstfan hstbdd (fun _ => false) (seed (xOf (fun _ => false)))
      (by rw [seedLen, hstlen]) (by rw [hstlen]; exact hsttr (fun _ => false))
    have hfinFan : FanInTwo ⟨fin.2, 0⟩ := simpStep_fan n mid ⟨.and, [u, 10 + D.size]⟩ hmid0.1
    have hfinEval : ∀ y : Fin n → Bool,
        evalV (fin.2.foldl step (List.ofFn y)) (fin.1.getD (11 + D.size) (.inl false)) = target y := by
      intro y
      have hmy := hfold gs st hgsfan hstfan hstbdd y (seed (xOf y))
        (by rw [seedLen, hstlen]) (by rw [hstlen]; exact hsttr y)
      obtain ⟨_, hfy⟩ := simpStep_sound n mid ⟨.and, [u, 10 + D.size]⟩ y (gs.foldl step (seed (xOf y)))
        (by simp) (by simp) (by rw [runLen, seedLen, hmy.2.1, hstlen]) hmy.2.2.1 hmy.2.2.2
      have hidx : 11 + D.size < fin.1.length := by
        have hfl : fin.1.length = mid.1.length + 1 := simpStep_envLen n mid ⟨.and, [u, 10 + D.size]⟩
        rw [hfl, hmy.2.1, hstlen, hgsEq]
        change 11 + D.gates.length < 11 + D.gates.length + 1; omega
      have h1 := hfy (11 + D.size) hidx
      have horigLen : (gs.foldl step (seed (xOf y))).length = 11 + D.size := by
        rw [runLen, seedLen, hgsEq]; rfl
      dsimp only [step] at h1
      rw [List.getD_append_right _ _ _ _ horigLen.le, horigLen, Nat.sub_self, List.getD_cons_zero] at h1
      rw [h1]
      change ((gs.foldl step (seed (xOf y))).getD u false &&
        ((gs.foldl step (seed (xOf y))).getD (10 + D.size) false && true)) = target y
      rw [Bool.and_true, hgsEq]
      exact (exactD (xOf y)).trans (htar y)
    cases hout : fin.1.getD (11 + D.size) (.inl false) with
    | inl c =>
      cases c with
      | true =>
        have hbad := hfinEval (fun _ => false)
        rw [hout, htar0] at hbad
        cases hbad
      | false =>
        refine ⟨⟨[], n⟩, (fun _ h => by cases h), Nat.zero_le _, fun y => ?_⟩
        have hy := hfinEval y
        rw [hout] at hy
        dsimp only [evalV] at hy
        rw [eval_nil, List.getD_eq_default _ _ (by simp)]
        exact hy
    | inr wOut =>
      refine ⟨⟨fin.2, wOut⟩, hfinFan, le_rfl, fun y => ?_⟩
      have hy := hfinEval y
      rw [hout] at hy
      exact hy
  have countFold : ∀ (n : ℕ) (P : Gate → Bool) (gs : List Gate) (s0 : List (Sum Bool ℕ) × List Gate),
      (∀ g s, g ∈ gs → s.1.length ≥ s0.1.length →
        (∀ i < s0.1.length, s.1.getD i (.inl false) = s0.1.getD i (.inl false)) →
        P g = true → (simpStep n s g).2.length = s.2.length) →
      (gs.foldl (simpStep n) s0).2.length + gs.countP P ≤ s0.2.length + gs.length := by
    intro n P gs
    induction gs with
    | nil => intro s0 _; simp
    | cons g gs ih =>
      intro s0 hdrop
      rw [List.foldl_cons, List.countP_cons, List.length_cons]
      have h1 : (gs.foldl (simpStep n) (simpStep n s0 g)).2.length + gs.countP P ≤
          (simpStep n s0 g).2.length + gs.length := by
        apply ih (simpStep n s0 g)
        intro g' s hg' hlen' hpref' hP'
        apply hdrop g' s (List.mem_cons_of_mem _ hg') (by rw [simpStep_envLen] at hlen'; omega)
        · intro i hi
          rw [hpref' i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s0 g i hi]
        · exact hP'
      cases hPg : P g with
      | true =>
        have h0 := hdrop g s0 List.mem_cons_self le_rfl (fun _ _ => rfl) hPg
        simp only [h0, ↓reduceIte] at h1 ⊢
        omega
      | false =>
        have h0 := simpStep_lenLe n s0 g
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
  have countFoldCascade : ∀ (n : ℕ) (q : ℕ) (a : List Gate) (g0 : Gate) (c : List Gate)
      (s0 : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ a ++ g0 :: c, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      s0.1.length = 11 → q < 11 → s0.1.getD q (.inl false) = .inl false →
      rd g0 q = true → g0.op.eval [true, false] = false →
      ((a ++ g0 :: c).foldl (simpStep n) s0).2.length +
        (a ++ g0 :: c).countP (fun h => rd h q || rd h (11 + a.length)) ≤
        s0.2.length + (a ++ g0 :: c).length := by
    intro n q a g0 c s0 hfanAll hlen0 hq11 hsq hrd0 hnotor
    rw [List.foldl_append, List.foldl_cons, List.countP_append, List.countP_cons, List.length_append, List.length_cons]
    have hpre : ∀ (ls : List Gate) (s : List (Sum Bool ℕ) × List Gate),
        (ls.foldl (simpStep n) s).1.length = s.1.length + ls.length ∧
        ∀ i < s.1.length, (ls.foldl (simpStep n) s).1.getD i (.inl false) = s.1.getD i (.inl false) := by
      intro ls
      induction ls with
      | nil => intro s; exact ⟨by simp, fun _ _ => rfl⟩
      | cons g ls ih =>
        intro s
        rw [List.foldl_cons]
        obtain ⟨hl, hp⟩ := ih (simpStep n s g)
        refine ⟨by rw [hl, simpStep_envLen]; simp; omega, fun i hi => ?_⟩
        rw [hp i (by rw [simpStep_envLen]; omega), simpStep_envPrefix n s g i hi]
    have hA : (a.foldl (simpStep n) s0).2.length + a.countP (fun h => rd h q || rd h (11 + a.length)) ≤
        s0.2.length + a.length := by
      have hgen : ∀ (k : ℕ) (ls : List Gate) (s : List (Sum Bool ℕ) × List Gate),
          (∀ g ∈ ls, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
          s.1.length + ls.length ≤ k → q < s.1.length → s.1.getD q (.inl false) = .inl false →
          (ls.foldl (simpStep n) s).2.length + ls.countP (fun h => rd h q || rd h k) ≤ s.2.length + ls.length := by
        intro k ls
        induction ls with
        | nil => intro s _ _ _ _; simp
        | cons g ls ih =>
          intro s hlf hle hqs hsq'
          rw [List.foldl_cons, List.countP_cons, List.length_cons]
          have h1 := ih (simpStep n s g) (fun h hh => hlf h (List.mem_cons_of_mem _ hh))
            (by rw [simpStep_envLen]; simp at hle; omega) (by rw [simpStep_envLen]; omega)
            (by rw [simpStep_envPrefix n s g q hqs]; exact hsq')
          cases hP : (rd g q || rd g k) with
          | true =>
            obtain ⟨hop, hgl⟩ := hlf g List.mem_cons_self
            have hd : (simpStep n s g).2.length = s.2.length := by
              rcases Bool.or_eq_true_iff.mp hP with h1' | h2'
              · exact simpStep_dropConst n s g q hop hgl h1' (by dsimp only [isConst]; rw [hsq'])
              · have hkge : s.1.length ≤ k := by simp at hle; omega
                exact simpStep_dropConst n s g k hop hgl h2'
                  (by dsimp only [isConst]; rw [List.getD_eq_default _ _ hkge])
            simp only [hd, ↓reduceIte] at h1 ⊢
            omega
          | false =>
            have h0 := simpStep_lenLe n s g
            simp only [Bool.false_eq_true, ↓reduceIte]
            omega
      exact hgen (11 + a.length) a s0 (fun g hg => hfanAll g (List.mem_append_left _ hg)) (by omega) (by omega) hsq
    let s1 := a.foldl (simpStep n) s0
    have hs1Len : s1.1.length = 11 + a.length := by rw [(hpre a s0).1, hlen0]
    have hs1q : s1.1.getD q (.inl false) = .inl false := by rw [(hpre a s0).2 q (by omega), hsq]
    obtain ⟨hop0, hgl0⟩ := hfanAll g0 (List.mem_append_right _ List.mem_cons_self)
    have hg0Drop : (simpStep n s1 g0).2.length = s1.2.length :=
      simpStep_dropConst n s1 g0 q hop0 hgl0 hrd0 (by dsimp only [isConst]; rw [hs1q])
    have hg0Const : isConst (simpStep n s1 g0).1 (11 + a.length) = true := by
      rw [← hs1Len]
      exact simpStep_makesConst n s1 g0 q hop0 hgl0 hrd0 hnotor hs1q
    have hs2q : (simpStep n s1 g0).1.getD q (.inl false) = .inl false := by
      rw [simpStep_envPrefix n s1 g0 q (by omega), hs1q]
    have hC : (c.foldl (simpStep n) (simpStep n s1 g0)).2.length +
        c.countP (fun h => rd h q || rd h (11 + a.length)) ≤
        (simpStep n s1 g0).2.length + c.length := by
      apply countFold n (fun h => rd h q || rd h (11 + a.length)) c (simpStep n s1 g0)
      intro g s hg _ hpref hP
      obtain ⟨hop, hgl⟩ := hfanAll g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
      rcases Bool.or_eq_true_iff.mp hP with h1' | h2'
      · exact simpStep_dropConst n s g q hop hgl h1'
          (by dsimp only [isConst]; rw [hpref q (by rw [simpStep_envLen, hs1Len]; omega), hs2q])
      · exact simpStep_dropConst n s g (11 + a.length) hop hgl h2'
          (by
            have hlt : 11 + a.length < (simpStep n s1 g0).1.length := by rw [simpStep_envLen, hs1Len]; omega
            dsimp only [isConst]
            rw [hpref (11 + a.length) hlt]
            exact hg0Const)
    have hPg0 : (rd g0 q || rd g0 (11 + a.length)) = true := by simp [hrd0]
    simp only [hPg0, ↓reduceIte]
    dsimp only [s1] at hg0Drop hC
    omega
  let f670 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have f670Zero : f670 (fun _ => false) = false := by decide
  let aut9 : Fin 10 → Fin 10 → Fin 10 := fun k i =>
    Fin.ofNat 10 ((([[9,4,0,1,6,7,3,5,2,8], [4,9,6,1,0,3,7,8,2,5], [0,4,9,6,1,5,3,7,8,2],
      [0,1,6,9,4,5,2,8,7,3], [4,0,1,6,9,3,5,2,8,7], [4,0,1,2,3,9,5,6,7,8],
      [0,4,3,2,1,5,9,8,7,6], [0,1,6,8,5,4,2,9,3,7], [0,1,2,7,5,4,6,3,9,8],
      [0,1,2,3,4,5,6,7,8,9]] : List (List ℕ)).getD k.val []).getD i.val 0)
  let inv9 : Fin 10 → Fin 10 → Fin 10 := fun k i =>
    Fin.ofNat 10 ((([[2,3,8,6,1,7,4,5,9,0], [4,3,8,5,0,9,2,6,7,1], [0,4,9,6,1,5,3,7,8,2],
      [0,1,6,9,4,5,2,8,7,3], [1,2,7,5,0,6,3,9,8,4], [1,2,3,4,0,6,7,8,9,5],
      [0,4,3,2,1,5,9,8,7,6], [0,1,6,8,5,4,2,9,3,7], [0,1,2,7,5,4,6,3,9,8],
      [0,1,2,3,4,5,6,7,8,9]] : List (List ℕ)).getD k.val []).getD i.val 0)
  let edges10 : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let pAdj : Fin 10 → Fin 10 → Bool := fun i j =>
    edges10.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)
  have aut9Fix : ∀ k : Fin 10, aut9 k k = 9 := by decide
  have aut9Left : ∀ k i : Fin 10, inv9 k (aut9 k i) = i := by decide
  have aut9Right : ∀ k i : Fin 10, aut9 k (inv9 k i) = i := by decide
  have aut9Inj : ∀ k i j : Fin 10, aut9 k i = aut9 k j → i = j := fun k i j h => by
    rw [← aut9Left k i, h, aut9Left k j]
  have aut9Surj : ∀ k j : Fin 10, ∃ i : Fin 10, aut9 k i = j := fun k j => ⟨inv9 k j, aut9Right k j⟩
  have pAdjSymm : ∀ i j : Fin 10, pAdj i j = pAdj j i := by
    intro i j
    dsimp only [pAdj]
    congr 1; funext e; simp only [Bool.or_comm]
  have aut9Edge : ∀ k : Fin 10, ∀ e ∈ edges10, pAdj (aut9 k e.1) (aut9 k e.2) = true := by decide
  have inv9Edge : ∀ k : Fin 10, ∀ e ∈ edges10, pAdj (inv9 k e.1) (inv9 k e.2) = true := by decide
  have aut9Adj : ∀ k i j : Fin 10, pAdj (aut9 k i) (aut9 k j) = pAdj i j := by
    intro k i j
    have hdir : ∀ (fn : Fin 10 → Fin 10), (∀ e ∈ edges10, pAdj (fn e.1) (fn e.2) = true) →
        ∀ a c : Fin 10, pAdj a c = true → pAdj (fn a) (fn c) = true := by
      intro fn hfn a c hac
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hac
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfn e he
      · rw [pAdjSymm]; exact hfn e he
    have hiff : pAdj (aut9 k i) (aut9 k j) = true ↔ pAdj i j = true := by
      constructor
      · intro h
        have h' := hdir (inv9 k) (inv9Edge k) (aut9 k i) (aut9 k j) h
        rwa [aut9Left, aut9Left] at h'
      · exact hdir (aut9 k) (aut9Edge k) i j
    exact Bool.eq_iff_iff.mpr hiff
  have fP_iff : ∀ x : Fin 10 → Bool, fP x = true ↔ ∃ i j : Fin 10, pAdj i j = true ∧ x i = true ∧ x j = true := by
    intro x
    have hlist : fP x = edges10.any (fun e => x e.1 && x e.2) := by
      change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) =
        ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) ||
        ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) ||
        ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
      simp only [Bool.or_false, Bool.or_assoc]
    rw [hlist, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hxy⟩
      simp only [Bool.and_eq_true] at hxy
      exact ⟨e.1, e.2, List.any_eq_true.mpr ⟨e, he, by simp⟩, hxy.1, hxy.2⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hij
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e, he, by simp [hi, hj]⟩
      · exact ⟨e, he, by simp [hi, hj]⟩
  let edges9 : List (Fin 9 × Fin 9) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  have f670_iff : ∀ y : Fin 9 → Bool, f670 y = true ↔
      ∃ i j : Fin 9, pAdj (Fin.castSucc i) (Fin.castSucc j) = true ∧ y i = true ∧ y j = true := by
    intro y
    have hlist : f670 y = edges9.any (fun e => y e.1 && y e.2) := by
      change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) ||
        (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
        (y 6 && y 8) || (y 8 && y 5)) =
        ((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 3 && y 4) || ((y 4 && y 0) ||
        ((y 0 && y 5) || ((y 1 && y 6) || ((y 2 && y 7) || ((y 3 && y 8) || ((y 5 && y 7) ||
        ((y 6 && y 8) || ((y 8 && y 5) || false))))))))))))
      simp only [Bool.or_false, Bool.or_assoc]
    rw [hlist, List.any_eq_true]
    constructor
    · rintro ⟨e, he, hxy⟩
      simp only [Bool.and_eq_true] at hxy
      have hp : ∀ e' ∈ edges9, pAdj (Fin.castSucc e'.1) (Fin.castSucc e'.2) = true := by decide
      exact ⟨e.1, e.2, hp e he, hxy.1, hxy.2⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨e, he, hm⟩ := List.any_eq_true.mp hij
      have h10to9 : ∀ e' ∈ edges10, e'.1 = 9 ∨ e'.2 = 9 ∨
          edges9.any (fun d => Fin.castSucc d.1 == e'.1 && Fin.castSucc d.2 == e'.2) = true := by decide
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      have hne9 : ∀ k : Fin 9, Fin.castSucc k ≠ (9 : Fin 10) := fun k hk => by
        have := congrArg Fin.val hk; simp at this; omega
      have hhas : edges9.any (fun d => Fin.castSucc d.1 == e.1 && Fin.castSucc d.2 == e.2) = true := by
        rcases h10to9 e he with h1 | h2 | h3
        · rcases hm with ⟨h1', _⟩ | ⟨h1', _⟩
          · exact absurd (h1'.symm.trans h1) (hne9 i)
          · exact absurd (h1'.symm.trans h1) (hne9 j)
        · rcases hm with ⟨_, h2'⟩ | ⟨_, h2'⟩
          · exact absurd (h2'.symm.trans h2) (hne9 j)
          · exact absurd (h2'.symm.trans h2) (hne9 i)
        · exact h3
      obtain ⟨d, hd, hdm⟩ := List.any_eq_true.mp hhas
      simp only [Bool.and_eq_true, beq_iff_eq] at hdm
      refine ⟨d, hd, ?_⟩
      rcases hm with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · have hd1 : d.1 = i := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.1.trans h1'))
        have hd2 : d.2 = j := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.2.trans h2'))
        simp [hd1, hd2, hi, hj]
      · have hd1 : d.1 = j := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.1.trans h1'))
        have hd2 : d.2 = i := Fin.ext (congrArg (Fin.val : Fin 10 → ℕ) (hdm.2.trans h2'))
        simp [hd1, hd2, hi, hj]
  have aut9Match : ∀ (k : Fin 10) (y : Fin 9 → Bool),
      fP (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)) = f670 y := by
    intro k y
    have hiff : fP (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)) = true ↔ f670 y = true := by
      rw [fP_iff (fun i : Fin 10 => if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)), f670_iff y]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        have hik : i ≠ k := by intro h; simp [h] at hi
        have hjk : j ≠ k := by intro h; simp [h] at hj
        have hi9 : (aut9 k i).val < 9 := by
          have hne : aut9 k i ≠ 9 := fun h => hik (aut9Inj k i k (h.trans (aut9Fix k).symm))
          have hlt := (aut9 k i).isLt
          have : (aut9 k i).val ≠ 9 := fun hv => hne (Fin.ext hv)
          omega
        have hj9 : (aut9 k j).val < 9 := by
          have hne : aut9 k j ≠ 9 := fun h => hjk (aut9Inj k j k (h.trans (aut9Fix k).symm))
          have hlt := (aut9 k j).isLt
          have : (aut9 k j).val ≠ 9 := fun hv => hne (Fin.ext hv)
          omega
        refine ⟨⟨(aut9 k i).val, hi9⟩, ⟨(aut9 k j).val, hj9⟩, ?_, ?_, ?_⟩
        · have hci : Fin.castSucc (⟨(aut9 k i).val, hi9⟩ : Fin 9) = aut9 k i := Fin.ext rfl
          have hcj : Fin.castSucc (⟨(aut9 k j).val, hj9⟩ : Fin 9) = aut9 k j := Fin.ext rfl
          rw [hci, hcj, aut9Adj]; exact hij
        · simpa [hik, Fin.ofNat, Nat.mod_eq_of_lt hi9] using hi
        · simpa [hjk, Fin.ofNat, Nat.mod_eq_of_lt hj9] using hj
      · rintro ⟨i, j, hij, hi, hj⟩
        obtain ⟨a, ha⟩ := aut9Surj k (Fin.castSucc i)
        obtain ⟨c, hc⟩ := aut9Surj k (Fin.castSucc j)
        have hak : a ≠ k := by
          intro h; subst h; rw [aut9Fix] at ha
          have : i.val = 9 := (congrArg Fin.val ha).symm
          omega
        have hck : c ≠ k := by
          intro h; subst h; rw [aut9Fix] at hc
          have : j.val = 9 := (congrArg Fin.val hc).symm
          omega
        refine ⟨a, c, ?_, ?_, ?_⟩
        · rw [← aut9Adj k, ha, hc]; exact hij
        · simp only [hak, ↓reduceIte, ha, Fin.val_castSucc]
          have : Fin.ofNat 9 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
          rw [this]; exact hi
        · simp only [hck, ↓reduceIte, hc, Fin.val_castSucc]
          have : Fin.ofNat 9 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
          rw [this]; exact hj
    exact Bool.eq_iff_iff.mpr hiff
  have elimEnd : ∀ (q r : Fin 10), (q = 0 ∧ r = pFin) ∨ (q = pFin ∧ r = 0) →
      D.gates.countP (fun g => rd g q.val || (rd g r.val && rd g 10)) + 15 ≤ D.size ∧
      (∀ a g c, D.gates = a ++ g :: c → rd g q.val = true → g.op.eval [true, false] = false →
        D.gates.countP (fun h => rd h q.val || rd h (11 + a.length)) + 15 ≤ D.size) := by
    intro q r hqr
    have hne : q ≠ r := by
      rcases hqr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> decide
    have hr9 : (aut9 q r).val < 9 := by
      have hne9 : aut9 q r ≠ 9 := fun h => hne (aut9Inj q r q (h.trans (aut9Fix q).symm)).symm
      have hlt := (aut9 q r).isLt
      have : (aut9 q r).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
      omega
    let xOf : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
      if i = q then false else y (Fin.ofNat 9 (aut9 q i).val)
    let env0 : List (Sum Bool ℕ) :=
      (List.finRange 10).map (fun i : Fin 10 => if i = q then .inl false else .inr (aut9 q i).val) ++
      [.inr (aut9 q r).val]
    have henv0Len : env0.length = 11 := by simp [env0]
    have henv0Bdd : ∀ s ∈ env0, ∀ j, s = .inr j → j < 9 + ([] : List Gate).length := by
      intro s hs j hj
      simp only [env0, List.mem_append, List.mem_map, List.mem_finRange, true_and, List.mem_singleton] at hs
      rcases hs with ⟨i, hi⟩ | hs
      · by_cases hiq : i = q
        · simp [hiq] at hi; rw [← hi] at hj; cases hj
        · simp [hiq] at hi; rw [← hi] at hj; cases hj
          have hne9 : aut9 q i ≠ 9 := fun h => hiq (aut9Inj q i q (h.trans (aut9Fix q).symm))
          have hlt := (aut9 q i).isLt
          have : (aut9 q i).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
          simp; omega
      · rw [hs] at hj; cases hj; simp; exact hr9
    have henv0Tr : ∀ y : Fin 9 → Bool, ∀ i < 11,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (env0.getD i (.inl false)) = (seed (xOf y)).getD i false := by
      intro y i hi
      by_cases h10 : i < 10
      · have hl1 : i < ((List.finRange 10).map (fun k : Fin 10 => if k = q then Sum.inl false else .inr (aut9 q k).val)).length := by simp [h10]
        have hl2 : i < (List.ofFn (xOf y)).length := by simp [h10]
        simp only [env0, seed, List.foldl_nil]
        rw [List.getD_append _ _ _ _ hl1, List.getD_append _ _ _ _ hl2,
            List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2]
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_ofFn, xOf]
        by_cases hiq : (⟨i, h10⟩ : Fin 10) = q
        · simp [hiq, evalV]
        · have hlt9 : (aut9 q ⟨i, h10⟩).val < 9 := by
            have hne9 : aut9 q ⟨i, h10⟩ ≠ 9 := fun h => hiq (aut9Inj q ⟨i, h10⟩ q (h.trans (aut9Fix q).symm))
            have hlt := (aut9 q ⟨i, h10⟩).isLt
            have : (aut9 q ⟨i, h10⟩).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
            omega
          simp only [Fin.cast_mk, hiq, ↓reduceIte, evalV]
          rw [List.getD_eq_getElem _ _ (by simp [hlt9]), List.getElem_ofFn]
          congr 1
          exact Fin.ext (Nat.mod_eq_of_lt hlt9).symm
      · have hi10 : i = 10 := by omega
        subst hi10
        simp only [env0, seed, List.foldl_nil]
        rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_map, List.length_finRange, List.length_ofFn, Nat.sub_self, List.getD_cons_zero, evalV]
        rw [List.getD_eq_getElem _ _ (by simp [hr9]), List.getElem_ofFn]
        rcases hqr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [xOf, ↓reduceIte, Bool.false_or, hne.symm]
          congr 1; exact Fin.ext (Nat.mod_eq_of_lt hr9).symm
        · simp only [xOf, ↓reduceIte, Bool.or_false, hne.symm]
          congr 1; exact Fin.ext (Nat.mod_eq_of_lt hr9).symm
    have henv0q : env0.getD q.val (.inl false) = .inl false := by
      have hl1 : q.val < ((List.finRange 10).map (fun k : Fin 10 => if k = q then Sum.inl false else .inr (aut9 q k).val)).length := by simp [q.isLt]
      simp only [env0]
      rw [List.getD_append _ _ _ _ hl1, List.getD_eq_getElem _ _ hl1]
      simp
    have henv0r : env0.getD r.val (.inl false) = .inr (aut9 q r).val := by
      have hl1 : r.val < ((List.finRange 10).map (fun k : Fin 10 => if k = q then Sum.inl false else .inr (aut9 q k).val)).length := by simp [r.isLt]
      simp only [env0]
      rw [List.getD_append _ _ _ _ hl1, List.getD_eq_getElem _ _ hl1]
      simp [hne.symm]
    have henv010 : env0.getD 10 (.inl false) = .inr (aut9 q r).val := by
      simp only [env0]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have hcirc : HasCircuitSize 9 f670 (simpStep 9 (D.gates.foldl (simpStep 9) (env0, [])) ⟨.and, [u, 10 + D.size]⟩).2.length :=
      simpRun_all 9 D.gates (env0, []) f670 xOf hDfan (fun _ h => by cases h) henv0Len henv0Bdd henv0Tr
        (fun y => aut9Match q y) f670Zero rfl
    have hge16 : 16 ≤ (simpStep 9 (D.gates.foldl (simpStep 9) (env0, [])) ⟨.and, [u, 10 + D.size]⟩).2.length := by
      by_contra! hle15
      obtain ⟨C, hCf, hCs, hCe⟩ := hcirc
      exact h670 ⟨C, hCf, by omega, hCe⟩
    have hmid15 : 15 ≤ (D.gates.foldl (simpStep 9) (env0, [])).2.length := by
      have htop := simpStep_lenLe 9 (D.gates.foldl (simpStep 9) (env0, [])) ⟨.and, [u, 10 + D.size]⟩
      omega
    constructor
    · have hcnt := countFold 9 (fun g => rd g q.val || (rd g r.val && rd g 10)) D.gates (env0, [])
        (fun g s hg _ hpref hP => by
          obtain ⟨hop, hgl⟩ := hDfan g hg
          rcases Bool.or_eq_true_iff.mp hP with h1 | h2
          · exact simpStep_dropConst 9 s g q.val hop hgl h1
              (by dsimp only [isConst]; rw [hpref q.val (by rw [henv0Len]; omega), henv0q])
          · obtain ⟨hr1, hr2⟩ := Bool.and_eq_true_iff.mp h2
            exact simpStep_dropPair 9 s g r.val 10 hop hgl hr1 hr2 (by omega)
              (by rw [hpref r.val (by rw [henv0Len]; omega), hpref 10 (by rw [henv0Len]; omega), henv0r, henv010]))
      simp only [List.length_nil, zero_add] at hcnt
      change D.gates.countP _ + 15 ≤ D.gates.length
      omega
    · intro a g c hsplit hrdg hnotor
      have hcnt := countFoldCascade 9 q.val a g c (env0, []) (by rw [← hsplit]; exact hDfan)
        henv0Len (by omega) henv0q hrdg hnotor
      rw [← hsplit] at hcnt
      simp only [List.length_nil, zero_add] at hcnt
      change D.gates.countP _ + 15 ≤ D.gates.length
      omega
  have elimAny : ∀ k : Fin 10, D.gates.countP (fun g => rd g k.val) + 14 ≤ D.size := by
    intro k
    by_cases hkq : k = 0 ∨ k = pFin
    · rcases hkq with rfl | rfl
      · have h1 := (elimEnd 0 pFin (Or.inl ⟨rfl, rfl⟩)).1
        simp only [Fin.val_zero] at h1
        have hle : D.gates.countP (fun g => rd g 0) ≤
            D.gates.countP (fun g => rd g 0 || (rd g pFin.val && rd g 10)) :=
          List.countP_mono_left fun g _ h => by simp [h]
        change D.gates.countP _ + 14 ≤ D.size
        simp only [Fin.val_zero]
        omega
      · have h1 := (elimEnd pFin 0 (Or.inr ⟨rfl, rfl⟩)).1
        simp only [Fin.val_zero] at h1
        have hle : D.gates.countP (fun g => rd g pFin.val) ≤
            D.gates.countP (fun g => rd g pFin.val || (rd g 0 && rd g 10)) :=
          List.countP_mono_left fun g _ h => by simp [h]
        omega
    · push Not at hkq
      obtain ⟨hk0, hkp⟩ := hkq
      have h0lt : (aut9 k 0).val < 9 := by
        have hne9 : aut9 k 0 ≠ 9 := fun h => hk0.symm (aut9Inj k 0 k (h.trans (aut9Fix k).symm))
        have hlt := (aut9 k 0).isLt
        have : (aut9 k 0).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
        omega
      have hplt : (aut9 k pFin).val < 9 := by
        have hne9 : aut9 k pFin ≠ 9 := fun h => hkp.symm (aut9Inj k pFin k (h.trans (aut9Fix k).symm))
        have hlt := (aut9 k pFin).isLt
        have : (aut9 k pFin).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
        omega
      let xOf : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
        if i = k then false else y (Fin.ofNat 9 (aut9 k i).val)
      let gFirst : Gate := ⟨.or, [(aut9 k 0).val, (aut9 k pFin).val]⟩
      let env0 : List (Sum Bool ℕ) :=
        (List.finRange 10).map (fun i : Fin 10 => if i = k then .inl false else .inr (aut9 k i).val) ++ [.inr 9]
      have henv0Len : env0.length = 11 := by simp [env0]
      have haccFan : FanInTwo ⟨[gFirst], 0⟩ := by
        intro g hg; obtain rfl := List.mem_singleton.mp hg; exact ⟨by simp [gFirst], by simp [gFirst]⟩
      have henv0Bdd : ∀ s ∈ env0, ∀ j, s = .inr j → j < 9 + ([gFirst] : List Gate).length := by
        intro s hs j hj
        simp only [env0, List.mem_append, List.mem_map, List.mem_finRange, true_and, List.mem_singleton] at hs
        rcases hs with ⟨i, hi⟩ | hs
        · by_cases hik : i = k
          · simp [hik] at hi; rw [← hi] at hj; cases hj
          · simp [hik] at hi; rw [← hi] at hj; cases hj
            have hlt := (aut9 k i).isLt
            simp
        · rw [hs] at hj; cases hj; simp
      have henv0Tr : ∀ y : Fin 9 → Bool, ∀ i < 11,
          evalV (([gFirst] : List Gate).foldl step (List.ofFn y)) (env0.getD i (.inl false)) = (seed (xOf y)).getD i false := by
        intro y i hi
        have hrun1 : ([gFirst] : List Gate).foldl step (List.ofFn y) =
            List.ofFn y ++ [y (Fin.ofNat 9 (aut9 k 0).val) || y (Fin.ofNat 9 (aut9 k pFin).val)] := by
          simp only [List.foldl_cons, List.foldl_nil, step, gFirst, eval_or, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          have hget0 : (List.ofFn y).getD (aut9 k 0).val false = y ⟨(aut9 k 0).val, h0lt⟩ := by
            rw [List.getD_eq_getElem _ _ (by simp [h0lt]), List.getElem_ofFn]
          have hgetp : (List.ofFn y).getD (aut9 k pFin).val false = y ⟨(aut9 k pFin).val, hplt⟩ := by
            rw [List.getD_eq_getElem _ _ (by simp [hplt]), List.getElem_ofFn]
          rw [hget0, hgetp]
          have h0f : (⟨(aut9 k 0).val, h0lt⟩ : Fin 9) = Fin.ofNat 9 (aut9 k 0).val :=
            Fin.ext (Nat.mod_eq_of_lt h0lt).symm
          have hpf : (⟨(aut9 k pFin).val, hplt⟩ : Fin 9) = Fin.ofNat 9 (aut9 k pFin).val :=
            Fin.ext (Nat.mod_eq_of_lt hplt).symm
          rw [h0f, hpf]
        by_cases h10 : i < 10
        · have hl1 : i < ((List.finRange 10).map (fun m : Fin 10 => if m = k then Sum.inl false else .inr (aut9 k m).val)).length := by simp [h10]
          have hl2 : i < (List.ofFn (xOf y)).length := by simp [h10]
          simp only [env0, seed]
          rw [List.getD_append _ _ _ _ hl1, List.getD_append _ _ _ _ hl2,
              List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2]
          simp only [List.getElem_map, List.getElem_finRange, List.getElem_ofFn, xOf]
          by_cases hik : (⟨i, h10⟩ : Fin 10) = k
          · simp [hik, evalV]
          · have hlt9 : (aut9 k ⟨i, h10⟩).val < 9 := by
              have hne9 : aut9 k ⟨i, h10⟩ ≠ 9 := fun h => hik (aut9Inj k ⟨i, h10⟩ k (h.trans (aut9Fix k).symm))
              have hlt := (aut9 k ⟨i, h10⟩).isLt
              have : (aut9 k ⟨i, h10⟩).val ≠ 9 := fun hv => hne9 (Fin.ext hv)
              omega
            simp only [Fin.cast_mk, hik, ↓reduceIte, evalV]
            rw [hrun1, List.getD_append _ _ _ _ (by simp [hlt9]), List.getD_eq_getElem _ _ (by simp [hlt9]), List.getElem_ofFn]
            congr 1; exact Fin.ext (Nat.mod_eq_of_lt hlt9).symm
        · have hi10 : i = 10 := by omega
          subst hi10
          simp only [env0, seed, hrun1]
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
          simp only [List.length_map, List.length_finRange, List.length_ofFn, Nat.sub_self, List.getD_cons_zero, evalV]
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp [xOf, hk0.symm, hkp.symm]
      have henv0k : env0.getD k.val (.inl false) = .inl false := by
        have hl1 : k.val < ((List.finRange 10).map (fun m : Fin 10 => if m = k then Sum.inl false else .inr (aut9 k m).val)).length := by simp [k.isLt]
        simp only [env0]
        rw [List.getD_append _ _ _ _ hl1, List.getD_eq_getElem _ _ hl1]
        simp
      have hcirc : HasCircuitSize 9 f670 (simpStep 9 (D.gates.foldl (simpStep 9) (env0, [gFirst])) ⟨.and, [u, 10 + D.size]⟩).2.length :=
        simpRun_all 9 D.gates (env0, [gFirst]) f670 xOf hDfan haccFan henv0Len henv0Bdd henv0Tr
          (fun y => aut9Match k y) f670Zero rfl
      have hge16 : 16 ≤ (simpStep 9 (D.gates.foldl (simpStep 9) (env0, [gFirst])) ⟨.and, [u, 10 + D.size]⟩).2.length := by
        by_contra! hle15
        obtain ⟨C, hCf, hCs, hCe⟩ := hcirc
        exact h670 ⟨C, hCf, by omega, hCe⟩
      have hmid15 : 15 ≤ (D.gates.foldl (simpStep 9) (env0, [gFirst])).2.length := by
        have htop := simpStep_lenLe 9 (D.gates.foldl (simpStep 9) (env0, [gFirst])) ⟨.and, [u, 10 + D.size]⟩
        omega
      have hcnt := countFold 9 (fun g => rd g k.val) D.gates (env0, [gFirst])
        (fun g s hg _ hpref hP => by
          obtain ⟨hop, hgl⟩ := hDfan g hg
          exact simpStep_dropConst 9 s g k.val hop hgl hP
            (by dsimp only [isConst]; rw [hpref k.val (by rw [henv0Len]; omega), henv0k]))
      simp only [List.length_singleton] at hcnt
      change D.gates.countP _ + 14 ≤ D.gates.length
      omega
  have hasZeroReader : ∃ g ∈ D.gates, rd g 0 = true := by
    by_contra hno
    push Not at hno
    have hno' : ∀ g ∈ D.gates, rd g 0 = false := fun g hg => Bool.eq_false_iff.mpr (hno g hg)
    let xA : Fin 10 → Bool := if b = true then fun i => decide (i = 1) else fun i => decide (i = 2 ∨ i = 5)
    let xB : Fin 10 → Bool := if b = true then fun i => decide (i = 0 ∨ i = 1) else fun i => decide (i = 0 ∨ i = 2 ∨ i = 5)
    have hseed : ∀ i, 1 ≤ i → (seed xA).getD i false = (seed xB).getD i false := by
      intro i hi
      by_cases h10 : i < 10
      · have la : i < (List.ofFn xA).length := by simp [h10]
        have lb : i < (List.ofFn xB).length := by simp [h10]
        simp only [seed]
        rw [List.getD_append _ _ _ _ la, List.getD_append _ _ _ _ lb,
            List.getD_eq_getElem _ _ la, List.getD_eq_getElem _ _ lb]
        simp only [List.getElem_ofFn, xA, xB]
        have hne0 : (⟨i, h10⟩ : Fin 10) ≠ 0 := fun h => by have := congrArg Fin.val h; simp at this; omega
        cases b <;> simp [hne0]
      · by_cases hi10 : i = 10
        · subst hi10
          simp only [seed]
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
          cases b <;> decide
        · rw [List.getD_eq_default _ _ (by rw [seedLen]; omega), List.getD_eq_default _ _ (by rw [seedLen]; omega)]
    have hagree : ∀ (ls : List Gate) (wA wB : List Bool),
        (∀ g ∈ ls, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ ls, rd g 0 = false) →
        wA.length = wB.length → 1 ≤ wA.length →
        (∀ i, 1 ≤ i → wA.getD i false = wB.getD i false) →
        ∀ i, 1 ≤ i → (ls.foldl step wA).getD i false = (ls.foldl step wB).getD i false := by
      intro ls
      induction ls with
      | nil => intro wA wB _ _ _ _ h i hi; exact h i hi
      | cons g ls ih =>
        intro wA wB hlf hnr hlen hpos hag i hi
        obtain ⟨hop, hgl⟩ := hlf g List.mem_cons_self
        have hg0 : rd g 0 = false := hnr g List.mem_cons_self
        have hgeval : g.op.eval (g.inputs.map fun k => wA.getD k false) =
            g.op.eval (g.inputs.map fun k => wB.getD k false) := by
          rcases g with ⟨op, inputs⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl | rfl
          · cases hgi : inputs with
            | nil => rfl
            | cons a l =>
              cases l with
              | nil =>
                simp [rd_and, hgi] at hg0
                simp only [List.map_cons, List.map_nil, hag a (by omega)]
              | cons c l2 =>
                cases l2 with
                | nil =>
                  simp [rd_and, hgi] at hg0
                  simp only [List.map_cons, List.map_nil, hag a (by omega), hag c (by omega)]
                | cons _ _ => simp [hgi] at hgl
          · cases hgi : inputs with
            | nil => rfl
            | cons a l =>
              cases l with
              | nil =>
                simp [rd_or, hgi] at hg0
                simp only [List.map_cons, List.map_nil, hag a (by omega)]
              | cons c l2 =>
                cases l2 with
                | nil =>
                  simp [rd_or, hgi] at hg0
                  simp only [List.map_cons, List.map_nil, hag a (by omega), hag c (by omega)]
                | cons _ _ => simp [hgi] at hgl
          · cases hgi : inputs with
            | nil => rfl
            | cons a l =>
              simp [rd_not, hgi] at hg0
              simp only [eval_not, List.map_cons, List.headD_cons, hag a (by omega)]
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (step wA g) (step wB g) (fun h hh => hlf h (List.mem_cons_of_mem _ hh))
          (fun h hh => hnr h (List.mem_cons_of_mem _ hh))
          (by simp [step, hlen]) (by simp [step])
        · intro j hj
          simp only [step]
          by_cases hlt : j < wA.length
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
            exact hag j hj
          · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen, hgeval]
        · exact hi
    have huEq : wD xA u = wD xB u :=
      hagree D.gates (seed xA) (seed xB) hDfan hno' (by simp [seedLen]) (by simp [seedLen]) hseed u (by omega)
    have hvEq' : wD xA (10 + D.size) = wD xB (10 + D.size) :=
      hagree D.gates (seed xA) (seed xB) hDfan hno' (by simp [seedLen]) (by simp [seedLen]) hseed (10 + D.size) (by omega)
    have hfEq : fP xA = fP xB := by
      rw [← exactD xA, ← exactD xB, huEq, hvEq']
    have hdiff : fP xA ≠ fP xB := by cases b <;> decide
    exact hdiff hfEq
  have hDge16 : 16 ≤ D.size := by
    obtain ⟨g, hg, hrg⟩ := hasZeroReader
    have h1 := (elimEnd 0 pFin (Or.inl ⟨rfl, rfl⟩)).1
    simp only [Fin.val_zero] at h1
    have hpos : 1 ≤ D.gates.countP (fun g => rd g 0 || (rd g pFin.val && rd g 10)) :=
      List.countP_pos_iff.mpr ⟨g, hg, by simp [hrg]⟩
    omega
  cases b with
  | true =>
    have h0 := elimEnd 0 1 (Or.inl ⟨rfl, rfl⟩)
    have h1 := elimEnd 1 0 (Or.inr ⟨rfl, rfl⟩)
    let f1007 : (Fin 8 → Bool) → Bool := fun x =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
      (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
    have f1007Zero : f1007 (fun _ => false) = false := by decide
    let map01 : Fin 10 → Fin 8 := fun i => Fin.ofNat 8 (([0, 0, 0, 1, 5, 6, 3, 4, 2, 7] : List ℕ).getD i.val 0)
    let xOf01 : (Fin 8 → Bool) → (Fin 10 → Bool) := fun y i =>
      if i = 0 ∨ i = 1 then false else y (map01 i)
    have match01 : ∀ y : Fin 8 → Bool, fP (xOf01 y) = f1007 y := by
      intro y
      change (false && false || false && y 0 || y 0 && y 1 || y 1 && y 5 || y 5 && false || false && y 6 || false && y 3 || y 0 && y 4 || y 1 && y 2 || y 5 && y 7 || y 6 && y 4 || y 4 && y 7 || y 7 && y 3 || y 3 && y 2 || y 2 && y 6) =
        ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) || (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4))
      simp only [Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · rintro (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr h.symm))
        · exact Or.inr h.symm
        · exact Or.inl (Or.inl (Or.inl (Or.inr h.symm)))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h.symm)))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · rintro (((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
        · exact Or.inl (Or.inr h.symm)
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inr h.symm))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h.symm))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h.symm)))
    let env01 : List (Sum Bool ℕ) :=
      [.inl false, .inl false, .inr 0, .inr 1, .inr 5, .inr 6, .inr 3, .inr 4, .inr 2, .inr 7, .inl false]
    have henv01Bdd : ∀ s ∈ env01, ∀ j, s = .inr j → j < 8 + ([] : List Gate).length := by
      intro s hs j hj
      simp only [env01, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        cases hj <;> decide
    have henv01Tr : ∀ y : Fin 8 → Bool, ∀ i < 11,
        evalV (([] : List Gate).foldl step (List.ofFn y)) (env01.getD i (.inl false)) = (seed (xOf01 y)).getD i false := by
      intro y i hi
      have hg8 : ∀ k : Fin 8, (List.ofFn y).getD k.val false = y k := fun k => by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have hg10 : ∀ k : Fin 10, (seed (xOf01 y)).getD k.val false = xOf01 y k := fun k => by
        simp only [seed]
        rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      interval_cases i
      · exact (hg10 0).symm
      · exact (hg10 1).symm
      · exact (hg8 0).trans (hg10 2).symm
      · exact (hg8 1).trans (hg10 3).symm
      · exact (hg8 5).trans (hg10 4).symm
      · exact (hg8 6).trans (hg10 5).symm
      · exact (hg8 3).trans (hg10 6).symm
      · exact (hg8 4).trans (hg10 7).symm
      · exact (hg8 2).trans (hg10 8).symm
      · exact (hg8 7).trans (hg10 9).symm
      · simp only [env01, seed, List.foldl_nil, evalV]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [xOf01, pFin]
    have hcirc01 : HasCircuitSize 8 f1007 (simpStep 8 (D.gates.foldl (simpStep 8) (env01, [])) ⟨.and, [u, 10 + D.size]⟩).2.length :=
      simpRun_all 8 D.gates (env01, []) f1007 xOf01 hDfan (fun _ h => by cases h) (by rfl) henv01Bdd henv01Tr
        match01 f1007Zero rfl
    have hge13 : 13 ≤ (simpStep 8 (D.gates.foldl (simpStep 8) (env01, [])) ⟨.and, [u, 10 + D.size]⟩).2.length := by
      by_contra! hle12
      obtain ⟨C, hCf, hCs, hCe⟩ := hcirc01
      exact h1007 ⟨C, hCf, by omega, hCe⟩
    have hmid12 : 12 ≤ (D.gates.foldl (simpStep 8) (env01, [])).2.length := by
      have htop := simpStep_lenLe 8 (D.gates.foldl (simpStep 8) (env01, [])) ⟨.and, [u, 10 + D.size]⟩
      omega
    have hcnt01 := countFold 8 (fun g => rd g 0 || rd g 1 || rd g 10) D.gates (env01, [])
      (fun g s hg _ hpref hP => by
        obtain ⟨hop, hgl⟩ := hDfan g hg
        rcases Bool.or_eq_true_iff.mp hP with h12 | h3
        · rcases Bool.or_eq_true_iff.mp h12 with h1' | h2'
          · exact simpStep_dropConst 8 s g 0 hop hgl h1' (by dsimp only [isConst]; rw [hpref 0 (by simp [env01])]; rfl)
          · exact simpStep_dropConst 8 s g 1 hop hgl h2' (by dsimp only [isConst]; rw [hpref 1 (by simp [env01])]; rfl)
        · exact simpStep_dropConst 8 s g 10 hop hgl h3 (by dsimp only [isConst]; rw [hpref 10 (by simp [env01])]; rfl))
    have hbound01 : D.gates.countP (fun g => rd g 0 || rd g 1 || rd g 10) + 12 ≤ D.size := by
      simp only [List.length_nil, zero_add] at hcnt01
      change D.gates.countP _ + 12 ≤ D.gates.length
      omega
    have hsplitOf : ∀ (ls : List Gate) (i : ℕ) (g : Gate), ls[i]? = some g →
        ∃ a c, ls = a ++ g :: c ∧ a.length = i := by
      intro ls
      induction ls with
      | nil => intro i g h; simp at h
      | cons x xs ih =>
        intro i g h
        cases i with
        | zero =>
          simp at h; subst h
          exact ⟨[], xs, rfl, rfl⟩
        | succ i =>
          simp at h
          obtain ⟨a, c, heq, hlen⟩ := ih i g h
          exact ⟨x :: a, c, by rw [heq]; rfl, by simp [hlen]⟩
    have hpair : ∀ p ∈ ([(0, 1), (1, 0)] : List (ℕ × ℕ)),
        D.gates.countP (fun g => rd g p.1 || (rd g p.2 && rd g 10)) + 15 ≤ D.size ∧
        ∀ i g, D.gates[i]? = some g → rd g p.1 = true → g.op.eval [true, false] = false →
          D.gates.countP (fun h => rd h p.1 || rd h (11 + i)) + 15 ≤ D.size := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨h0.1, fun i g hi hrdg hnot => ?_⟩
        obtain ⟨a, c, hsp, hal⟩ := hsplitOf D.gates i g hi
        rw [← hal]; exact h0.2 a g c hsp hrdg hnot
      · refine ⟨h1.1, fun i g hi hrdg hnot => ?_⟩
        obtain ⟨a, c, hsp, hal⟩ := hsplitOf D.gates i g hi
        rw [← hal]; exact h1.2 a g c hsp hrdg hnot
    have hboth : ∀ c : Bool, ∃ x, wD x u = c ∧ wD x (10 + D.size) = !c := by
      intro c; cases c
      · exact H2D
      · exact H1D
    exact hAdj D u ⟨hDfan, hDge16, hDle17, lower14, huLtD⟩ hpair hbound01
      (fun k hk => elimAny ⟨k, hk⟩) hboth (fun x => (exactD x).trans (pc10 x).symm)
  | false =>
    have h0 := elimEnd 0 2 (Or.inl ⟨rfl, rfl⟩)
    have h2 := elimEnd 2 0 (Or.inr ⟨rfl, rfl⟩)
    have hsplitOf : ∀ (ls : List Gate) (i : ℕ) (g : Gate), ls[i]? = some g →
        ∃ a c, ls = a ++ g :: c ∧ a.length = i := by
      intro ls
      induction ls with
      | nil => intro i g h; simp at h
      | cons x xs ih =>
        intro i g h
        cases i with
        | zero =>
          simp at h; subst h
          exact ⟨[], xs, rfl, rfl⟩
        | succ i =>
          simp at h
          obtain ⟨a, c, heq, hlen⟩ := ih i g h
          exact ⟨x :: a, c, by rw [heq]; rfl, by simp [hlen]⟩
    have hpair : ∀ p ∈ ([(0, 2), (2, 0)] : List (ℕ × ℕ)),
        D.gates.countP (fun g => rd g p.1 || (rd g p.2 && rd g 10)) + 15 ≤ D.size ∧
        ∀ i g, D.gates[i]? = some g → rd g p.1 = true → g.op.eval [true, false] = false →
          D.gates.countP (fun h => rd h p.1 || rd h (11 + i)) + 15 ≤ D.size := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨h0.1, fun i g hi hrdg hnot => ?_⟩
        obtain ⟨a, c, hsp, hal⟩ := hsplitOf D.gates i g hi
        rw [← hal]; exact h0.2 a g c hsp hrdg hnot
      · refine ⟨h2.1, fun i g hi hrdg hnot => ?_⟩
        obtain ⟨a, c, hsp, hal⟩ := hsplitOf D.gates i g hi
        rw [← hal]; exact h2.2 a g c hsp hrdg hnot
    have hboth : ∀ c : Bool, ∃ x, wD x u = c ∧ wD x (10 + D.size) = !c := by
      intro c; cases c
      · exact H2D
      · exact H1D
    exact hNonAdj D u ⟨hDfan, hDge16, hDle17, lower14, huLtD⟩ hpair
      (fun k hk => elimAny ⟨k, hk⟩) hboth (fun x => (exactD x).trans (pc10 x).symm)
