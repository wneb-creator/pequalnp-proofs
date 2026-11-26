import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4073_2
    (onlyInputNot : ∀ (C : Circuit) (u : ℕ), FanInTwo C → C.size = 17 → 11 ≤ u → u < 27 →
      (∀ g ∈ C.gates, g.op ≠ GateOp.not) →
      let w := fun (r : ℕ) (i : ℕ) =>
        (C.wires (List.ofFn (fun j : Fin 10 => r.testBit j.val) ++ [!(r.testBit 0)])).getD i false
      (∃ r ∈ ([6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641] : List ℕ),
        (w r u && w r 27) = false) ∨
      (∃ r ∈ ([50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773] : List ℕ),
        (w r u && w r 27) = true))
    (extraNot : ∀ (C : Circuit) (u : ℕ), FanInTwo C → C.size = 17 → 11 ≤ u → u < 27 →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ¬ (∀ x : Fin 10 → Bool,
        let w := (C.wires (List.ofFn x ++ [!x 0])).getD
        (w u false && w 27 false) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))) :
    ∀ (C : Circuit) (a b : ℕ), FanInTwo C → C.size ≤ 17 →
      let f := fun (x : Fin 10 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x ++ [!x 0])).getD i false
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      (∀ x, f x = true → w x a = true ∧ w x b = true) →
      ∃ x, f x = false ∧ w x a = true ∧ w x b = true := by
  intro C a b hC hsize f w hab hba hpos
  by_contra hneg
  have exactPair (x : Fin 10 → Bool) : (w x a && w x b) = f x := by
    cases hx : f x
    · cases hA : w x a <;> cases hB : w x b <;> try rfl
      exact (hneg ⟨x, hx, hA, hB⟩).elim
    · obtain ⟨hA, hB⟩ := hpos x hx
      simp [hA, hB]
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have lengthRun (gs : List Gate) (ws : List Bool) :
      (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).length = _
      rw [ih]
      simp [step]
      omega
  have retain (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).getD i false = ws.getD i false
      rw [ih _ (by simpa [step] using Nat.lt_succ_of_lt hi)]
      exact List.getD_append _ _ _ _ hi
  have bound (i : ℕ) (h : ∀ x, f x = true → w x i = true) : 11 ≤ i ∧ i < 11 + C.size := by
    let x := fun j : Fin 10 => (3 : ℕ).testBit j.val
    let y := fun j : Fin 10 => (640 : ℕ).testBit j.val
    have hx : w x i = true := h x (by decide)
    have hy : w y i = true := h y (by decide)
    have len (z : Fin 10 → Bool) : (List.ofFn z ++ [!z 0]).length = 11 := by simp
    have hlo : 11 ≤ i := by
      by_contra! hi
      have readX := retain C.gates (List.ofFn x ++ [!x 0]) i (by rwa [len])
      have readY := retain C.gates (List.ofFn y ++ [!y 0]) i (by rwa [len])
      change _ = (_ : List Bool).getD i false at readX readY
      change (C.gates.foldl step _).getD i false = true at hx hy
      rw [readX] at hx
      rw [readY] at hy
      have incompatible : ∀ j : Fin 11,
          ¬ ((List.ofFn x ++ [!x 0]).getD j false = true ∧
             (List.ofFn y ++ [!y 0]).getD j false = true) := by decide
      exact incompatible ⟨i, hi⟩ ⟨hx, hy⟩
    refine ⟨hlo, ?_⟩
    by_contra! hi
    change (C.gates.foldl step _).getD i false = true at hx
    rw [List.getD_eq_default _ _ (by rw [lengthRun, len]; exact hi)] at hx
    exact Bool.false_ne_true hx
  have ha := bound a (fun x hx => (hpos x hx).1)
  have hb := bound b (fun x hx => (hpos x hx).2)
  have hab' : a ≠ b := by
    rintro rfl
    obtain ⟨x, h₁, h₂⟩ := hab
    rw [h₁] at h₂
    contradiction
  let u := min a b
  let v := max a b
  have huv : u < v := by
    rcases lt_or_gt_of_ne hab' with h | h
    · simpa [u, v, min_eq_left h.le, max_eq_right h.le] using h
    · simpa [u, v, min_eq_right h.le, max_eq_left h.le] using h
  have hu : 11 ≤ u := le_min ha.1 hb.1
  have hv : v < 11 + C.size := max_lt ha.2 hb.2
  have evalPair (x : Fin 10 → Bool) : (w x u && w x v) = f x := by
    rcases le_total a b with h | h
    · simpa [u, v, min_eq_left h, max_eq_right h] using exactPair x
    · simpa [u, v, min_eq_right h, max_eq_left h, Bool.and_comm] using exactPair x
  have huv27 : v ≤ 27 := by omega
  have hu' : u < 27 := by omega
  have normalized : ∃ D : Circuit, FanInTwo D ∧ D.size = 17 ∧
      ∀ x : Fin 10 → Bool,
        let W := (D.wires (List.ofFn x ++ [!x 0])).getD
        (W u false && W 27 false) = f x := by
    by_cases hv27 : v = 27
    · have hc : C.size = 17 := by omega
      refine ⟨C, hC, hc, ?_⟩
      intro x
      change (w x u && w x 27) = f x
      simpa only [hv27] using evalPair x
    · have hvlt : v < 27 := by omega
      let gs := C.gates.take (v - 10)
      have hgs : gs.length = v - 10 := by
        have hz : v - 10 ≤ C.size := by omega
        change v - 10 ≤ C.gates.length at hz
        simp [gs, List.length_take, Nat.min_eq_left hz]
      let dummy : Gate := ⟨GateOp.or, []⟩
      let copy : Gate := ⟨GateOp.or, [v]⟩
      let pad := List.replicate (26 - v) dummy
      let D : Circuit := ⟨gs ++ pad ++ [copy], 27⟩
      have hlenD : D.size = 17 := by
        change (gs ++ pad ++ [copy]).length = 17
        simp only [List.length_append, List.length_cons, List.length_nil]
        dsimp only [pad]
        simp only [List.length_replicate]
        omega
      have hlegal : FanInTwo D := by
        intro g hg
        change g ∈ gs ++ pad ++ [copy] at hg
        simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hg
        rcases hg with (hg | hg) | rfl
        · exact hC g (List.mem_of_mem_take hg)
        · have heq : g = dummy := (List.mem_replicate.mp (by simpa [pad] using hg)).2
          subst g
          simp [dummy]
        · simp [copy]
      refine ⟨D, hlegal, hlenD, ?_⟩
      intro x
      let xs := List.ofFn x ++ [!x 0]
      let ws := gs.foldl step xs
      let ps := pad.foldl step ws
      have hwlen : ws.length = v + 1 := by
        simp [ws, xs, lengthRun, hgs]
        omega
      have hplen : ps.length = 27 := by
        simp [ps, lengthRun, pad, hwlen]
        omega
      have hprefix (i : ℕ) (hi : i ≤ v) : ws.getD i false = w x i := by
        have hlt : i < ws.length := by omega
        have split : C.gates = gs ++ C.gates.drop (v - 10) := (List.take_append_drop _ _).symm
        change ws.getD i false = (C.gates.foldl step xs).getD i false
        rw [split, List.foldl_append]
        exact (retain _ _ _ hlt).symm
      have padded (i : ℕ) (hi : i ≤ v) : ps.getD i false = w x i := by
        rw [show ps.getD i false = ws.getD i false by exact retain _ _ _ (by omega)]
        exact hprefix i hi
      change (((gs ++ pad ++ [copy]).foldl step xs).getD u false &&
        ((gs ++ pad ++ [copy]).foldl step xs).getD 27 false) = f x
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((step ps copy).getD u false && (step ps copy).getD 27 false) = f x
      have huval : (step ps copy).getD u false = w x u := by
        change (List.foldl step ps [copy]).getD u false = _
        rw [retain [copy] ps u (by omega)]
        exact padded u huv.le
      have hvval : (step ps copy).getD 27 false = w x v := by
        have hlast : (step ps copy).getD 27 false = ps.getD v false := by
          change (ps ++ [GateOp.or.eval [ps.getD v false]]).getD 27 false = _
          rw [← hplen, List.getD_append_right _ _ _ _ le_rfl]
          simp only [Nat.sub_self]
          cases (ps.getD v false) <;> rfl
        rw [hlast]
        exact padded v le_rfl
      rw [huval, hvval]
      exact evalPair x
  obtain ⟨D, hD, size17, eval27⟩ := normalized
  let wD := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x ++ [!x 0])).getD i false
  by_cases hnot : ∃ g ∈ D.gates, g.op = GateOp.not
  · exact extraNot D u hD size17 hu hu' hnot eval27
  have hmono : ∀ g ∈ D.gates, g.op ≠ GateOp.not := fun g hg he => hnot ⟨g, hg, he⟩
  rcases onlyInputNot D u hD size17 hu hu' hmono with ⟨r, hr, hw⟩ | ⟨r, hr, hw⟩
  · have good : ∀ r : ℕ, r ∈ ([6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641] : List ℕ) →
        f (fun j => r.testBit j.val) = true := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have bad := (eval27 (fun j => r.testBit j.val)).trans (good r hr)
    change (wD (fun j => r.testBit j.val) u && wD (fun j => r.testBit j.val) 27) = false at hw
    rw [hw] at bad
    contradiction
  · have good : ∀ r : ℕ, r ∈ ([50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773] : List ℕ) →
        f (fun j => r.testBit j.val) = false := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have bad := (eval27 (fun j => r.testBit j.val)).trans (good r hr)
    change (wD (fun j => r.testBit j.val) u && wD (fun j => r.testBit j.val) 27) = true at hw
    rw [hw] at bad
    contradiction
