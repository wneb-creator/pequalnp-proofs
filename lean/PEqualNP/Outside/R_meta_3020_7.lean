import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3020_7
    (h1 : ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (1 : ℕ) → x1.map (fun i : Fin 11 => (i : ℕ)) ≤ x1.map (fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : List (Fin (11 : ℕ))),   x1.length = (2 : ℕ) → x1.map (fun i : Fin 11 => (i : ℕ)) ≤ x1.map (fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen C hfan hsz
  have hwi : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.wires l = D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := fun _ _ => rfl
  have hev : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.eval l = (D.wires l).getD D.output false :=
    fun _ _ => rfl
  -- the symmetry (0 2)(3 5)(4 7) of the graph, which keeps the wire x0 OR x2
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b2 && b1 || b1 && b0 || b0 && b5 || b5 && b7 || b7 && b2 || b2 && b3 || b1 && b6 ||
        b0 && b4 || b5 && b8 || b3 && b4 || b6 && b8 || b8 && b3) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 ||
        b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hinv : ∀ j : ℕ, List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) = j := by
    intro j
    by_cases hj : j < 9
    · interval_cases j <;> decide
    · rw [hge j (by omega), hge j (by omega)]
  have hr : ∀ v : Fin 11, ((Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑v ↑v) : Fin 11) : ℕ) = List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑v ↑v := by
    intro v
    rw [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    by_cases h : (v : ℕ) < 9
    · have := hlt v h
      omega
    · rw [hge v (by omega)]
      exact v.2
  have happ : ∀ (W W' : List Bool) (u : Bool), W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ, (W' ++ [u]).getD (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) false = (W ++ [u]).getD j false := by
    intro W W' u hl h9 hW j
    by_cases hj : j < W.length
    · have hj' : List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j < W'.length := by
        by_cases h : j < 9
        · have := hlt j h
          omega
        · rw [hge j (by omega)]
          omega
      have hWj := hW j
      generalize List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j = r at hj' hWj ⊢
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hj', List.getElem?_append_left hj]
      simpa only [List.getD_eq_getElem?_getD] using hWj
    · rw [hge j (by omega)]
      by_cases hj2 : j = W.length
      · subst hj2
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
          List.getElem?_append_right (le_refl _), ← hl,
          List.getElem?_append_right (le_refl _)]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp
        omega
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        exact happ W W' _ hl h9 hW j
  -- the ten shared wires: the nine inputs and x0 OR x2
  have h10 : ∀ (y : Fin 9 → Bool) (j : ℕ),
      (List.ofFn y ++ [y 0 || y 2]).getD (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) j j) false =
        (List.ofFn (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)) ++ [y 2 || y 0]).getD j false := by
    intro y j
    by_cases hj : j < 10
    · interval_cases j
      all_goals first
        | rfl
        | (show (y 0 || y 2) = (y 2 || y 0); exact Bool.or_comm _ _)
    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hcase : ∀ L : List (Fin 11), L.length ≤ 2 →
      L.map (fun i : Fin 11 => (i : ℕ)) ≤ L.map (fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        D.eval ((List.ofFn x ++ [x 0 || x 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (L.map fun i : Fin 11 => (List.ofFn x ++ [x 0 || x 2]).getD ↑i false)]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro L hL hc D hD hDs
    rcases Nat.lt_or_ge L.length 2 with h | h
    · exact h1 L (by omega) hc D hD hDs
    · exact h2 L (by omega) hc D hD hDs
  rcases le_total (x1.map fun i : Fin 11 => (i : ℕ)) (x1.map fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i)
    with hc | hc
  · exact hcase x1 hlen hc C hfan hsz
  · have hmapval : (x1.map fun i : Fin 11 => (Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11)).map
        (fun i : Fin 11 => (i : ℕ)) = x1.map (fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hr i
    have hmaprho : (x1.map fun i : Fin 11 => (Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11)).map
        (fun i : Fin 11 => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) = x1.map (fun i : Fin 11 => (i : ℕ)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      show List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑(Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11) ↑(Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11) = ↑i
      rw [hr, hinv]
    have hfan' : PEqualNP.MetaComplexity.FanInTwo
        (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i))) (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) C.output C.output)) := by
      intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      refine ⟨(hfan d0 hd0).1, ?_⟩
      simpa using (hfan d0 hd0).2
    have hsz' : (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i))) (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) C.output C.output)).size ≤ 13 := by
      show (C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i))).length ≤ 13
      rw [List.length_map]
      exact hsz
    obtain ⟨y, hy⟩ := hcase (x1.map fun i : Fin 11 => (Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11))
      (by rw [List.length_map]; exact hlen) (by rw [hmapval, hmaprho]; exact hc)
      (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.map (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map fun i => List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) i i))) (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) C.output C.output)) hfan' hsz'
    refine ⟨(fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)), ?_⟩
    intro x7 hcon
    apply hy
    -- the extra wire is the same for the two circuits
    have hE : PEqualNP.CircuitLowerBounds.GateOp.and.eval
        ((x1.map fun i : Fin 11 => (Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11)).map
          fun i : Fin 11 => (List.ofFn y ++ [y 0 || y 2]).getD ↑i false) =
        PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (x1.map fun i : Fin 11 => (List.ofFn (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)) ++ [y 2 || y 0]).getD ↑i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      show (List.ofFn y ++ [y 0 || y 2]).getD ↑(Fin.ofNat 11 (List.getD ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List ℕ) ↑i ↑i) : Fin 11) false = _
      rw [hr]
      exact h10 y i
    have e := hpre C.gates
      ((List.ofFn (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)) ++ [y 2 || y 0]) ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
        (x1.map fun i : Fin 11 => (List.ofFn (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)) ++ [y 2 || y 0]).getD ↑i false)])
      ((List.ofFn y ++ [y 0 || y 2]) ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
        (x1.map fun i : Fin 11 => (List.ofFn (fun i => y (![2, 1, 0, 5, 7, 3, 6, 4, 8] i)) ++ [y 2 || y 0]).getD ↑i false)])
      (by simp) (by simp)
      (happ _ _ _ (by simp) (by simp) (h10 y)) C.output
    rw [hE, hev]
    refine e.trans (hcon.trans ?_)
    exact hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
