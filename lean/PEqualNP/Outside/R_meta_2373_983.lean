import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2373_983 :
  (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.circuitFun 10 C = (fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) →
    17 ≤ List.countP (fun g => !g.op.eval [false]) C.gates) →
  (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩], 10 + gs.length⟩;
    let w : (Fin 10 → Bool) → ℕ → Bool := fun x i =>
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false;
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 19 →
    (∃ x, w x a = true ∧ w x b = false) →
    (∃ x, w x a = false ∧ w x b = true) →
    PEqualNP.NotBracket.notCount C = 0 →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) →
  (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩], 10 + gs.length⟩;
    let w : (Fin 10 → Bool) → ℕ → Bool := fun x i =>
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false;
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 19 →
    (∃ x, w x a = true ∧ w x b = false) →
    (∃ x, w x a = false ∧ w x b = true) →
    PEqualNP.NotBracket.notCount C = 1 →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) →
  (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩], 10 + gs.length⟩;
    let w : (Fin 10 → Bool) → ℕ → Bool := fun x i =>
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false;
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 19 →
    (∃ x, w x a = true ∧ w x b = false) →
    (∃ x, w x a = false ∧ w x b = true) →
    PEqualNP.NotBracket.notCount C = 2 →
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  classical
  intro hBound h0 h1 h2
  have wires_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
    intro gs w
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have append_eval (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) :
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs ++ [g], xs.length + gs.length⟩ xs =
        g.op.eval (g.inputs.map fun i =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs).getD i false) := by
    let w := PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs
    have hl : w.length = xs.length + gs.length := wires_length gs xs
    change ((gs ++ [g]).foldl
      (fun (w : List Bool) h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)])
      xs).getD (xs.length + gs.length) false = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD
      (xs.length + gs.length) false = _
    rw [← hl, List.getD_eq_getElem _ _ (by simp)]
    simp
    rfl
  have append_or_eval (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (xs : List Bool) (a b : ℕ) :
      PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨gs ++ [⟨.or, [a, b]⟩], xs.length + gs.length⟩ xs =
        ((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs).getD a false ||
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs).getD b false) := by
    rw [append_eval]
    change ((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs).getD a false ||
      ((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ xs).getD b false || false)) = _
    simp only [Bool.or_false]
  intro g C a b legal_first legal_tail small_tail
  let f : (Fin 10 → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))
  let w : (Fin 10 → Bool) → ℕ → Bool := fun x i =>
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: C.gates, 0⟩ (List.ofFn x)).getD i false
  change (∃ x, w x a = true ∧ w x b = false) →
    (∃ x, w x a = false ∧ w x b = true) →
    (∀ x, f x = false → w x a = false ∧ w x b = false) →
    ∃ x, f x = true ∧ w x a = false ∧ w x b = false
  intro left_only right_only off
  by_contra missing
  let gs := g :: C.gates
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gs ++ [⟨.or, [a, b]⟩], 10 + gs.length⟩
  have legal : PEqualNP.MetaComplexity.FanInTwo D := by
    intro h hh
    change h ∈ gs ++ [⟨.or, [a, b]⟩] at hh
    rcases List.mem_append.mp hh with hh | hh
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact legal_first h (by simp)
      · exact legal_tail h hh
    · have eq : h = ⟨.or, [a, b]⟩ := List.mem_singleton.mp hh
      subst h
      exact ⟨by simp, by simp⟩
  have small : D.size ≤ 19 := by
    change (gs ++ [(⟨.or, [a, b]⟩ : PEqualNP.CircuitLowerBounds.Gate)]).length ≤ 19
    simp only [gs, List.length_append, List.length_cons, List.length_nil]
    change C.gates.length ≤ 17 at small_tail
    omega
  have output (x : Fin 10 → Bool) : D.eval (List.ofFn x) = (w x a || w x b) := by
    simpa only [D, w, gs, List.length_ofFn] using append_or_eval gs (List.ofFn x) a b
  have covered (x : Fin 10 → Bool) (positive : f x = true) : (w x a || w x b) = true := by
    cases ha : w x a <;> cases hb : w x b
    · exact False.elim (missing ⟨x, positive, ha, hb⟩)
    all_goals rfl
  have computes : PEqualNP.MetaComplexity.circuitFun 10 D = f := by
    funext x
    change D.eval (List.ofFn x) = f x
    rw [output]
    cases hf : f x
    · obtain ⟨ha, hb⟩ := off x hf
      rw [ha, hb]
      rfl
    · exact covered x hf
  have compact_eq (x : Fin 10 → Bool) : (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))) = f x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) || (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) || (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) || (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) || (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || (false)))))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false]
    ac_rfl
  have exact_compact : PEqualNP.MetaComplexity.circuitFun 10 D = (fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))))) := by
    funext x
    exact (congrFun computes x).trans (compact_eq x).symm
  have lower := hBound D legal exact_compact
  have partition : ∀ ds : List PEqualNP.CircuitLowerBounds.Gate,
      List.countP (fun h => !h.op.eval [false]) ds +
        List.countP (fun h => h.op.eval [false]) ds = ds.length := by
    intro ds
    induction ds with
    | nil => rfl
    | cons h ds ih =>
      cases eq : h.op.eval [false] <;> simp [eq] <;> omega
  have count_eq : List.countP (fun h => h.op.eval [false]) D.gates =
      PEqualNP.NotBracket.notCount D := by
    unfold PEqualNP.NotBracket.notCount
    rw [← List.countP_eq_length_filter]
    apply List.countP_congr
    intro h hh
    obtain ⟨op, ins⟩ := h
    have hop := (legal _ hh).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with (eq | eq | eq) <;> change op = _ at eq <;> subst op <;> rfl
  have bounded : PEqualNP.NotBracket.notCount D ≤ 2 := by
    have total := partition D.gates
    rw [count_eq] at total
    change D.gates.length ≤ 19 at small
    omega
  have mismatch : ∃ x : Fin 10 → Bool, D.eval (List.ofFn x) ≠ (List.finRange 5).any (fun i =>
        (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
        (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))) := by
    have cases : PEqualNP.NotBracket.notCount D = 0 ∨
        PEqualNP.NotBracket.notCount D = 1 ∨ PEqualNP.NotBracket.notCount D = 2 := by omega
    rcases cases with h | h | h
    · exact h0 gs a b legal small left_only right_only h
    · exact h1 gs a b legal small left_only right_only h
    · exact h2 gs a b legal small left_only right_only h
  obtain ⟨x, hx⟩ := mismatch
  exact hx (congrFun exact_compact x)
