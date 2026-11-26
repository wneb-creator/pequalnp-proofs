import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2300000 in
theorem PEqualNP.Outside.R_meta_5827_47
    (adjacent : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 1]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)))
    (nonadjacent : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
        ∃ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x 2]);
          (w.getD i false || w.getD j false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false := by
  intro a b C u v fan budget
  let target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let generator (g : Bool) (i : Fin 10) : Fin 10 :=
    ((if g then [2, 1, 6, 8, 3, 7, 0, 9, 5, 4] else [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]) : List (Fin 10)).getD i.val 0
  let run (w : List Bool) (i : Fin 10) := w.foldr generator i
  let words : List (List Bool) := [[], [], [], [false, true, false, true, true, true], [false, true, false, true, true, true], [false, true, false], [true, true, true, false, true, true, true, false], [false, true, false], [false, true, true, true, true, false], [true, true, true, false, true, true, false], [], [false], [false], [false, true, false, true, true, true, false], [false, true, false, true, true, true, false], [false], [false, true, true, true], [false, true, true, true, true], [true, true, true, false, true, true], [false, true, true, true, true], [false, true], [false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, false, true, true, false], [true, false, true, false, true, true, false], [false, true, false, true, false, true, true, true, false], [true, true, true, true, true], [false, true, false, true, false, true, true, true, false], [true, false, true, false, true, false, true, false], [false, true, true, true, true, true, false, true, true], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, true, true, true, false, true, true], [true, true, true, true, false, true, true], [false, true, false, true, false, true, true], [false, true, false, true, false, true, true], [true, false, true, false, true, false], [true, false, true, false, true], [false, true, false, true, false, true, false, true, false], [true, false, true, false, true, false], [false, true, false, true, false, true, false, true], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false, true, true, true], [true, false, true, false, true, true], [true, false, true, false, true, true], [true, false, true, true, true], [true, true, false], [false, true, false, true, false, true, true, true], [false, true, false, true, true, true, true, true, false], [false, true, false, true, true, false], [false, true, false, true, false, true, true, true], [true, false, true, true, true], [true, false], [true, false], [false, true, false, true, true, true, true, false], [false, true, true, true, true, false, true, false], [true, true, false, true, true, true], [true, false], [false, true, false, true, false], [false, true, false, true, true, true, true, false], [false, true, false, true, false], [true, true, false, true, true, false, true, true], [true, false], [true], [true], [true, true, false, true, true, true, false], [true, true, false, true, false, true, false], [false, true, false, true, true, true, true], [false, true, false, true], [true], [false, true, true, false, true], [false, true, false, true], [false, true, false, true, true, true, true], [true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, false], [true, false, true, false, true, true, true, false], [true, true, true, true, true, false, true, true], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, true], [true, false, true, true, true, true, false], [true, true, false, true, false], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true], [false, true, false, true, false, true], [false, true, false, true, false, true, false], [false, true, false, true, false, true, false], [true, false, true, false], [true, false, true], [false, true, true, false, true, false, true], [true, false, true, false], [true, true, false, true, true, true, true], [true, false, true, false], [true, false, true, false, true, true, true], [true, false, true, true, true, true], [false, true, false, true, false, true, true, true, true], [true, false, true, false, true, false, true, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true, true, false], [true, false, true, true, true, true], [true, false, true, false, true, true, true, true, false], [true, true, false, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true], [], [false], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false], [true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true, false, true, true, true], []]
  let second : List (Fin 10) := [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  let source : List Nat := [0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99]
  let ix (a b : Fin 11) := a.val * 11 + b.val
  let σ (a b : Fin 11) (i : Fin 10) : Fin 10 :=
    run (words.getD (ix a b) []) i
  let k (a b : Fin 11) := second.getD (ix a b) 1
  let src (a b : Fin 11) := source.getD (ix a b) 0
  have choices : ∀ a b : Fin 11, k a b = 1 ∨ k a b = 2 := by decide +kernel
  have kinds : ∀ a b : Fin 11,
      (src a b = 99 ∧ a.val = 10 ∧ b.val = 10) ∨
      (src a b = 0 ∧ (a.val = 10 ∨ σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧
          (b.val = 10 ∨ σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧ (a.val < 10 ∨ b.val < 10)) ∨
      (src a b = 10 ∧ a.val < 10 ∧ b.val < 10 ∧
          σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0 ∧
          σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = k a b) := by decide +kernel
  have one (g : Bool) (x : Fin 10 → Bool) : target (x ∘ generator g) = target x := by
    cases g
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 0) || (x 6 && x 9) || (x 8 && x 5) || (x 3 && x 4) || (x 7 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  have word (w : List Bool) (x : Fin 10 → Bool) : target (x ∘ run w) = target x := by
    induction w generalizing x with
    | nil => rfl
    | cons g w ih => exact (ih (x ∘ generator g)).trans (one g x)
  have invariant (x : Fin 10 → Bool) : target (x ∘ σ a b) = target x := word _ x
  let ρ (i : Nat) := if h : i < 10 then (σ a b ⟨i,h⟩).val else if i = 10 then src a b else i
  have srcCases : src a b = 99 ∨ src a b = 0 ∨ src a b = 10 := by
    rcases kinds a b with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  have hρ (n : Nat) (lo : 11 ≤ n) (hi : n ≤ 28) (i : Nat) : ρ i = n ↔ i = n := by
    by_cases h : i < 10
    · simp only [ρ,dite_eq_left h]
      have := (σ a b ⟨i,h⟩).isLt
      omega
    · by_cases e : i = 10
      · simp only [ρ,dite_eq_right h,ite_eq_left e]
        rcases srcCases with s|s|s <;> omega
      · simp [ρ,h,e]
  let raw (x : Fin 10 → Bool) (i : Fin 11) := (List.ofFn (x ∘ σ a b)).getD i.val false
  have rawGood (x : Fin 10 → Bool) (i : Fin 11) (h : i.val < 10) :
      raw x i = x (σ a b ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩) := by
    change (List.ofFn (x ∘ σ a b)).getD i.val false = _
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    simp [Nat.mod_eq_of_lt h]
  have rawBad (x : Fin 10 → Bool) (i : Fin 11) (h : i.val = 10) : raw x i = false := by
    simp [raw,h,List.getD_eq_getElem?_getD]
  let observed (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 || x (k a b)]
  have gift (x : Fin 10 → Bool) : (raw x a || raw x b) = (observed x).getD (src a b) false := by
    rcases kinds a b with ⟨s,ha,hb⟩ | ⟨s,ha,hb,hn⟩ | ⟨s,ha,hb,za,zb⟩
    · rw [rawBad _ _ ha,rawBad _ _ hb,s,List.getD_eq_default _ _ (by simp [observed])]
      rfl
    · have each (i : Fin 11) (hi : i.val = 10 ∨ σ a b ⟨i.val % 10,Nat.mod_lt _ (by decide)⟩ = 0) :
          raw x i = if i.val = 10 then false else x 0 := by
        by_cases e : i.val = 10
        · simp [e,rawBad _ _ e]
        · have lt : i.val < 10 := by have := i.isLt; omega
          simp [e,rawGood _ _ lt,hi.resolve_left e]
      rw [each a ha,each b hb,s,List.getD_append _ _ _ _ (by simp)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,show 0 < 10 by decide,dite_eq_left,Option.getD_some]
      rcases hn with h | h <;> split_ifs <;> simp_all <;> omega
    · rw [rawGood _ _ ha,rawGood _ _ hb,za,zb,s]
      change _ = (List.ofFn x ++ [x 0 || x (k a b)]).getD 10 false
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
      rfl

  let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  have app (w : List Bool) (z : Bool) (i : Nat) :
      (w ++ [z]).getD i false = if i = w.length then z else w.getD i false := by
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
    · by_cases eq : i = w.length
      · subst i
        simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right eq, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
  have simulation (gs : List Gate) (xs ys : List Bool)
      (len : xs.length = ys.length) (lower : 11 ≤ xs.length) (cap : xs.length + gs.length ≤ 28)
      (initial : ∀ i, xs.getD i false = ys.getD (ρ i) false) :
      ∀ i, ((⟨gs,0⟩ : Circuit).wires xs).getD i false =
        ((⟨gs.map rg,0⟩ : Circuit).wires ys).getD (ρ i) false := by
    induction gs generalizing xs ys with
    | nil => exact initial
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
      have next : (rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false) = z := by
        change g.op.eval _ = g.op.eval _
        congr 1
        simp only [rg,List.map_map,Function.comp_def]
        exact List.map_congr_left fun i _ => (initial i).symm
      change ∀ i, ((⟨gs,0⟩ : Circuit).wires (xs ++ [z])).getD i false =
        ((⟨gs.map rg,0⟩ : Circuit).wires (ys ++ [(rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false)])).getD (ρ i) false
      rw [next]
      apply ih
      · simp [len]
      · simp; omega
      · simp_all only [List.length_cons,List.length_append,List.length_nil]; omega
      · intro i
        simp only [app,←len,hρ _ lower (by omega) i,initial i]
  let D : Circuit := ⟨C.gates.map rg,0⟩
  have newFan : FanInTwo D := by
    intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using fan h hh
  have newCap : D.size ≤ 17 := by
    change (C.gates.map rg).length ≤ 17
    rw [List.length_map]
    exact budget
  have physical (x : Fin 10 → Bool) (i : Nat) :
      (C.wires (List.ofFn (x ∘ σ a b) ++ [raw x a || raw x b])).getD i false =
        (D.wires (observed x)).getD (ρ i) false := by
    apply simulation
    · simp [observed]
    · simp
    · have h : C.gates.length ≤ 17 := budget
      simpa only [List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using (show 10 + (0+1) + C.gates.length ≤ 28 by omega)
    · intro j
      by_cases hj : j < 10
      · simp only [ρ,dite_eq_left hj,observed]
        rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj),List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (σ a b ⟨j,hj⟩).isLt),List.getElem_ofFn]
        rfl
      · by_cases he : j = 10
        · subst j
          simp only [ρ,show ¬ 10 < 10 by decide,ite_eq_left]
          rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
          exact gift x
        · have high : 11 ≤ j := by omega
          simp only [ρ,dite_eq_right hj,ite_eq_right he]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [observed]; omega)]
  let I := 10 + u.val
  let J := 10 + v.val
  have miss : ∃ x : Fin 10 → Bool,
      (((D.wires (observed x)).getD (ρ I) false) || ((D.wires (observed x)).getD (ρ J) false)) ≠ target x := by
    rcases choices a b with h | h
    · simpa only [observed,h,target] using adjacent D (ρ I) (ρ J) newFan newCap
    · simpa only [observed,h,target] using nonadjacent D (ρ I) (ρ J) newFan newCap
  obtain ⟨x,hx⟩ := miss
  dsimp only
  intro _ _ sound
  let y := x ∘ σ a b
  let pre := (⟨[⟨.or,[a.val,b.val]⟩],0⟩ : Circuit).wires (List.ofFn y)
  have starter : pre = List.ofFn y ++ [raw x a || raw x b] := by
    change (_ ++ [raw x a || (raw x b || false)]) = _
    simp
  have mismatch : ((C.wires pre).getD I false || (C.wires pre).getD J false) ≠ target y := by
    rw [starter,physical,physical,invariant]
    exact hx
  have zsound : target y = false → (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false := sound y
  refine ⟨y,?_⟩
  change target y = true ∧ (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false
  cases ht : target y <;> cases hu : (C.wires pre).getD I false <;> cases hv : (C.wires pre).getD J false <;> simp_all only [Bool.false_eq_true, Bool.true_eq_false, Bool.false_or,Bool.true_or,not_true_eq_false, ne_eq, and_self,true_and, and_true]
