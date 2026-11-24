import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3821_1
    (hmono : let G : (Fin 10 → Bool) → Bool := fun x =>
    (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 28),
    D.output = 0 → D.size = 18 → PEqualNP.MetaComplexity.FanInTwo D →
    (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      ∀ j ∈ g.inputs, j ≤ 28) →
    ¬ ∀ x : Fin 10 → Bool,
      ((D.wires (List.ofFn x)).getD a.val false ||
        (D.wires (List.ofFn x)).getD b.val false) = G x)
    (hnot : let G : (Fin 10 → Bool) → Bool := fun x =>
    (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 28),
    D.output = 0 → D.size = 18 → PEqualNP.MetaComplexity.FanInTwo D →
    (∀ g ∈ D.gates, ∀ j ∈ g.inputs, j ≤ 28) →
    (∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
    let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
    let U := fun x => W x a.val || W x b.val
    (∃ x, W x a.val = true ∧ W x b.val = false) →
    (∃ x, W x a.val = false ∧ W x b.val = true) →
    (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x) →
    ∃ (s : Equiv.Perm (Fin 10)) (v : Bool) (E : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x : Fin 10 → Bool, G (x ∘ s) = G x) ∧
      PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ (if v = true then 10 else 15) ∧
      ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = U ((Fin.lastCases v y : Fin 10 → Bool) ∘ s)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  classical
  let graphValue (x : Fin 10 → Bool) : Bool :=
    (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))

  let pairAt (i j : Fin 10) (k : Fin 10) : Bool := decide (k = i ∨ k = j)

  have pairAt_count : ∀ i j : Fin 10, (List.ofFn (pairAt i j)).count true ≤ 2 := by
    decide

  have graphValue_mono {x y : Fin 10 → Bool}
      (h : ∀ i, x i = true → y i = true) (hx : graphValue x = true) :
      graphValue y = true := by
    simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
    obtain ⟨i, hi, hxy⟩ := hx
    refine ⟨i, hi, ?_⟩
    rcases hxy with (hxy | hxy) | hxy
    · exact Or.inl (Or.inl ⟨h _ hxy.1, h _ hxy.2⟩)
    · exact Or.inl (Or.inr ⟨h _ hxy.1, h _ hxy.2⟩)
    · exact Or.inr ⟨h _ hxy.1, h _ hxy.2⟩

  have graphValue_pair_witness {x : Fin 10 → Bool} (hx : graphValue x = true) :
      ∃ i j : Fin 10, graphValue (pairAt i j) = true ∧
        ∀ k, pairAt i j k = true → x k = true := by
    simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hx
    obtain ⟨i, hi, hxy⟩ := hx
    have pair_below (a b : Fin 10) (ha : x a = true) (hb : x b = true) :
        ∀ k, pairAt a b k = true → x k = true := by
      intro k hk
      simp only [pairAt, decide_eq_true_eq] at hk
      rcases hk with rfl | rfl <;> assumption
    rcases hxy with (hxy | hxy) | hxy
    · refine ⟨Fin.castAdd 5 i, Fin.castAdd 5 (i + 1), ?_, pair_below _ _ hxy.1 hxy.2⟩
      simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
      exact ⟨i, hi, Or.inl (Or.inl ⟨by simp [pairAt], by simp [pairAt]⟩)⟩
    · refine ⟨Fin.castAdd 5 i, Fin.natAdd 5 i, ?_, pair_below _ _ hxy.1 hxy.2⟩
      simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
      exact ⟨i, hi, Or.inl (Or.inr ⟨by simp [pairAt], by simp [pairAt]⟩)⟩
    · refine ⟨Fin.natAdd 5 i, Fin.natAdd 5 (i + 2), ?_, pair_below _ _ hxy.1 hxy.2⟩
      simp only [graphValue, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
      exact ⟨i, hi, Or.inr ⟨by simp [pairAt], by simp [pairAt]⟩⟩

  have monotone_promise_full (u : (Fin 10 → Bool) → Bool)
      (hm : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
      (hp : ∀ x, graphValue x = false ∨ (List.ofFn x).count true ≤ 2 →
        u x = graphValue x) :
      ∀ x, u x = graphValue x := by
    intro x
    cases hx : graphValue x with
    | false => exact (hp x (Or.inl hx)).trans hx
    | true =>
      obtain ⟨i, j, hij, below⟩ := graphValue_pair_witness hx
      exact hm (pairAt i j) x below ((hp _ (Or.inr (pairAt_count i j))).trans hij)


  have append_mono (p q : List Bool) (a b : Bool) (hlen : p.length = q.length)
      (hpq : ∀ i, p.getD i false = true → q.getD i false = true)
      (hab : a = true → b = true) :
      ∀ i, (p ++ [a]).getD i false = true → (q ++ [b]).getD i false = true := by
    intro i hi
    by_cases before : i < p.length
    · rw [List.getD_append _ _ _ _ before] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hpq i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      cases h : i - p.length with
      | zero => simpa [h] using hab (by simpa [h] using hi)
      | succ j => simp [h] at hi

  have gate_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
      (p q : List Bool) (hpq : ∀ i, p.getD i false = true → q.getD i false = true) :
      g.op.eval (g.inputs.map fun i => p.getD i false) = true →
        g.op.eval (g.inputs.map fun i => q.getD i false) = true := by
    rcases hg with hg | hg
    · rw [hg]
      change (g.inputs.map fun i => p.getD i false).all id = true →
        (g.inputs.map fun i => q.getD i false).all id = true
      simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]
      intro h i hi
      exact hpq i (h i hi)
    · rw [hg]
      change (g.inputs.map fun i => p.getD i false).any id = true →
        (g.inputs.map fun i => q.getD i false).any id = true
      simp only [List.any_map, Function.comp_def, id_eq, List.any_eq_true]
      rintro ⟨i, hi, h⟩
      exact ⟨i, hi, hpq i h⟩

  have fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (p q : List Bool) (hlen : p.length = q.length)
      (hpq : ∀ i, p.getD i false = true → q.getD i false = true) :
      ∀ i,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) p).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) q).getD i false = true := by
    induction gs generalizing p q with
    | nil => exact hpq
    | cons g gs ih =>
      apply ih (fun g h => hg g (List.mem_cons_of_mem _ h))
      · simpa using hlen
      · exact append_mono p q _ _ hlen hpq (gate_mono g (hg _ List.mem_cons_self) p q hpq)

  have ofFn_mono {n : Nat} (x y : Fin n → Bool)
      (h : ∀ i, x i = true → y i = true) :
      ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases bound : i < n
    · have get (f : Fin n → Bool) : (List.ofFn f).getD i false = f ⟨i, bound⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using bound)]
        simp
      rw [get] at hi ⊢
      exact h _ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound)] at hi
      contradiction

  have positive_wires_mono {n : Nat} (c : Circuit)
      (hc : ∀ g ∈ c.gates, g.op = .and ∨ g.op = .or)
      (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
      ∀ i, (c.wires (List.ofFn x)).getD i false = true →
        (c.wires (List.ofFn y)).getD i false = true := by
    exact fold_mono c.gates hc (List.ofFn x) (List.ofFn y) (by simp) (ofFn_mono x y h)

  have positive_two_wire_promise_full (c : Circuit) (a b : Nat)
      (hc : ∀ g ∈ c.gates, g.op = .and ∨ g.op = .or)
      (hp : ∀ x : Fin 10 → Bool, graphValue x = false ∨ (List.ofFn x).count true ≤ 2 →
        ((c.wires (List.ofFn x)).getD a false || (c.wires (List.ofFn x)).getD b false) = graphValue x) :
      ∀ x : Fin 10 → Bool,
        ((c.wires (List.ofFn x)).getD a false || (c.wires (List.ofFn x)).getD b false) = graphValue x := by
    apply monotone_promise_full _ _ hp
    intro x y hxy h
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (positive_wires_mono c hc x y hxy a) (positive_wires_mono c hc x y hxy b)

  have normalize :
      ∀ (C : Circuit) (a b : Nat), FanInTwo C → C.size ≤ 18 →
        (∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD a false = true) →
        (∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD b false = true) →
        ∃ (gs : List Gate) (a' b' : Fin 28),
          FanInTwo ⟨gs, 0⟩ ∧ gs.length = 18 ∧
          (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 28) ∧
          ∀ x : Fin 10 → Bool,
            ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a'.val false =
              (C.wires (List.ofFn x)).getD a false ∧
            ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b'.val false =
              (C.wires (List.ofFn x)).getD b false := by
    let capGate (n : ℕ) (g : Gate) : Gate :=
      ⟨g.op, g.inputs.map (fun i => min i n)⟩

    let capGates (n : ℕ) (gs : List Gate) : List Gate :=
      List.rec (motive := fun _ => ℕ → List Gate) (fun _ => [])
        (fun g _ ih k => capGate k g :: ih (k + 1)) gs n

    let capCircuit (n : ℕ) (C : Circuit) : Circuit :=
      ⟨capGates n C.gates, min C.output (n + C.gates.length)⟩

    have getD_min_length (w : List Bool) (i : ℕ) :
        w.getD (min i w.length) false = w.getD i false := by
      by_cases h : i < w.length
      · rw [Nat.min_eq_left (Nat.le_of_lt h)]
      · rw [Nat.min_eq_right (Nat.le_of_not_gt h)]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

    have capGate_eval (w : List Bool) (g : Gate) :
        (capGate w.length g).op.eval
          ((capGate w.length g).inputs.map (fun i => w.getD i false)) =
        g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
      simp only [capGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_min_length w i

    have capGates_length (n : ℕ) (gs : List Gate) :
        (capGates n gs).length = gs.length := by
      induction gs generalizing n with
      | nil => rfl
      | cons g gs ih => simp only [capGates, List.length_cons, ih]

    have capGates_wires (gs : List Gate) (w : List Bool) :
        (capGates w.length gs).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [capGates, List.foldl_cons, capGate_eval]
        have hn : (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).length =
            w.length + 1 := by simp
        rw [← hn]
        exact ih _

    have capCircuit_wires (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
        (capCircuit n C).wires x = C.wires x := by
      subst n
      exact capGates_wires C.gates x

    have wires_length (C : Circuit) (x : List Bool) :
        (C.wires x).length = x.length + C.gates.length := by
      obtain ⟨gs, o⟩ := C
      unfold Circuit.wires
      induction gs generalizing x with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp only [List.length_append, List.length_singleton]
        omega

    have capCircuit_eval (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
        (capCircuit n C).eval x = C.eval x := by
      unfold Circuit.eval
      rw [capCircuit_wires n C x hx]
      change (C.wires x).getD (min C.output (n + C.gates.length)) false =
        (C.wires x).getD C.output false
      rw [← hx, ← wires_length]
      exact getD_min_length _ _

    have capCircuit_size (n : ℕ) (C : Circuit) :
        (capCircuit n C).size = C.size :=
      capGates_length n C.gates

    have capGates_legal (n : ℕ) (gs : List Gate)
        (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) :
        ∀ g ∈ capGates n gs,
          g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2 := by
      induction gs generalizing n with
      | nil => simp [capGates]
      | cons g gs ih =>
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa [capGate] using h g List.mem_cons_self
        · exact ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) g' hg'

    have capCircuit_legal (n : ℕ) (C : Circuit) (h : FanInTwo C) :
        FanInTwo (capCircuit n C) :=
      capGates_legal n C.gates h

    have capGates_inputs_bound (n : ℕ) (gs : List Gate) :
        ∀ g ∈ capGates n gs, ∀ i ∈ g.inputs, i ≤ n + gs.length := by
      induction gs generalizing n with
      | nil => simp [capGates]
      | cons g gs ih =>
        intro g' hg' i hi
        rcases List.mem_cons.mp hg' with rfl | hg'
        · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
          have := Nat.min_le_right j n
          simp only [List.length_cons]
          omega
        · have := ih (n + 1) g' hg' i hi
          simp only [List.length_cons]
          omega

    have capCircuit_bounded (n s : ℕ) (C : Circuit) (h : C.size ≤ s) :
        (capCircuit n C).output ≤ n + s ∧
        ∀ g ∈ (capCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + s := by
      have hs : C.gates.length ≤ s := h
      constructor
      · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left hs n)
      · intro g hg i hi
        exact le_trans (capGates_inputs_bound n C.gates g hg i hi)
          (Nat.add_le_add_left hs n)

    have capCircuit_read (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
        (i : ℕ) :
        ((capCircuit n C).wires x).getD (min i (n + C.size)) false =
          (C.wires x).getD i false := by
      rw [capCircuit_wires n C x hx]
      change (C.wires x).getD (min i (n + C.gates.length)) false = _
      rw [← hx, ← wires_length]
      exact getD_min_length _ _

    have bounded_pair (n s : ℕ) (C : Circuit) (a b : ℕ) (legal : FanInTwo C)
        (budget : C.size ≤ s) :
        ∃ (D : Circuit) (a' b' : ℕ),
          FanInTwo D ∧ D.size = C.size ∧ D.output ≤ n + s ∧
          (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
          a' ≤ n + s ∧ b' ≤ n + s ∧
          ∀ x : List Bool, x.length = n →
            (D.wires x).getD a' false = (C.wires x).getD a false ∧
            (D.wires x).getD b' false = (C.wires x).getD b false := by
      refine ⟨capCircuit n C, min a (n + C.size), min b (n + C.size),
        capCircuit_legal n C legal, capCircuit_size n C,
        (capCircuit_bounded n s C budget).1, (capCircuit_bounded n s C budget).2,
        ?_, ?_, ?_⟩
      · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
      · exact le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left budget n)
      · intro x hx
        exact ⟨capCircuit_read n C x hx a, capCircuit_read n C x hx b⟩

    let padCircuit (s : ℕ) (C : Circuit) : Circuit :=
      ⟨C.gates ++ List.replicate (s - C.size) ⟨GateOp.or, []⟩, C.output⟩

    have fold_padding (k : ℕ) (w : List Bool) :
        (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
          w ++ List.replicate k false := by
      induction k generalizing w with
      | zero => simp
      | succ k ih =>
        simp only [List.replicate_succ, List.foldl_cons]
        change (List.replicate k (⟨GateOp.or, []⟩ : Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
          (w ++ [false]) = _
        rw [ih]
        simp only [List.append_assoc, List.singleton_append]

    have padCircuit_wires (s : ℕ) (C : Circuit) (x : List Bool) :
        (padCircuit s C).wires x = C.wires x ++ List.replicate (s - C.size) false := by
      unfold Circuit.wires padCircuit
      rw [List.foldl_append, fold_padding]

    have getD_append_false (w : List Bool) (k i : ℕ) :
        (w ++ List.replicate k false).getD i false = w.getD i false := by
      by_cases h : i < w.length
      · exact List.getD_append _ _ _ _ h
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_eq_default w false (by omega : w.length ≤ i)]
        simp [List.getD_eq_getElem?_getD]

    have padCircuit_read (s : ℕ) (C : Circuit) (x : List Bool) (i : ℕ) :
        ((padCircuit s C).wires x).getD i false = (C.wires x).getD i false := by
      rw [padCircuit_wires]
      exact getD_append_false _ _ _

    have padCircuit_size (s : ℕ) (C : Circuit) (h : C.size ≤ s) :
        (padCircuit s C).size = s := by
      have : C.gates.length ≤ s := h
      change (C.gates ++ List.replicate (s - C.gates.length) (⟨GateOp.or, []⟩ : Gate)).length = s
      simp only [List.length_append, List.length_replicate]
      omega

    have padCircuit_legal (s : ℕ) (C : Circuit) (h : FanInTwo C) :
        FanInTwo (padCircuit s C) := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h g hg
      · have heq := (List.mem_replicate.mp hg).2
        subst g
        simp

    intro C a b legal budget ha hb
    have hsize := padCircuit_size 18 C budget
    obtain ⟨D, a', b', hD, hlen, _, hbound, _, _, heval⟩ :=
      bounded_pair 10 18 (padCircuit 18 C) a b (padCircuit_legal 18 C legal) (by omega)
    have evals (x : Fin 10 → Bool) :
        (D.wires (List.ofFn x)).getD a' false = (C.wires (List.ofFn x)).getD a false ∧
        (D.wires (List.ofFn x)).getD b' false = (C.wires (List.ofFn x)).getD b false := by
      exact ⟨((heval _ (by simp)).1).trans (padCircuit_read 18 C _ a),
        ((heval _ (by simp)).2).trans (padCircuit_read 18 C _ b)⟩
    have hlength : D.gates.length = 18 := hlen.trans hsize
    have alt : a' < 28 := by
      obtain ⟨x, hx⟩ := ha
      have hx' : (D.wires (List.ofFn x)).getD a' false = true := (evals x).1.trans hx
      by_contra out
      rw [List.getD_eq_default _ _ (by rw [wires_length]; simp [hlength]; omega)] at hx'
      contradiction
    have blt : b' < 28 := by
      obtain ⟨x, hx⟩ := hb
      have hx' : (D.wires (List.ofFn x)).getD b' false = true := (evals x).2.trans hx
      by_contra out
      rw [List.getD_eq_default _ _ (by rw [wires_length]; simp [hlength]; omega)] at hx'
      contradiction
    exact ⟨D.gates, ⟨a', alt⟩, ⟨b', blt⟩, hD, hlength, hbound, evals⟩

  dsimp only at hmono hnot ⊢
  intro C a b legal budget ha hb promise
  obtain ⟨gs, a', b', hD, hlen, hbound, heval⟩ := normalize C a b legal budget
    (by obtain ⟨x, hx, _⟩ := ha; exact ⟨x, hx⟩)
    (by obtain ⟨x, _, hx⟩ := hb; exact ⟨x, hx⟩)
  let D : Circuit := ⟨gs, 0⟩
  have sameU (x : Fin 10 → Bool) :
      ((D.wires (List.ofFn x)).getD a'.val false || (D.wires (List.ofFn x)).getD b'.val false) =
        ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false) := by
    rw [(heval x).1, (heval x).2]
  have promiseD (x : Fin 10 → Bool)
      (hx : graphValue x = false ∨ (List.ofFn x).count true ≤ 2) :
      ((D.wires (List.ofFn x)).getD a'.val false || (D.wires (List.ofFn x)).getD b'.val false) =
        graphValue x := (sameU x).trans (promise x hx)
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · have haD : ∃ x : Fin 10 → Bool,
        (D.wires (List.ofFn x)).getD a'.val false = true ∧
          (D.wires (List.ofFn x)).getD b'.val false = false := by
      obtain ⟨x, h1, h2⟩ := ha
      exact ⟨x, (heval x).1.trans h1, (heval x).2.trans h2⟩
    have hbD : ∃ x : Fin 10 → Bool,
        (D.wires (List.ofFn x)).getD a'.val false = false ∧
          (D.wires (List.ofFn x)).getD b'.val false = true := by
      obtain ⟨x, h1, h2⟩ := hb
      exact ⟨x, (heval x).1.trans h1, (heval x).2.trans h2⟩
    obtain ⟨s, v, E, hs, hE, hsize, he⟩ :=
      hnot D a' b' rfl hlen hD hbound hn haD hbD promiseD
    refine ⟨s, v, E, hs, hE, hsize, ?_⟩
    intro y
    exact (he y).trans (sameU _)
  · have hnone (g : Gate) (hg : g ∈ gs) : g.op ≠ GateOp.not := by
      intro hop
      exact hn ⟨g, hg, hop⟩
    have hpos (g : Gate) (hg : g ∈ gs) : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have hop := (hD g hg).1
      have hne := hnone g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      tauto
    exact False.elim (hmono D a' b' rfl hlen hD
      (fun g hg => ⟨hnone g hg, hbound g hg⟩)
      (positive_two_wire_promise_full D a'.val b'.val hpos promiseD))
