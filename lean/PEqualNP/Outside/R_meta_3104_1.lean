import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3104_1
    (cofactor : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (zeroA : let f : (Fin (8 : ℕ) → Bool) → Bool := fun x => x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) || x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size = (13 : ℕ) →
        (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)), (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ))]).getD x4 Bool.false]) = f x9) →
        ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [Bool.true, Bool.true]) ≠ (f x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))))
    (smallA : let f : (Fin (8 : ℕ) → Bool) → Bool := fun x => x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) || x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 →
        (1 : ℕ) ≤ x2.size → x2.size ≤ (5 : ℕ) → x2.size + x3.size = (13 : ℕ) →
        let w : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x (1 : Fin (8 : ℕ)) || b])
        (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (w Bool.false x9 ++ [(w Bool.false x9).getD x4 Bool.false]) = f x9) →
        ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (w Bool.true x10 ++ [Bool.true]) ≠ (f x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))))
    (largeA : let f : (Fin (8 : ℕ) → Bool) → Bool := fun x => x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) || x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)) || x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) || x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) || x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) || x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 →
        (6 : ℕ) ≤ x2.size → (1 : ℕ) ≤ x3.size → x2.size + x3.size = (13 : ℕ) →
        let w : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x (1 : Fin (8 : ℕ)) || b])
        (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (w Bool.false x9 ++ [(w Bool.false x9).getD x4 Bool.false]) = f x9) →
        ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (w Bool.true x10 ++ [Bool.true]) ≠ (f x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ)))) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  let f : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  intro f0 x2 x3 x4 hfan2 hfan3 hsum w0 hbase
  dsimp only [f0, w0] at hbase ⊢
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [step]; omega
  by_cases hle12 : x2.size + x3.size ≤ 12
  · exfalso
    apply cofactor
    let n2 := x2.gates.length
    let n3 := x3.gates.length
    let r2 : ℕ → ℕ := fun i => if i < 8 then i else if i = 8 then 1 else i - 1
    let r3 : ℕ → ℕ := fun i =>
      if i < 9 + n2 then r2 i
      else if i = 9 + n2 then (if x4 < 9 + n2 then r2 x4 else 8 + n2 + n3)
      else i - 2
    let remapGate : (ℕ → ℕ) → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun r g => ⟨g.op, g.inputs.map r⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨x2.gates.map (remapGate r2) ++ x3.gates.map (remapGate r3), r3 x3.output⟩
    have hsim2 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
        w.length = w'.length + 1 → 9 ≤ w.length →
        (∀ i, w.getD i false = w'.getD (r2 i) false) →
        ∀ i, (gs.foldl step w).getD i false =
          ((gs.map (remapGate r2)).foldl step w').getD (r2 i) false := by
      intro gs
      induction gs with
      | nil => intro w w' _ _ h i; exact h i
      | cons g gs ih =>
        intro w w' hlen h9 h
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hbit : g.op.eval (g.inputs.map fun i => w.getD i false) =
            (remapGate r2 g).op.eval ((remapGate r2 g).inputs.map fun i => w'.getD i false) := by
          simp only [remapGate, List.map_map, Function.comp_def, h]
        apply ih (step w g) (step w' (remapGate r2 g))
        · simp [step]; omega
        · simp [step]; omega
        · intro i
          simp only [step, ← hbit]
          by_cases hilt : i < w.length
          · have hrlt : r2 i < w'.length := by simp only [r2]; split <;> [omega; (split <;> omega)]
            rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ hrlt]
            exact h i
          · by_cases hieq : i = w.length
            · subst hieq
              have hreq : r2 w.length = w'.length := by simp only [r2]; split <;> [omega; (split <;> omega)]
              rw [hreq, List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
              simp
            · have hrgt : w'.length + 1 ≤ r2 i := by simp only [r2]; split <;> [omega; (split <;> omega)]
              rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hsim3 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
        w.length = w'.length + 2 → 10 + n2 ≤ w.length → w'.length + gs.length ≤ 8 + n2 + n3 →
        (∀ i, w.getD i false = w'.getD (r3 i) false) →
        ∀ i, (gs.foldl step w).getD i false =
          ((gs.map (remapGate r3)).foldl step w').getD (r3 i) false := by
      intro gs
      induction gs with
      | nil => intro w w' _ _ _ h i; exact h i
      | cons g gs ih =>
        intro w w' hlen h10 hcap h
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hbit : g.op.eval (g.inputs.map fun i => w.getD i false) =
            (remapGate r3 g).op.eval ((remapGate r3 g).inputs.map fun i => w'.getD i false) := by
          simp only [remapGate, List.map_map, Function.comp_def, h]
        apply ih (step w g) (step w' (remapGate r3 g))
        · simp [step]; omega
        · simp [step]; omega
        · simp [step] at hcap ⊢; omega
        · intro i
          simp only [step, ← hbit]
          by_cases hilt : i < w.length
          · rw [List.getD_append _ _ _ _ hilt]
            by_cases hi1 : i < 9 + n2
            · have hrlt : r3 i < w'.length := by
                simp only [r3, hi1, ↓reduceIte, r2]
                split <;> [omega; (split <;> omega)]
              rw [List.getD_append _ _ _ _ hrlt]
              exact h i
            · by_cases hi2 : i = 9 + n2
              · subst hi2
                by_cases hx4 : x4 < 9 + n2
                · have hrlt : r3 (9 + n2) < w'.length := by
                    simp only [r3, lt_irrefl, ↓reduceIte, hx4, r2]
                    split <;> [omega; (split <;> omega)]
                  rw [List.getD_append _ _ _ _ hrlt]
                  exact h (9 + n2)
                · have hreq : r3 (9 + n2) = 8 + n2 + n3 := by simp [r3, hx4]
                  have h0 := h (9 + n2)
                  rw [hreq] at h0 ⊢
                  rw [List.getD_eq_default w' false (by simp at hcap; omega)] at h0
                  rw [h0, List.getD_eq_default _ false (by simp at hcap ⊢; omega)]
              · have hrlt : r3 i < w'.length := by simp only [r3, hi1, hi2, ↓reduceIte]; omega
                rw [List.getD_append _ _ _ _ hrlt]
                exact h i
          · by_cases hieq : i = w.length
            · subst hieq
              have hreq : r3 w.length = w'.length := by
                have h1 : ¬ w.length < 9 + n2 := by omega
                have h2 : w.length ≠ 9 + n2 := by omega
                simp [r3, h1, h2]; omega
              rw [hreq, List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
              simp
            · have hrgt : w'.length + 1 ≤ r3 i := by
                have h1 : ¬ i < 9 + n2 := by omega
                have h2 : i ≠ 9 + n2 := by omega
                simp [r3, h1, h2]; omega
              rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    refine ⟨C, ?_, ?_, ?_⟩
    · intro g hg
      simp only [C, List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
      · obtain ⟨hop, hlen⟩ := hfan2 g0 hg0
        exact ⟨hop, by simp [remapGate, hlen]⟩
      · obtain ⟨hop, hlen⟩ := hfan3 g0 hg0
        exact ⟨hop, by simp [remapGate, hlen]⟩
    · change (x2.gates.map (remapGate r2) ++ x3.gates.map (remapGate r3)).length ≤ 12
      simp only [List.length_append, List.length_map]
      exact hle12
    · intro x
      have hinit2 : ∀ i, (List.ofFn x ++ [x 1]).getD i false = (List.ofFn x).getD (r2 i) false := by
        intro i
        by_cases h8 : i < 8
        · simp only [r2, h8, ↓reduceIte]
          rw [List.getD_append _ _ _ _ (by simp; omega)]
        · by_cases he8 : i = 8
          · subst he8
            simp only [r2, lt_irrefl, ↓reduceIte]
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp [List.getD_eq_getElem?_getD]
          · have hge9 : 9 ≤ i := by omega
            simp only [r2, h8, he8, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hw2 : ∀ i, (x2.wires (List.ofFn x ++ [x 1])).getD i false =
          ((x2.gates.map (remapGate r2)).foldl step (List.ofFn x)).getD (r2 i) false :=
        hsim2 x2.gates (List.ofFn x ++ [x 1]) (List.ofFn x) (by simp) (by simp) hinit2
      let w2 := x2.wires (List.ofFn x ++ [x 1])
      let w2' := (x2.gates.map (remapGate r2)).foldl step (List.ofFn x)
      have hw2_len : w2.length = 9 + n2 := by
        change (x2.gates.foldl step (List.ofFn x ++ [x 1])).length = 9 + n2
        rw [step_len]; simp [n2]
      have hw2'_len : w2'.length = 8 + n2 := by
        change ((x2.gates.map (remapGate r2)).foldl step (List.ofFn x)).length = 8 + n2
        rw [step_len]; simp [n2]
      have hinit3 : ∀ i, (w2 ++ [w2.getD x4 false]).getD i false = w2'.getD (r3 i) false := by
        intro i
        by_cases hi1 : i < 9 + n2
        · simp only [r3, hi1, ↓reduceIte]
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hw2 i
        · by_cases hi2 : i = 9 + n2
          · subst hi2
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp only [hw2_len, Nat.sub_self, List.getD_cons_zero, r3, lt_irrefl, ↓reduceIte]
            by_cases hx4 : x4 < 9 + n2
            · simp only [hx4, ↓reduceIte]
              exact hw2 x4
            · simp only [hx4, ↓reduceIte]
              rw [List.getD_eq_default w2 false (by omega), List.getD_eq_default w2' false (by omega)]
          · simp only [r3, hi1, hi2, ↓reduceIte]
            rw [List.getD_eq_default _ _ (by simp [hw2_len]; omega), List.getD_eq_default w2' false (by omega)]
      have hw3 := hsim3 x3.gates (w2 ++ [w2.getD x4 false]) w2'
        (by simp [hw2_len, hw2'_len]; omega) (by simp [hw2_len]; omega) (by simp [hw2'_len, n3]) hinit3 x3.output
      have hceval : C.eval (List.ofFn x) = ((x3.gates.map (remapGate r3)).foldl step w2').getD (r3 x3.output) false := by
        change ((x2.gates.map (remapGate r2) ++ x3.gates.map (remapGate r3)).foldl step (List.ofFn x)).getD (r3 x3.output) false = _
        rw [List.foldl_append]
      rw [hceval, ← hw3]
      change x3.eval (w2 ++ [w2.getD x4 false]) = f x
      simpa only [w2, Bool.or_false] using hbase x
  · have heq13 : x2.size + x3.size = 13 := by omega
    by_cases h3zero : x3.size = 0
    · have h3nil : x3.gates = [] := List.eq_nil_of_length_eq_zero h3zero
      have h3eval : ∀ l : List Bool, x3.eval l = l.getD x3.output false := by
        intro l
        change (x3.gates.foldl step l).getD x3.output false = _
        rw [h3nil]; rfl
      have hlen : ∀ (b : Bool) (x : Fin 8 → Bool), (x2.wires (List.ofFn x ++ [x 1 || b])).length = 9 + x2.gates.length := by
        intro b x
        change (x2.gates.foldl step (List.ofFn x ++ [x 1 || b])).length = 9 + x2.gates.length
        rw [step_len]; simp
      by_cases hout1 : x3.output < 9 + x2.gates.length
      · let xstar : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
        refine ⟨xstar, ?_⟩
        have hsame : x2.wires (List.ofFn xstar ++ [xstar 1 || true]) =
            x2.wires (List.ofFn xstar ++ [xstar 1 || false]) := by
          have hx1 : xstar 1 = true := by decide
          rw [hx1]; rfl
        rw [h3eval, List.getD_append _ _ _ _ (by rw [hlen]; exact hout1), hsame]
        have hb := hbase xstar
        rw [h3eval, List.getD_append _ _ _ _ (by rw [hlen]; exact hout1)] at hb
        rw [hb]
        decide
      · by_cases hout2 : x3.output = 9 + x2.gates.length
        · refine ⟨fun _ => false, ?_⟩
          rw [h3eval, List.getD_append_right _ _ _ _ (by rw [hlen]; omega)]
          simp only [hlen, hout2, Nat.sub_self, List.getD_cons_zero]
          decide
        · refine ⟨fun _ => true, ?_⟩
          rw [h3eval, List.getD_eq_default _ _ (by rw [List.length_append, hlen]; simp; omega)]
          decide
    · by_cases h2zero : x2.size = 0
      · have h2nil : x2.gates = [] := List.eq_nil_of_length_eq_zero h2zero
        have h2wires : ∀ l : List Bool, x2.wires l = l := by
          intro l
          change x2.gates.foldl step l = l
          rw [h2nil]; rfl
        have hbase0 : ∀ (x9 : Fin 8 → Bool),
            x3.eval (List.ofFn x9 ++ [x9 1, (List.ofFn x9 ++ [x9 1]).getD x4 false]) = f x9 := by
          intro x9
          have hb := hbase x9
          simpa only [h2wires, Bool.or_false, List.append_assoc, List.cons_append, List.nil_append] using hb
        obtain ⟨x10, hx10⟩ := zeroA x3 x4 hfan3 (by omega) hbase0
        refine ⟨x10, ?_⟩
        simpa only [h2wires, Bool.or_true, List.append_assoc, List.cons_append, List.nil_append] using hx10
      · by_cases h2le5 : x2.size ≤ 5
        · exact smallA x2 x3 x4 hfan2 hfan3 (by omega) h2le5 heq13 hbase
        · exact largeA x2 x3 x4 hfan2 hfan3 (by omega) (by omega) heq13 hbase
