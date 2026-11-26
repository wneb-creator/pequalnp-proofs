import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_7700_73
    (hNo26 : ∀ C : Circuit, C.size ≤ 26 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      False)
    (hDisjoint : ∀ C : Circuit, C.size = 27 → IsAO2 14 C →
      let op := opnd C; let gt := gateAt C; let A := GateOp.and;
      let t (k : Fin 14) (j : ℕ) := (C.wires (List.ofFn fun i : Fin 14 => decide (i = k))).getD (14 + j) false;
      (∀ j < 27, op j 0 ≠ op j 1) → (gt 0).op = A →
      (∃ p l : Fin 7, p ∈ fanoLines l ∧ (op 0 0 = p.val ∧ op 0 1 = 7 + l.val ∨ op 0 0 = 7 + l.val ∧ op 0 1 = p.val)) →
      (circuitFun 14 C = fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      (∃ g1 g2 : ℕ, 0 < g1 ∧ g1 < 27 ∧ 0 < g2 ∧ g2 < 27 ∧ g1 ≠ g2 ∧ (gt g1).op = A ∧ (gt g2).op = A ∧
        (∀ b : Fin 2, 14 ≤ op g1 b ∧ 14 ≤ op g2 b) ∧
        t 7 g1 = true ∧ t 0 g1 = false ∧ t 0 g2 = true ∧ t 7 g2 = false ∧
        ¬ ∃ w < 27, t 0 w = true ∧ t 7 w = true) →
      False)
    (hShared : ∀ C : Circuit, C.size = 27 → IsAO2 14 C →
      let op := opnd C; let gt := gateAt C; let A := GateOp.and;
      let t (k : Fin 14) (j : ℕ) := (C.wires (List.ofFn fun i : Fin 14 => decide (i = k))).getD (14 + j) false;
      (∀ j < 27, op j 0 ≠ op j 1) → (gt 0).op = A →
      (∃ p l : Fin 7, p ∈ fanoLines l ∧ (op 0 0 = p.val ∧ op 0 1 = 7 + l.val ∨ op 0 0 = 7 + l.val ∧ op 0 1 = p.val)) →
      (circuitFun 14 C = fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      (∃ g1 g2 : ℕ, 0 < g1 ∧ g1 < 27 ∧ 0 < g2 ∧ g2 < 27 ∧ g1 ≠ g2 ∧ (gt g1).op = A ∧ (gt g2).op = A ∧
        (∀ b : Fin 2, 14 ≤ op g1 b ∧ 14 ≤ op g2 b) ∧
        t 7 g1 = true ∧ t 0 g1 = false ∧ t 0 g2 = true ∧ t 7 g2 = false ∧
        ∃ w < 27, t 0 w = true ∧ t 7 w = true) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∃ x7 < x1.size,                 ∃ x8 < x1.size,                   (0 : ℕ) < x7 ∧                     (0 : ℕ) < x8 ∧                       x7 ≠ x8 ∧                         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                           (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧                             have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = (0 : Fin (14 : ℕ))));                             have x10 : List Bool := x1.wires (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = (7 : Fin (14 : ℕ))));                             x10.getD ((14 : ℕ) + x7) Bool.false = Bool.true ∧ x9.getD ((14 : ℕ) + x7) Bool.false = Bool.false ∧ x9.getD ((14 : ℕ) + x8) Bool.false = Bool.true ∧ x10.getD ((14 : ℕ) + x8) Bool.false = Bool.false) →               False := by
  intro C hSize hAO hDist hGate0 hSpec hWit
  have hfano_iff : ∀ p l : Fin 7, p ∈ fanoLines l ↔ (p = l ∨ p = l + 1 ∨ p = l + 3) := by decide
  have hfano_eq : circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
      p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    change C.eval (List.ofFn x) = true ↔ _
    rw [hSpec x]
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, l, (hfano_iff p l).mpr hpl, hp, hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, l, (hfano_iff p l).mp hpl, hp, hl⟩
  by_cases hle26 : C.size ≤ 26
  · exact hNo26 C hle26 hAO hDist hfano_eq
  · have h27 : C.size = 27 := Nat.le_antisymm hSize (Nat.lt_of_not_ge hle26)
    let wstep : List Bool → Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have wfold_len : ∀ (gs : List Gate) (acc : List Bool),
        (gs.foldl wstep acc).length = acc.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro acc; rfl
      | cons g rest ih =>
        intro acc
        simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
    have wfold_getD_lt : ∀ (gs : List Gate) (acc : List Bool) (r : ℕ),
        r < acc.length → (gs.foldl wstep acc).getD r false = acc.getD r false := by
      intro gs
      induction gs with
      | nil => intro acc r _; rfl
      | cons g rest ih =>
        intro acc r hr
        simp only [List.foldl_cons]
        have hr' : r < (wstep acc g).length := by
          simp only [wstep, List.length_append, List.length_cons, List.length_nil]
          exact Nat.lt_succ_of_lt hr
        rw [ih (wstep acc g) r hr']
        simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
    have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
    have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
    have hgate_mem : ∀ (D : Circuit) (j : ℕ), j < D.size → gateAt D j ∈ D.gates := by
      intro D j hj
      change D.gates.getD j ⟨GateOp.or, []⟩ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hgate_len : ∀ D : Circuit, IsAO2 14 D → ∀ j < D.size, (gateAt D j).inputs.length = 2 := by
      intro D hDAO j hj
      exact hDAO.2.2 _ (hgate_mem D j hj)
    have hgate_inputs : ∀ D : Circuit, IsAO2 14 D → ∀ j < D.size,
        (gateAt D j).inputs = [opnd D j 0, opnd D j 1] := by
      intro D hDAO j hj
      have hlen2 := hgate_len D hDAO j hj
      cases hl : (gateAt D j).inputs with
      | nil => simp [hl] at hlen2
      | cons a l1 =>
        cases l1 with
        | nil => simp [hl] at hlen2
        | cons b l2 =>
          cases l2 with
          | nil =>
            have ha : opnd D j 0 = a := by change (gateAt D j).inputs.getD 0 0 = a; rw [hl]; rfl
            have hb : opnd D j 1 = b := by change (gateAt D j).inputs.getD 1 0 = b; rw [hl]; rfl
            rw [ha, hb]
          | cons c l3 => simp [hl] at hlen2
    have hgate_in_lt : ∀ D : Circuit, IsAO2 14 D → ∀ j < D.size,
        opnd D j 0 < 14 + j ∧ opnd D j 1 < 14 + j := by
      intro D hDAO j hj
      have hinputs := hgate_inputs D hDAO j hj
      have hrb := hDAO.2.1 j hj
      exact ⟨hrb _ (by simp [hinputs]), hrb _ (by simp [hinputs])⟩
    have hwire_in : ∀ (D : Circuit) (x : Fin 14 → Bool) (i : ℕ) (hi : i < 14),
        (D.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
      intro D x i hi
      change (D.gates.foldl wstep (List.ofFn x)).getD i false = x ⟨i, hi⟩
      rw [wfold_getD_lt _ _ i (by simpa using hi), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hi]
    have hwire_gate : ∀ (D : Circuit), IsAO2 14 D → ∀ (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.size),
        (D.wires (List.ofFn x)).getD (14 + j) false =
          (gateAt D j).op.eval [(D.wires (List.ofFn x)).getD (opnd D j 0) false,
            (D.wires (List.ofFn x)).getD (opnd D j 1) false] := by
      intro D hDAO x j hj
      have hj' : j < D.gates.length := hj
      have hinputs := hgate_inputs D hDAO j hj
      have hlt := hgate_in_lt D hDAO j hj
      have hgj : D.gates[j] = gateAt D j := by
        change D.gates[j] = D.gates.getD j ⟨GateOp.or, []⟩
        rw [List.getD_eq_getElem _ _ hj']
      have hsplit : D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
        rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
      let pref := (D.gates.take j).foldl wstep (List.ofFn x)
      have htake_len : (D.gates.take j).length = j := by
        rw [List.length_take]
        exact Nat.min_eq_left (Nat.le_of_lt hj')
      have hpref_len : pref.length = 14 + j := by
        dsimp only [pref]
        rw [wfold_len, List.length_ofFn, htake_len]
      have hwstep_len : (wstep pref (gateAt D j)).length = 14 + j + 1 := by
        simp only [wstep, List.length_append, List.length_cons, List.length_nil, hpref_len]
      have hwires : D.wires (List.ofFn x) =
          (D.gates.drop (j + 1)).foldl wstep (wstep pref (gateAt D j)) := by
        change D.gates.foldl wstep (List.ofFn x) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hpref_get : ∀ i < 14 + j, pref.getD i false = (D.wires (List.ofFn x)).getD i false := by
        intro i hi
        rw [hwires, wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) i
          (by rw [hwstep_len]; exact Nat.lt_succ_of_lt hi)]
        simp only [wstep, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [hpref_len]; exact hi)]
      conv_lhs => rw [hwires]
      rw [wfold_getD_lt (D.gates.drop (j + 1)) (wstep pref (gateAt D j)) (14 + j)
        (by rw [hwstep_len]; exact Nat.lt_succ_self _)]
      have hstep_at : (wstep pref (gateAt D j)).getD (14 + j) false =
          (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => pref.getD i false) := by
        simp only [wstep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [hpref_len]), hpref_len, Nat.sub_self]
        rfl
      rw [hstep_at, hinputs]
      simp only [List.map_cons, List.map_nil, hpref_get _ hlt.1, hpref_get _ hlt.2]
    have hmono : ∀ (D : Circuit), IsAO2 14 D → ∀ (x y : Fin 14 → Bool),
        (∀ i : Fin 14, x i = true → y i = true) →
        ∀ w : ℕ, (D.wires (List.ofFn x)).getD w false = true →
          (D.wires (List.ofFn y)).getD w false = true := by
      intro D hDAO x y hxy w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hw14 : w < 14
        · rw [hwire_in D x w hw14] at hw
          rw [hwire_in D y w hw14]
          exact hxy ⟨w, hw14⟩ hw
        · have hwge : 14 ≤ w := Nat.le_of_not_lt hw14
          let j := w - 14
          have hj_eq : w = 14 + j := (Nat.add_sub_of_le hwge).symm
          by_cases hj : j < D.size
          · rw [hj_eq] at hw ⊢
            rw [hwire_gate D hDAO x j hj] at hw
            rw [hwire_gate D hDAO y j hj]
            have hlt := hgate_in_lt D hDAO j hj
            have iha := ih (opnd D j 0) (by rw [hj_eq]; exact hlt.1)
            have ihb := ih (opnd D j 1) (by rw [hj_eq]; exact hlt.2)
            rcases hDAO.1 _ (hgate_mem D j hj) with hop | hop
            · rw [hop] at hw ⊢
              rw [eval_and, Bool.and_eq_true] at hw ⊢
              exact ⟨iha hw.1, ihb hw.2⟩
            · rw [hop] at hw ⊢
              rw [eval_or, Bool.or_eq_true] at hw ⊢
              rcases hw with ha | hb
              · exact Or.inl (iha ha)
              · exact Or.inr (ihb hb)
          · have hlenx : (D.wires (List.ofFn x)).length = 14 + D.size := by
              change (D.gates.foldl wstep (List.ofFn x)).length = 14 + D.size
              rw [wfold_len, List.length_ofFn]
              rfl
            have hge_len : (D.wires (List.ofFn x)).length ≤ w := by
              rw [hlenx, hj_eq]
              exact Nat.add_le_add_left (Nat.le_of_not_lt hj) 14
            rw [List.getD_eq_default _ _ hge_len] at hw
            cases hw
    let optVal : (Fin 14 → Bool) → Option ℕ → Bool :=
      fun x o => Option.casesOn (motive := fun _ => Bool) o false (fun s => (List.ofFn x).getD s false)
    let optW : List Bool → Option ℕ → Bool :=
      fun ws o => Option.casesOn (motive := fun _ => Bool) o false (fun w => ws.getD w false)
    have hCompress : ∀ (k0 : ℕ), k0 < C.size →
        ∀ (rep0 : Option ℕ), (∀ s, rep0 = some s → s < 14) →
        (∀ x : Fin 14 → Bool, optVal x rep0 = true → (C.wires (List.ofFn x)).getD (14 + k0) false = true) →
        (∀ p l : Fin 7, p ∈ fanoLines l →
          let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
          (C.wires (List.ofFn e)).getD (14 + k0) false = optVal e rep0) →
        False := by
      intro k0 hk0 rep0 hrep0 hUpper0 hEdge0
      have hBuild : ∀ n ≤ C.size, ∃ (gs : List Gate) (rep : ℕ → Option ℕ),
          IsAO2 14 ⟨gs, 0⟩ ∧
          (∀ j < gs.length, opnd ⟨gs, 0⟩ j 0 ≠ opnd ⟨gs, 0⟩ j 1) ∧
          gs.length ≤ n ∧
          (k0 < n → gs.length + 1 ≤ n) ∧
          (∀ w < 14 + n, ∀ w', rep w = some w' → w' < 14 + gs.length) ∧
          (∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + n →
            optW (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) (rep w) = true →
            (C.wires (List.ofFn x)).getD w false = true) ∧
          (∀ p l : Fin 7, p ∈ fanoLines l →
            let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
            ∀ w < 14 + n, optW (Circuit.wires ⟨gs, 0⟩ (List.ofFn e)) (rep w) =
              (C.wires (List.ofFn e)).getD w false) := by
        intro n hn
        induction n with
        | zero =>
          refine ⟨[], fun w => if w < 14 then some w else none, ?_, ?_, Nat.le_refl 0, ?_, ?_, ?_, ?_⟩
          · refine ⟨fun g hg => absurd hg (by simp), fun j hj => absurd hj (Nat.not_lt_zero j),
              fun g hg => absurd hg (by simp)⟩
          · intro j hj; exact absurd hj (Nat.not_lt_zero j)
          · intro h; exact absurd h (Nat.not_lt_zero k0)
          · intro w hw w' hr
            rw [Nat.add_zero] at hw
            simp only [hw, ↓reduceIte, Option.some.injEq] at hr
            rw [← hr]
            exact Nat.lt_of_lt_of_le hw (Nat.le_add_right 14 [].length)
          · intro x w hw hopt
            rw [Nat.add_zero] at hw
            simp only [hw, ↓reduceIte, optW] at hopt
            have h1 : (Circuit.wires ⟨[], 0⟩ (List.ofFn x)) = List.ofFn x := rfl
            rw [h1, List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hopt
            simp only [hw, ↓reduceDIte, Option.getD_some] at hopt
            rw [hwire_in C x w hw]
            exact hopt
          · intro p l _ e w hw
            rw [Nat.add_zero] at hw
            simp only [hw, ↓reduceIte, optW]
            have h1 : (Circuit.wires ⟨[], 0⟩ (List.ofFn e)) = List.ofFn e := rfl
            rw [h1, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp only [hw, ↓reduceDIte, Option.getD_some]
            exact (hwire_in C e w hw).symm
        | succ n ih =>
          obtain ⟨gs, rep, hgsAO, hgsDist, hgsLen, hgsDrop, hrepLt, hUp, hEd⟩ :=
            ih (Nat.le_trans (Nat.le_succ n) hn)
          have hn_lt : n < C.size := hn
          by_cases hnk : n = k0
          · subst hnk
            refine ⟨gs, fun w => if w = 14 + n then rep0 else rep w, hgsAO, hgsDist,
              Nat.le_trans hgsLen (Nat.le_succ n), fun _ => Nat.succ_le_succ hgsLen, ?_, ?_, ?_⟩
            · intro w hw w' hr
              by_cases hw_eq : w = 14 + n
              · simp only [hw_eq, ↓reduceIte] at hr
                exact Nat.lt_of_lt_of_le (hrep0 w' hr) (Nat.le_add_right 14 gs.length)
              · simp only [hw_eq, ↓reduceIte] at hr
                have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                exact hrepLt w hw_lt w' hr
            · intro x w hw hopt
              by_cases hw_eq : w = 14 + n
              · subst hw_eq
                simp only [↓reduceIte] at hopt
                apply hUpper0 x
                cases h0 : rep0 with
                | none => simp [h0, optW] at hopt
                | some s =>
                  simp only [h0, optW, optVal] at hopt ⊢
                  have hs14 : s < 14 := hrep0 s h0
                  have hws : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD s false = x ⟨s, hs14⟩ :=
                    hwire_in ⟨gs, 0⟩ x s hs14
                  rw [hws] at hopt
                  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
                  simp [hs14, hopt]
              · simp only [hw_eq, ↓reduceIte] at hopt
                have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                exact hUp x w hw_lt hopt
            · intro p l hpl e w hw
              by_cases hw_eq : w = 14 + n
              · subst hw_eq
                simp only [↓reduceIte]
                rw [hEdge0 p l hpl]
                cases h0 : rep0 with
                | none => rfl
                | some s =>
                  simp only [optW, optVal]
                  have hs14 : s < 14 := hrep0 s h0
                  rw [hwire_in ⟨gs, 0⟩ e s hs14, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
                  simp [hs14, e]
              · simp only [hw_eq, ↓reduceIte]
                have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                exact hEd p l hpl w hw_lt
          · have hdrop_next : k0 < n + 1 → gs.length + 1 ≤ n := by
              intro hkn
              have hk_lt : k0 < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hkn) (Ne.symm hnk)
              exact hgsDrop hk_lt
            let a := opnd C n 0
            let b := opnd C n 1
            have hab_lt := hgate_in_lt C hAO n hn_lt
            have ha_lt : a < 14 + n := hab_lt.1
            have hb_lt : b < 14 + n := hab_lt.2
            have noEmit : ∀ (r : Option ℕ), (∀ w', r = some w' → w' < 14 + gs.length) →
                (∀ x : Fin 14 → Bool, optW (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) r = true →
                  (C.wires (List.ofFn x)).getD (14 + n) false = true) →
                (∀ p l : Fin 7, p ∈ fanoLines l →
                  let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
                  optW (Circuit.wires ⟨gs, 0⟩ (List.ofFn e)) r =
                    (C.wires (List.ofFn e)).getD (14 + n) false) →
                ∃ (gs' : List Gate) (rep' : ℕ → Option ℕ),
                  IsAO2 14 ⟨gs', 0⟩ ∧
                  (∀ j < gs'.length, opnd ⟨gs', 0⟩ j 0 ≠ opnd ⟨gs', 0⟩ j 1) ∧
                  gs'.length ≤ n + 1 ∧
                  (k0 < n + 1 → gs'.length + 1 ≤ n + 1) ∧
                  (∀ w < 14 + (n + 1), ∀ w', rep' w = some w' → w' < 14 + gs'.length) ∧
                  (∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + (n + 1) →
                    optW (Circuit.wires ⟨gs', 0⟩ (List.ofFn x)) (rep' w) = true →
                    (C.wires (List.ofFn x)).getD w false = true) ∧
                  (∀ p l : Fin 7, p ∈ fanoLines l →
                    let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
                    ∀ w < 14 + (n + 1), optW (Circuit.wires ⟨gs', 0⟩ (List.ofFn e)) (rep' w) =
                      (C.wires (List.ofFn e)).getD w false) := by
              intro r hrLt hrUp hrEd
              refine ⟨gs, fun w => if w = 14 + n then r else rep w, hgsAO, hgsDist,
                Nat.le_trans hgsLen (Nat.le_succ n), fun h => Nat.le_trans (hdrop_next h) (Nat.le_succ n),
                ?_, ?_, ?_⟩
              · intro w hw w' hrw
                by_cases hw_eq : w = 14 + n
                · simp only [hw_eq, ↓reduceIte] at hrw
                  exact hrLt w' hrw
                · simp only [hw_eq, ↓reduceIte] at hrw
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  exact hrepLt w hw_lt w' hrw
              · intro x w hw hopt
                by_cases hw_eq : w = 14 + n
                · subst hw_eq
                  simp only [↓reduceIte] at hopt
                  exact hrUp x hopt
                · simp only [hw_eq, ↓reduceIte] at hopt
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  exact hUp x w hw_lt hopt
              · intro p l hpl e w hw
                by_cases hw_eq : w = 14 + n
                · subst hw_eq
                  simp only [↓reduceIte]
                  exact hrEd p l hpl
                · simp only [hw_eq, ↓reduceIte]
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  exact hEd p l hpl w hw_lt
            have doEmit : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) →
                (gateAt C n).op = op →
                ∀ (a' b' : ℕ), rep a = some a' → rep b = some b' → a' ≠ b' →
                ∃ (gs' : List Gate) (rep' : ℕ → Option ℕ),
                  IsAO2 14 ⟨gs', 0⟩ ∧
                  (∀ j < gs'.length, opnd ⟨gs', 0⟩ j 0 ≠ opnd ⟨gs', 0⟩ j 1) ∧
                  gs'.length ≤ n + 1 ∧
                  (k0 < n + 1 → gs'.length + 1 ≤ n + 1) ∧
                  (∀ w < 14 + (n + 1), ∀ w', rep' w = some w' → w' < 14 + gs'.length) ∧
                  (∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + (n + 1) →
                    optW (Circuit.wires ⟨gs', 0⟩ (List.ofFn x)) (rep' w) = true →
                    (C.wires (List.ofFn x)).getD w false = true) ∧
                  (∀ p l : Fin 7, p ∈ fanoLines l →
                    let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
                    ∀ w < 14 + (n + 1), optW (Circuit.wires ⟨gs', 0⟩ (List.ofFn e)) (rep' w) =
                      (C.wires (List.ofFn e)).getD w false) := by
              intro op hop_ao hop_eq a' b' hra hrb hne_ab
              let g' : Gate := ⟨op, [a', b']⟩
              let gs' := gs ++ [g']
              have hlen_gs' : gs'.length = gs.length + 1 := by simp [gs']
              have ha'_lt : a' < 14 + gs.length := hrepLt a ha_lt a' hra
              have hb'_lt : b' < 14 + gs.length := hrepLt b hb_lt b' hrb
              have hgs'AO : IsAO2 14 ⟨gs', 0⟩ := by
                refine ⟨?_, ?_, ?_⟩
                · intro g hg
                  rcases List.mem_append.mp hg with hg1 | hg2
                  · exact hgsAO.1 g hg1
                  · simp only [List.mem_singleton] at hg2
                    subst hg2
                    exact hop_ao
                · intro j hj i hi
                  rw [hlen_gs'] at hj
                  by_cases hj_old : j < gs.length
                  · have hgat : gateAt ⟨gs', 0⟩ j = gateAt ⟨gs, 0⟩ j := by
                      change (gs ++ [g']).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩
                      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                        List.getElem?_append_left hj_old]
                    rw [hgat] at hi
                    exact hgsAO.2.1 j hj_old i hi
                  · have hj_eq : j = gs.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (Nat.le_of_not_lt hj_old)
                    subst hj_eq
                    have hgat : gateAt ⟨gs', 0⟩ gs.length = g' := by
                      change (gs ++ [g']).getD gs.length ⟨GateOp.or, []⟩ = g'
                      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
                        Nat.sub_self]
                      rfl
                    rw [hgat] at hi
                    simp only [g', List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · exact ha'_lt
                    · exact hb'_lt
                · intro g hg
                  rcases List.mem_append.mp hg with hg1 | hg2
                  · exact hgsAO.2.2 g hg1
                  · simp only [List.mem_singleton] at hg2
                    subst hg2
                    rfl
              have hgs'Dist : ∀ j < gs'.length, opnd ⟨gs', 0⟩ j 0 ≠ opnd ⟨gs', 0⟩ j 1 := by
                intro j hj
                rw [hlen_gs'] at hj
                by_cases hj_old : j < gs.length
                · have hgat : gateAt ⟨gs', 0⟩ j = gateAt ⟨gs, 0⟩ j := by
                    change (gs ++ [g']).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩
                    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_append_left hj_old]
                  have hop0 : opnd ⟨gs', 0⟩ j 0 = opnd ⟨gs, 0⟩ j 0 := by
                    change (gateAt ⟨gs', 0⟩ j).inputs.getD 0 0 = (gateAt ⟨gs, 0⟩ j).inputs.getD 0 0
                    rw [hgat]
                  have hop1 : opnd ⟨gs', 0⟩ j 1 = opnd ⟨gs, 0⟩ j 1 := by
                    change (gateAt ⟨gs', 0⟩ j).inputs.getD 1 0 = (gateAt ⟨gs, 0⟩ j).inputs.getD 1 0
                    rw [hgat]
                  rw [hop0, hop1]
                  exact hgsDist j hj_old
                · have hj_eq : j = gs.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (Nat.le_of_not_lt hj_old)
                  subst hj_eq
                  have hgat : gateAt ⟨gs', 0⟩ gs.length = g' := by
                    change (gs ++ [g']).getD gs.length ⟨GateOp.or, []⟩ = g'
                    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
                      Nat.sub_self]
                    rfl
                  have hop0 : opnd ⟨gs', 0⟩ gs.length 0 = a' := by
                    change (gateAt ⟨gs', 0⟩ gs.length).inputs.getD 0 0 = a'
                    rw [hgat]; rfl
                  have hop1 : opnd ⟨gs', 0⟩ gs.length 1 = b' := by
                    change (gateAt ⟨gs', 0⟩ gs.length).inputs.getD 1 0 = b'
                    rw [hgat]; rfl
                  rw [hop0, hop1]
                  exact hne_ab
              have hwires_old : ∀ (x : Fin 14 → Bool) (w' : ℕ), w' < 14 + gs.length →
                  (Circuit.wires ⟨gs', 0⟩ (List.ofFn x)).getD w' false =
                    (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w' false := by
                intro x w' hw'
                have hfold_app : Circuit.wires ⟨gs', 0⟩ (List.ofFn x) =
                    wstep (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) g' := by
                  change (gs ++ [g']).foldl wstep (List.ofFn x) =
                    wstep (gs.foldl wstep (List.ofFn x)) g'
                  rw [List.foldl_append]
                  rfl
                have hlen_w : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 14 + gs.length := by
                  change (gs.foldl wstep (List.ofFn x)).length = 14 + gs.length
                  rw [wfold_len, List.length_ofFn]
                rw [hfold_app]
                simp only [wstep, List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_left (by rw [hlen_w]; exact hw')]
              have hwires_new : ∀ (x : Fin 14 → Bool),
                  (Circuit.wires ⟨gs', 0⟩ (List.ofFn x)).getD (14 + gs.length) false =
                    op.eval [(Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD a' false,
                      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD b' false] := by
                intro x
                have hfold_app : Circuit.wires ⟨gs', 0⟩ (List.ofFn x) =
                    wstep (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) g' := by
                  change (gs ++ [g']).foldl wstep (List.ofFn x) =
                    wstep (gs.foldl wstep (List.ofFn x)) g'
                  rw [List.foldl_append]
                  rfl
                have hlen_w : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 14 + gs.length := by
                  change (gs.foldl wstep (List.ofFn x)).length = 14 + gs.length
                  rw [wfold_len, List.length_ofFn]
                rw [hfold_app]
                simp only [wstep, List.getD_eq_getElem?_getD, g']
                rw [List.getElem?_append_right (by rw [hlen_w]), hlen_w, Nat.sub_self]
                rfl
              refine ⟨gs', fun w => if w = 14 + n then some (14 + gs.length) else rep w,
                hgs'AO, hgs'Dist, by rw [hlen_gs']; exact Nat.succ_le_succ hgsLen,
                fun h => by rw [hlen_gs']; exact Nat.succ_le_succ (hdrop_next h), ?_, ?_, ?_⟩
              · intro w hw w' hrw
                by_cases hw_eq : w = 14 + n
                · simp only [hw_eq, ↓reduceIte, Option.some.injEq] at hrw
                  rw [← hrw, hlen_gs']
                  exact Nat.lt_succ_self _
                · simp only [hw_eq, ↓reduceIte] at hrw
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  rw [hlen_gs']
                  exact Nat.lt_succ_of_lt (hrepLt w hw_lt w' hrw)
              · intro x w hw hopt
                by_cases hw_eq : w = 14 + n
                · subst hw_eq
                  simp only [↓reduceIte, optW] at hopt
                  rw [hwires_new x] at hopt
                  rw [hwire_gate C hAO x n hn_lt, hop_eq]
                  rcases hop_ao with rfl | rfl
                  · rw [eval_and, Bool.and_eq_true] at hopt ⊢
                    exact ⟨hUp x a ha_lt (by simpa [hra, optW] using hopt.1),
                      hUp x b hb_lt (by simpa [hrb, optW] using hopt.2)⟩
                  · rw [eval_or, Bool.or_eq_true] at hopt ⊢
                    rcases hopt with ha' | hb'
                    · exact Or.inl (hUp x a ha_lt (by simpa [hra, optW] using ha'))
                    · exact Or.inr (hUp x b hb_lt (by simpa [hrb, optW] using hb'))
                · simp only [hw_eq, ↓reduceIte] at hopt
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  apply hUp x w hw_lt
                  cases hrw : rep w with
                  | none => simp [hrw, optW] at hopt
                  | some w' =>
                    simp only [hrw, optW] at hopt ⊢
                    rwa [hwires_old x w' (hrepLt w hw_lt w' hrw)] at hopt
              · intro p l hpl e w hw
                by_cases hw_eq : w = 14 + n
                · subst hw_eq
                  simp only [↓reduceIte, optW]
                  rw [hwires_new e, hwire_gate C hAO e n hn_lt, hop_eq]
                  have ha_ed := hEd p l hpl a ha_lt
                  have hb_ed := hEd p l hpl b hb_lt
                  simp only [hra, hrb, optW] at ha_ed hb_ed
                  rw [ha_ed, hb_ed]
                · simp only [hw_eq, ↓reduceIte]
                  have hw_lt : w < 14 + n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) hw_eq
                  have he := hEd p l hpl w hw_lt
                  cases hrw : rep w with
                  | none => rw [hrw] at he; exact he
                  | some w' =>
                    simp only [hrw, optW] at he ⊢
                    rw [hwires_old e w' (hrepLt w hw_lt w' hrw)]
                    exact he
            rcases hAO.1 _ (hgate_mem C n hn_lt) with hand | hor
            · cases hra : rep a with
              | none =>
                refine noEmit none (fun _ h => by cases h)
                  (fun x h => by simp [optW] at h) (fun p l hpl => ?_)
                dsimp only
                rw [hwire_gate C hAO _ n hn_lt, hand, eval_and]
                have ha_ed := hEd p l hpl a ha_lt
                simp only [hra, optW] at ha_ed
                dsimp only [a] at ha_ed
                rw [← ha_ed, Bool.false_and]
              | some a' =>
                cases hrb : rep b with
                | none =>
                  refine noEmit none (fun _ h => by cases h)
                    (fun x h => by simp [optW] at h) (fun p l hpl => ?_)
                  dsimp only
                  rw [hwire_gate C hAO _ n hn_lt, hand, eval_and]
                  have hb_ed := hEd p l hpl b hb_lt
                  simp only [hrb, optW] at hb_ed
                  dsimp only [b] at hb_ed
                  rw [← hb_ed, Bool.and_false]
                | some b' =>
                  by_cases heq : a' = b'
                  · subst heq
                    refine noEmit (some a') (fun w' h => by cases h; exact hrepLt a ha_lt a' hra)
                      (fun x h => ?_) (fun p l hpl => ?_)
                    · rw [hwire_gate C hAO x n hn_lt, hand, eval_and, Bool.and_eq_true]
                      exact ⟨hUp x a ha_lt (by simpa [hra, optW] using h),
                        hUp x b hb_lt (by simpa [hrb, optW] using h)⟩
                    · dsimp only
                      rw [hwire_gate C hAO _ n hn_lt, hand, eval_and]
                      have ha_ed := hEd p l hpl a ha_lt
                      have hb_ed := hEd p l hpl b hb_lt
                      simp only [hra, hrb, optW] at ha_ed hb_ed
                      dsimp only [a, b] at ha_ed hb_ed
                      rw [← ha_ed, ← hb_ed, Bool.and_self]
                  · exact doEmit GateOp.and (Or.inl rfl) hand a' b' hra hrb heq
            · cases hra : rep a with
              | none =>
                cases hrb : rep b with
                | none =>
                  refine noEmit none (fun _ h => by cases h)
                    (fun x h => by simp [optW] at h) (fun p l hpl => ?_)
                  dsimp only
                  rw [hwire_gate C hAO _ n hn_lt, hor, eval_or]
                  have ha_ed := hEd p l hpl a ha_lt
                  have hb_ed := hEd p l hpl b hb_lt
                  simp only [hra, hrb, optW] at ha_ed hb_ed
                  dsimp only [a, b] at ha_ed hb_ed
                  rw [← ha_ed, ← hb_ed]
                  rfl
                | some b' =>
                  refine noEmit (some b') (fun w' h => by cases h; exact hrepLt b hb_lt b' hrb)
                    (fun x h => ?_) (fun p l hpl => ?_)
                  · rw [hwire_gate C hAO x n hn_lt, hor, eval_or, Bool.or_eq_true]
                    exact Or.inr (hUp x b hb_lt (by simpa [hrb, optW] using h))
                  · dsimp only
                    rw [hwire_gate C hAO _ n hn_lt, hor, eval_or]
                    have ha_ed := hEd p l hpl a ha_lt
                    have hb_ed := hEd p l hpl b hb_lt
                    simp only [hra, hrb, optW] at ha_ed hb_ed
                    dsimp only [a, b] at ha_ed hb_ed
                    rw [← ha_ed, ← hb_ed, Bool.false_or]
              | some a' =>
                cases hrb : rep b with
                | none =>
                  refine noEmit (some a') (fun w' h => by cases h; exact hrepLt a ha_lt a' hra)
                    (fun x h => ?_) (fun p l hpl => ?_)
                  · rw [hwire_gate C hAO x n hn_lt, hor, eval_or, Bool.or_eq_true]
                    exact Or.inl (hUp x a ha_lt (by simpa [hra, optW] using h))
                  · dsimp only
                    rw [hwire_gate C hAO _ n hn_lt, hor, eval_or]
                    have ha_ed := hEd p l hpl a ha_lt
                    have hb_ed := hEd p l hpl b hb_lt
                    simp only [hra, hrb, optW] at ha_ed hb_ed
                    dsimp only [a, b] at ha_ed hb_ed
                    rw [← ha_ed, ← hb_ed, Bool.or_false]
                | some b' =>
                  by_cases heq : a' = b'
                  · subst heq
                    refine noEmit (some a') (fun w' h => by cases h; exact hrepLt a ha_lt a' hra)
                      (fun x h => ?_) (fun p l hpl => ?_)
                    · rw [hwire_gate C hAO x n hn_lt, hor, eval_or, Bool.or_eq_true]
                      exact Or.inl (hUp x a ha_lt (by simpa [hra, optW] using h))
                    · dsimp only
                      rw [hwire_gate C hAO _ n hn_lt, hor, eval_or]
                      have ha_ed := hEd p l hpl a ha_lt
                      have hb_ed := hEd p l hpl b hb_lt
                      simp only [hra, hrb, optW] at ha_ed hb_ed
                      dsimp only [a, b] at ha_ed hb_ed
                      rw [← ha_ed, ← hb_ed, Bool.or_self]
                  · exact doEmit GateOp.or (Or.inr rfl) hor a' b' hra hrb heq
      obtain ⟨gs, rep, hgsAO, hgsDist, _, hgsDrop, hrepLt, hUp, hEd⟩ := hBuild C.size (Nat.le_refl _)
      have hgs26 : gs.length ≤ 26 := by
        have hd := hgsDrop hk0
        rw [h27] at hd
        exact Nat.le_of_succ_le_succ hd
      have hCout_lt : C.output < 14 + C.size := by
        by_contra hge
        have hle : (C.wires (List.ofFn fun i : Fin 14 => decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14)))).length ≤ C.output := by
          have hlen_w : (C.wires (List.ofFn fun i : Fin 14 => decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14)))).length = 14 + C.size := by
            change (C.gates.foldl wstep _).length = 14 + C.size
            rw [wfold_len, List.length_ofFn]
            rfl
          rw [hlen_w]
          exact Nat.le_of_not_lt hge
        have hev0 : C.eval (List.ofFn fun i : Fin 14 => decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14))) = true :=
          (hSpec _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
        have hdef : C.eval (List.ofFn fun i : Fin 14 => decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14))) = false :=
          List.getD_eq_default _ _ hle
        rw [hdef] at hev0
        cases hev0
      cases hrepOut : rep C.output with
      | none =>
        have he00 : C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7) ∨ i = Fin.natAdd 7 (0 : Fin 7))) = true :=
          (hSpec _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
        have hed := hEd (0 : Fin 7) (0 : Fin 7) (by decide) C.output hCout_lt
        simp only [hrepOut, optW] at hed
        change false = C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7) ∨ i = Fin.natAdd 7 (0 : Fin 7))) at hed
        rw [he00] at hed
        cases hed
      | some out' =>
        let D : Circuit := ⟨gs, out'⟩
        have hD26 : D.size ≤ 26 := hgs26
        have hDAO : IsAO2 14 D := hgsAO
        have hDdist : ∀ j < D.size, opnd D j 0 ≠ opnd D j 1 := hgsDist
        have hDfano : circuitFun 14 D = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7,
            p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
          funext x
          apply Bool.eq_iff_iff.mpr
          rw [decide_eq_true_eq]
          change D.eval (List.ofFn x) = true ↔ _
          constructor
          · intro hDx
            have hDx' : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD out' false = true := hDx
            have hCx : C.eval (List.ofFn x) = true :=
              hUp x C.output hCout_lt (by rw [hrepOut]; exact hDx')
            rw [hSpec x] at hCx
            rcases hCx with ⟨p, l, hpl, hp, hl⟩
            exact ⟨p, l, (hfano_iff p l).mpr hpl, hp, hl⟩
          · rintro ⟨p, l, hpl, hp, hl⟩
            let e : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
            have hCe : C.eval (List.ofFn e) = true :=
              (hSpec e).mpr ⟨p, l, (hfano_iff p l).mp hpl, by simp [e], by simp [e]⟩
            have hDe : (D.wires (List.ofFn e)).getD out' false = true := by
              have hed := hEd p l hpl C.output hCout_lt
              simp only [hrepOut, optW] at hed
              exact hed.trans hCe
            refine hmono D hDAO e x (fun i hi => ?_) out' hDe
            simp only [e, decide_eq_true_eq] at hi
            rcases hi with rfl | rfl
            · exact hp
            · exact hl
        exact hNo26 D hD26 hDAO hDdist hDfano
    have hEdge0 : ∃ p l : Fin 7, p ∈ fanoLines l ∧
        ((opnd C 0 0 = p.val ∧ opnd C 0 1 = 7 + l.val) ∨
         (opnd C 0 0 = 7 + l.val ∧ opnd C 0 1 = p.val)) := by
      by_contra hnoEdge
      apply hCompress 0 (by rw [h27]; exact Nat.zero_lt_succ 26) none (fun _ h => by cases h)
        (fun _ h => Bool.noConfusion h)
      intro p l hpl e
      rw [hwire_gate C hAO e 0 (by rw [h27]; exact Nat.zero_lt_succ 26), hGate0, eval_and]
      dsimp only [optVal]
      have hlt0 := hgate_in_lt C hAO 0 (by rw [h27]; exact Nat.zero_lt_succ 26)
      rw [Nat.add_zero] at hlt0
      rw [hwire_in C e (opnd C 0 0) hlt0.1, hwire_in C e (opnd C 0 1) hlt0.2]
      by_cases ha : (⟨opnd C 0 0, hlt0.1⟩ : Fin 14) = Fin.castAdd 7 p ∨
          (⟨opnd C 0 0, hlt0.1⟩ : Fin 14) = Fin.natAdd 7 l
      · by_cases hb : (⟨opnd C 0 1, hlt0.2⟩ : Fin 14) = Fin.castAdd 7 p ∨
            (⟨opnd C 0 1, hlt0.2⟩ : Fin 14) = Fin.natAdd 7 l
        · exfalso
          apply hnoEdge
          refine ⟨p, l, hpl, ?_⟩
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · have h0 := congrArg Fin.val ha
            have h1 := congrArg Fin.val hb
            exact absurd (h0.trans h1.symm) (hDist 0 (by rw [h27]; exact Nat.zero_lt_succ 26))
          · exact Or.inl ⟨congrArg Fin.val ha, congrArg Fin.val hb⟩
          · exact Or.inr ⟨congrArg Fin.val ha, congrArg Fin.val hb⟩
          · have h0 := congrArg Fin.val ha
            have h1 := congrArg Fin.val hb
            exact absurd (h0.trans h1.symm) (hDist 0 (by rw [h27]; exact Nat.zero_lt_succ 26))
        · have hbf : e ⟨opnd C 0 1, hlt0.2⟩ = false := decide_eq_false hb
          rw [hbf, Bool.and_false]
      · have haf : e ⟨opnd C 0 0, hlt0.1⟩ = false := decide_eq_false ha
        rw [haf, Bool.false_and]
    obtain ⟨g1, hg1, g2, hg2, hg1_pos, hg2_pos, hne, hg1_and, hg2_and, hw7_g1, hw0_g1, hw0_g2, hw7_g2⟩ := hWit
    have hg1_27 : g1 < 27 := by rwa [← h27]
    have hg2_27 : g2 < 27 := by rwa [← h27]
    have hKillInput : ∀ (g s : ℕ), g < C.size → (gateAt C g).op = GateOp.and →
        (hs14 : s < 14) →
        (C.wires (List.ofFn fun i : Fin 14 => decide (i.val = s))).getD (14 + g) false = true →
        (opnd C g 0 = s ∨ opnd C g 1 = s) → False := by
      intro g s hg hgap hs14 hws hopnd_s
      apply hCompress g hg (some s) (fun _ h => by cases h; exact hs14)
      · intro x hopt
        dsimp only [optVal] at hopt
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hopt
        simp only [hs14, ↓reduceDIte, Option.getD_some] at hopt
        have hsub : ∀ i : Fin 14, decide (i.val = s) = true → x i = true := by
          intro i hi
          rw [decide_eq_true_eq] at hi
          have : i = ⟨s, hs14⟩ := Fin.ext hi
          rwa [this]
        exact hmono C hAO (fun i => decide (i.val = s)) x hsub (14 + g) hws
      · intro p l _ e
        dsimp only [optVal]
        conv_rhs => rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hs14, ↓reduceDIte, Option.getD_some]
        rw [hwire_gate C hAO e g hg, hgap, eval_and]
        have hws_gate := hws
        rw [hwire_gate C hAO _ g hg, hgap, eval_and, Bool.and_eq_true] at hws_gate
        rcases hopnd_s with h0 | h1
        · have he0 : (C.wires (List.ofFn e)).getD (opnd C g 0) false = e ⟨s, hs14⟩ := by
            rw [h0, hwire_in C e s hs14]
          rw [he0]
          cases hes : e ⟨s, hs14⟩ with
          | false => rfl
          | true =>
            have hsub : ∀ i : Fin 14, decide (i.val = s) = true → e i = true := by
              intro i hi
              rw [decide_eq_true_eq] at hi
              have : i = ⟨s, hs14⟩ := Fin.ext hi
              rwa [this]
            have h1_true := hmono C hAO (fun i => decide (i.val = s)) e hsub (opnd C g 1) hws_gate.2
            rw [h1_true]
            rfl
        · have he1 : (C.wires (List.ofFn e)).getD (opnd C g 1) false = e ⟨s, hs14⟩ := by
            rw [h1, hwire_in C e s hs14]
          rw [he1]
          cases hes : e ⟨s, hs14⟩ with
          | false => simp
          | true =>
            have hsub : ∀ i : Fin 14, decide (i.val = s) = true → e i = true := by
              intro i hi
              rw [decide_eq_true_eq] at hi
              have : i = ⟨s, hs14⟩ := Fin.ext hi
              rwa [this]
            have h0_true := hmono C hAO (fun i => decide (i.val = s)) e hsub (opnd C g 0) hws_gate.1
            rw [h0_true]
            rfl
    have hSing : ∀ (g : ℕ) (s : Fin 14), g < C.size → (gateAt C g).op = GateOp.and →
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = s))).getD (14 + g) false = true →
        14 ≤ opnd C g 0 ∧ 14 ≤ opnd C g 1 := by
      intro g s hg hgap hws
      have hws' : (C.wires (List.ofFn fun i : Fin 14 => decide (i.val = s.val))).getD (14 + g) false = true := by
        convert hws using 4
      have hlt := hgate_in_lt C hAO g hg
      have hne_op : ∀ b : Fin 2, opnd C g b ≠ s.val := by
        intro b hb
        exact hKillInput g s.val hg hgap s.isLt hws' (by fin_cases b <;> [exact Or.inl hb; exact Or.inr hb])
      have hge : ∀ b : Fin 2, opnd C g b < 14 + g → opnd C g b ≠ s.val → 14 ≤ opnd C g b := by
        intro b hb_lt hb_ne
        by_contra hlt14
        have h14 : opnd C g b < 14 := Nat.lt_of_not_le hlt14
        have hws_gate := hws
        rw [hwire_gate C hAO _ g hg, hgap, eval_and, Bool.and_eq_true] at hws_gate
        have hval : (C.wires (List.ofFn fun i : Fin 14 => decide (i = s))).getD (opnd C g b) false = true := by
          fin_cases b
          · exact hws_gate.1
          · exact hws_gate.2
        rw [hwire_in C _ (opnd C g b) h14] at hval
        simp only [decide_eq_true_eq] at hval
        exact hb_ne (congrArg Fin.val hval)
      exact ⟨hge 0 hlt.1 (hne_op 0), hge 1 hlt.2 (hne_op 1)⟩
    have hg1_op := hSing g1 7 hg1 hg1_and hw7_g1
    have hg2_op := hSing g2 0 hg2 hg2_and hw0_g2
    have hDist27 : ∀ j < 27, opnd C j 0 ≠ opnd C j 1 := by
      intro j hj
      exact hDist j (by rw [h27]; exact hj)
    have hOp14 : ∀ b : Fin 2, 14 ≤ opnd C g1 b ∧ 14 ≤ opnd C g2 b := by
      intro b
      fin_cases b
      · exact ⟨hg1_op.1, hg2_op.1⟩
      · exact ⟨hg1_op.2, hg2_op.2⟩
    by_cases hsh : ∃ w < 27,
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = (0 : Fin 14)))).getD (14 + w) false = true ∧
        (C.wires (List.ofFn fun i : Fin 14 => decide (i = (7 : Fin 14)))).getD (14 + w) false = true
    · exact hShared C h27 hAO hDist27 hGate0 hEdge0 hfano_eq
        ⟨g1, g2, hg1_pos, hg1_27, hg2_pos, hg2_27, hne, hg1_and, hg2_and,
          hOp14, hw7_g1, hw0_g1, hw0_g2, hw7_g2, hsh⟩
    · exact hDisjoint C h27 hAO hDist27 hGate0 hEdge0 hfano_eq
        ⟨g1, g2, hg1_pos, hg1_27, hg2_pos, hg2_27, hne, hg1_and, hg2_and,
          hOp14, hw7_g1, hw0_g1, hw0_g2, hw7_g2, hsh⟩
