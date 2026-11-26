import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7217_317
    (pureCircuit :
      let edge := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let reads := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) →
        (∀ v : Fin 10, (C.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length ≤ 3) →
        ∃ (v : Fin 10) (D : Circuit), FanInTwo D ∧ D.size + 4 ≤ C.size ∧
          ∀ x : Fin 10 → Bool, x v = false → D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (usesExtra :
      let edge := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let pre := fun x : Fin 10 → Bool => List.ofFn x ++ [x 0 && x 2]
      let reads := fun g : Gate => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
        (∀ x : Fin 10 → Bool, C.eval (pre x) = edge x) →
        (∃ g ∈ C.gates, 10 ∈ reads g) →
        (∀ v : Fin 10, (C.gates.filter fun g => (reads g).any fun i =>
          decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))).length ≤ 3) →
        ∃ (v : Fin 10) (D : Circuit), FanInTwo D ∧ D.size + 4 ≤ C.size ∧
          ∀ x : Fin 10 → Bool, x v = false → D.eval (pre x) = C.eval (pre x)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (10 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (10 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (10 : ℕ) → Fin (10 : ℕ)) → (Fin (10 : ℕ) → Bool) → List Bool := fun (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Fin (10 : ℕ) → Bool) => List.ofFn (x3 ∘ x2) ++ [x3 (0 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (18 : ℕ) → (∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2 x4 x7) = x1 x7) → ∃ (x8 : Fin (10 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (4 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (10 : ℕ) → Bool), x10 x8 = Bool.false → x9.eval (x2 x4 x10) = x3.eval (x2 x4 x10) := by
  let edge : (Fin 10 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  let pre : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 2]
  let reads : Gate → List ℕ := fun g => GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
  have wires_len (gs : List Gate) (w : List Bool) :
      ((Circuit.mk gs 0).wires w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => exact (Nat.add_zero _).symm
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w ++ [_])).length = _
      rw [ih]
      simp
      omega
  have wires_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w ++ [_])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
  have wires_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires w =
        let ws := (Circuit.mk gs 0).wires w
        ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)] := by
    exact List.foldl_append
  have rewire_perm :
      ∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C →
        ∃ E : Circuit, FanInTwo E ∧ E.size = C.size ∧
          ∀ x : Fin 10 → Bool, E.eval (pre x) = C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) := by
    intro C p hC
    let rename (i : ℕ) : ℕ := if hi : i < 10 then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < 10) : rename i < 10 := by
      simp [rename, hi]
    have late (i : ℕ) (hi : 10 ≤ i) : rename i = i := by
      simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let E : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hC g' hg').1, by simpa [mapGate] using (hC g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length) (lo : 10 ≤ x.length)
        (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have step : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [step]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases h10 : i < 10
            · have := early i h10
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x
    apply run C.gates _ _ (by simp [pre]) (by simp) _ C.output
    intro i
    by_cases hi : i < 10
    · have h1 : rename i < (List.ofFn x).length := by simpa using early i hi
      have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      simp [rename, hi]
    · rw [late i (by omega),
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have rewire_inv :
      ∀ (D : Circuit) (p q : Fin 10 → Fin 10), (∀ i, p (q i) = i) → FanInTwo D →
        ∃ D' : Circuit, FanInTwo D' ∧ D'.size = D.size ∧
          ∀ x : Fin 10 → Bool, D'.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = D.eval (pre x) := by
    intro D p q hpq hD
    let rename (i : ℕ) : ℕ := if hi : i < 10 then (q ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < 10) : rename i < 10 := by
      simp [rename, hi]
    have late (i : ℕ) (hi : 10 ≤ i) : rename i = i := by
      simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D' : Circuit := ⟨D.gates.map mapGate, rename D.output⟩
    refine ⟨D', ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hD g' hg').1, by simpa [mapGate] using (hD g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length) (lo : 10 ≤ x.length)
        (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have step : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [step]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases h10 : i < 10
            · have := early i h10
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x
    apply run D.gates _ _ (by simp [pre]) (by simp [pre]) _ D.output
    intro i
    by_cases hi : i < 10
    · have h1 : rename i < (List.ofFn (x ∘ p)).length := by simpa using early i hi
      have h2 : i < (List.ofFn x).length := by simpa using hi
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [List.getElem_ofFn, Function.comp_apply]
      have hidx : (⟨rename i, early i hi⟩ : Fin 10) = q ⟨i, hi⟩ := by
        apply Fin.ext
        simp [rename, hi]
      rw [hidx, hpq ⟨i, hi⟩]
    · rw [late i (by omega),
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have bij_of_computes :
      ∀ (C : Circuit) (p : Fin 10 → Fin 10),
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = edge x) →
        Function.Bijective p := by
    intro C p hcomp
    have hsurj : Function.Surjective p := by
      intro v
      by_contra hmiss
      push Not at hmiss
      let nb : Fin 10 → Fin 10 := fun j =>
        ([1, 0, 1, 4, 3, 7, 8, 5, 6, 4] : List (Fin 10)).getD j.val 4
      let xF : Fin 10 → Bool := fun j => decide (j = nb v)
      let xT : Fin 10 → Bool := fun j => decide (j = nb v ∨ j = v)
      have hdiff : edge xF ≠ edge xT := by
        have h : ∀ u : Fin 10,
            edge (fun j => decide (j = nb u)) ≠ edge (fun j => decide (j = nb u ∨ j = u)) := by
          decide
        exact h v
      have hsame_comp : xF ∘ p = xT ∘ p := by
        funext i
        have hne : p i ≠ v := hmiss i
        simp [xF, xT, hne]
      have hsame_extra : (xF 0 && xF 2) = (xT 0 && xT 2) := by
        have h : ∀ u : Fin 10,
            (decide ((0 : Fin 10) = nb u) && decide ((2 : Fin 10) = nb u)) =
            (decide ((0 : Fin 10) = nb u ∨ (0 : Fin 10) = u) &&
             decide ((2 : Fin 10) = nb u ∨ (2 : Fin 10) = u)) := by
          decide
        exact h v
      have heq : C.eval (List.ofFn (xF ∘ p) ++ [xF 0 && xF 2]) =
          C.eval (List.ofFn (xT ∘ p) ++ [xT 0 && xT 2]) := by
        rw [hsame_comp, hsame_extra]
      rw [hcomp xF, hcomp xT] at heq
      exact hdiff heq
    exact ⟨(Finite.injective_iff_surjective (f := p)).mpr hsurj, hsurj⟩
  have elim_high :
      ∀ (E : Circuit) (v : Fin 10), FanInTwo E →
        (∀ x : Fin 10 → Bool, E.eval (pre x) = edge x) →
        let killed : ℕ → Bool := fun i => decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))
        4 ≤ (E.gates.filter fun g => (reads g).any killed).length →
        ∃ D : Circuit, FanInTwo D ∧ D.size + 4 ≤ E.size ∧
          ∀ x : Fin 10 → Bool, x v = false → D.eval (pre x) = E.eval (pre x) := by
    intro E v hE hcomp killed h4
    let evalVal : List Bool → (Bool ⊕ ℕ) → Bool := fun w =>
      Sum.elim id (fun u => w.getD u false)
    let stepAnd2 (gs : List Gate) (env : List (Bool ⊕ ℕ)) (a b : Bool ⊕ ℕ) :
        List Gate × List (Bool ⊕ ℕ) :=
      Sum.casesOn a
        (fun ca => Bool.casesOn ca (gs, env ++ [Sum.inl false]) (gs, env ++ [b]))
        (fun ua => Sum.casesOn b
          (fun cb => Bool.casesOn cb (gs, env ++ [Sum.inl false]) (gs, env ++ [Sum.inr ua]))
          (fun ub => (gs ++ [⟨.and, [ua, ub]⟩], env ++ [Sum.inr (11 + gs.length)])))
    let stepOr2 (gs : List Gate) (env : List (Bool ⊕ ℕ)) (a b : Bool ⊕ ℕ) :
        List Gate × List (Bool ⊕ ℕ) :=
      Sum.casesOn a
        (fun ca => Bool.casesOn ca (gs, env ++ [b]) (gs, env ++ [Sum.inl true]))
        (fun ua => Sum.casesOn b
          (fun cb => Bool.casesOn cb (gs, env ++ [Sum.inr ua]) (gs, env ++ [Sum.inl true]))
          (fun ub => (gs ++ [⟨.or, [ua, ub]⟩], env ++ [Sum.inr (11 + gs.length)])))
    let step : (List Gate × List (Bool ⊕ ℕ)) → Gate → (List Gate × List (Bool ⊕ ℕ)) :=
      fun st g =>
        let gs := st.1
        let env := st.2
        let vals := g.inputs.map (fun i => env.getD i (Sum.inl false))
        GateOp.casesOn (motive := fun _ => List Gate × List (Bool ⊕ ℕ)) g.op
          (List.casesOn vals (gs, env ++ [Sum.inl true]) fun a rest =>
            List.casesOn rest (gs, env ++ [a]) fun b rest2 =>
              List.casesOn rest2 (stepAnd2 gs env a b) fun _ _ => (gs, env ++ [Sum.inl false]))
          (List.casesOn vals (gs, env ++ [Sum.inl false]) fun a rest =>
            List.casesOn rest (gs, env ++ [a]) fun b rest2 =>
              List.casesOn rest2 (stepOr2 gs env a b) fun _ _ => (gs, env ++ [Sum.inl false]))
          (List.casesOn vals (gs, env ++ [Sum.inl true]) fun a _ =>
            Sum.casesOn a
              (fun ca => (gs, env ++ [Sum.inl (!ca)]))
              (fun ua => (gs ++ [⟨.not, [ua]⟩], env ++ [Sum.inr (11 + gs.length)])))
          (fun _ => (gs, env ++ [Sum.inl false]))
          (gs, env ++ [Sum.inl false])
    let initEnv : List (Bool ⊕ ℕ) :=
      List.ofFn fun i : Fin 11 => if killed i.val then Sum.inl false else Sum.inr i.val
    have inv :
        ∀ (pref : List Gate),
          FanInTwo ⟨pref, 0⟩ →
          let st := pref.foldl step ([], initEnv)
          FanInTwo ⟨st.1, 0⟩ ∧
          st.2.length = 11 + pref.length ∧
          st.1.length + (pref.filter fun g => (reads g).any killed).length ≤ pref.length ∧
          (∀ i : ℕ, i < 11 → killed i = true → st.2.getD i (Sum.inl false) = Sum.inl false) ∧
          (∀ i u, st.2.getD i (Sum.inl false) = Sum.inr u → u < 11 + st.1.length) ∧
          (∀ x : Fin 10 → Bool, x v = false → ∀ i : ℕ,
            ((Circuit.mk pref 0).wires (pre x)).getD i false =
              evalVal ((Circuit.mk st.1 0).wires (pre x)) (st.2.getD i (Sum.inl false))) := by
      intro pref
      induction pref using List.reverseRecOn with
      | nil =>
        intro _
        dsimp only [List.foldl]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg; cases hg
        · simp [initEnv]
        · simp
        · intro i hi hk
          have hlen : i < initEnv.length := by simp [initEnv, hi]
          rw [List.getD_eq_getElem _ _ hlen]
          simp only [initEnv, List.getElem_ofFn, hk, ↓reduceIte]
        · intro i u hu
          by_cases hi : i < 11
          · have hlen : i < initEnv.length := by simp [initEnv, hi]
            rw [List.getD_eq_getElem _ _ hlen] at hu
            simp only [initEnv, List.getElem_ofFn] at hu
            split_ifs at hu with hk
            cases hu
            simp; omega
          · rw [List.getD_eq_default _ _ (by simp [initEnv]; omega)] at hu
            cases hu
        · intro x hx i
          change (pre x).getD i false = evalVal (pre x) (initEnv.getD i (Sum.inl false))
          by_cases hi : i < 11
          · have hlen : i < initEnv.length := by simp [initEnv, hi]
            rw [List.getD_eq_getElem _ _ hlen]
            simp only [initEnv, List.getElem_ofFn]
            split_ifs with hk
            · simp only [evalVal]
              have hk' : i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10) := of_decide_eq_true hk
              rcases hk' with rfl | ⟨hv02, rfl⟩
              · have h10 : v.val < (List.ofFn x).length := by simp
                rw [List.getD_append _ _ _ _ h10, List.getD_eq_getElem _ _ h10, List.getElem_ofFn]
                exact hx
              · rw [List.getD_append_right _ _ _ _ (by simp)]
                rcases hv02 with rfl | rfl <;> simp [hx]
            · rfl
          · rw [List.getD_eq_default _ _ (by simp [pre]; omega),
                List.getD_eq_default _ _ (by simp [initEnv]; omega)]
            rfl
      | append_singleton pref g ih =>
        intro hpf
        have hpref : FanInTwo ⟨pref, 0⟩ := fun h hh => hpf h (List.mem_append_left _ hh)
        have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
          hpf g (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨hfan, hlen, hsz, hkill, hbd, heval⟩ := ih hpref
        set st := pref.foldl step ([], initEnv)
        have hfold : (pref ++ [g]).foldl step ([], initEnv) = step st g := by
          simp [List.foldl_append, st]
        rw [hfold]
        have hkill_any : (reads g).any killed = true →
            (step st g).1 = st.1 := by
          intro hany
          obtain ⟨idx, hidx, hki⟩ := List.any_eq_true.mp hany
          have hlt : idx < 11 := by
            have hk' := of_decide_eq_true hki
            rcases hk' with rfl | ⟨_, rfl⟩
            · exact Nat.lt_trans v.isLt (by decide)
            · decide
          have hval : st.2.getD idx (Sum.inl false) = Sum.inl false := hkill idx hlt hki
          obtain ⟨hop, hilen⟩ := hg
          rcases g with ⟨op, ins⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl | rfl
          · simp [reads] at hidx
            rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · cases hidx
            · rfl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hidx
              rcases hidx with rfl | rfl
              · simp only [step, stepAnd2, List.map_cons, List.map_nil, hval]
              · cases h1 : st.2.getD a (Sum.inl false) with
                | inl c => cases c <;> simp only [step, stepAnd2, List.map_cons, List.map_nil, h1, hval]
                | inr u => simp only [step, stepAnd2, List.map_cons, List.map_nil, h1, hval]
            · simp at hilen
          · simp [reads] at hidx
            rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · cases hidx
            · rfl
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hidx
              rcases hidx with rfl | rfl
              · simp only [step, stepOr2, List.map_cons, List.map_nil, hval]
              · cases h1 : st.2.getD a (Sum.inl false) with
                | inl c => cases c <;> simp only [step, stepOr2, List.map_cons, List.map_nil, h1, hval]
                | inr u => simp only [step, stepOr2, List.map_cons, List.map_nil, h1, hval]
            · simp at hilen
          · simp [reads] at hidx
            rcases ins with _ | ⟨a, rest⟩
            · cases hidx
            · simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hidx
              subst hidx
              simp only [step, List.map_cons, hval]
        have hstep_core :
            FanInTwo ⟨(step st g).1, 0⟩ ∧
            (step st g).2.length = st.2.length + 1 ∧
            (step st g).1.length ≤ st.1.length + 1 ∧
            (∃ tail, (step st g).1 = st.1 ++ tail) ∧
            (∃ outv, (step st g).2 = st.2 ++ [outv] ∧
              (∀ u, outv = Sum.inr u → u < 11 + (step st g).1.length) ∧
              ∀ x : Fin 10 → Bool, x v = false →
                g.op.eval (g.inputs.map fun i => ((Circuit.mk pref 0).wires (pre x)).getD i false) =
                  evalVal ((Circuit.mk (step st g).1 0).wires (pre x)) outv) := by
          obtain ⟨hop, hilen⟩ := hg
          rcases g with ⟨op, ins⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl | rfl
          · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · have hst : step st ⟨.and, []⟩ = (st.1, st.2 ++ [Sum.inl true]) := rfl
              rw [hst]
              refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl true, rfl, (by intro u h; cases h), ?_⟩
              intro x _; rfl
            · have hst : step st ⟨.and, [a]⟩ = (st.1, st.2 ++ [st.2.getD a (Sum.inl false)]) := rfl
              rw [hst]
              refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, st.2.getD a (Sum.inl false), rfl, fun u hu => hbd a u hu, ?_⟩
              intro x hx
              simp only [List.map_cons, List.map_nil, heval x hx a]
              exact Bool.and_true _
            · cases ha : st.2.getD a (Sum.inl false) with
              | inl ca =>
                cases ca
                · have hst : step st ⟨.and, [a, b]⟩ = (st.1, st.2 ++ [Sum.inl false]) := by
                    simp only [step, stepAnd2, List.map_cons, List.map_nil, ha]
                  rw [hst]
                  refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl false, rfl, (by intro u h; cases h), ?_⟩
                  intro x hx
                  simp only [List.map_cons, List.map_nil, heval x hx a, ha, evalVal, Sum.elim_inl, id_eq]
                  rfl
                · have hst : step st ⟨.and, [a, b]⟩ = (st.1, st.2 ++ [st.2.getD b (Sum.inl false)]) := by
                    simp only [step, stepAnd2, List.map_cons, List.map_nil, ha]
                  rw [hst]
                  refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, st.2.getD b (Sum.inl false), rfl, fun u hu => hbd b u hu, ?_⟩
                  intro x hx
                  simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, evalVal, Sum.elim_inl, id_eq]
                  exact Bool.and_true _
              | inr ua =>
                cases hb : st.2.getD b (Sum.inl false) with
                | inl cb =>
                  cases cb
                  · have hst : step st ⟨.and, [a, b]⟩ = (st.1, st.2 ++ [Sum.inl false]) := by
                      simp only [step, stepAnd2, List.map_cons, List.map_nil, ha, hb]
                    rw [hst]
                    refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl false, rfl, (by intro u h; cases h), ?_⟩
                    intro x hx
                    simp only [List.map_cons, List.map_nil, heval x hx b, hb, evalVal, Sum.elim_inl, id_eq]
                    exact Bool.and_false _
                  · have hst : step st ⟨.and, [a, b]⟩ = (st.1, st.2 ++ [Sum.inr ua]) := by
                      simp only [step, stepAnd2, List.map_cons, List.map_nil, ha, hb]
                    rw [hst]
                    refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inr ua, rfl, (fun u hu => by cases hu; exact hbd a ua ha), ?_⟩
                    intro x hx
                    simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, hb, evalVal, Sum.elim_inl, Sum.elim_inr, id_eq]
                    exact Bool.and_true _
                | inr ub =>
                  have hst : step st ⟨.and, [a, b]⟩ = (st.1 ++ [⟨.and, [ua, ub]⟩], st.2 ++ [Sum.inr (11 + st.1.length)]) := by
                    simp only [step, stepAnd2, List.map_cons, List.map_nil, ha, hb]
                  rw [hst]
                  refine ⟨?_, by simp, by simp, ⟨[⟨.and, [ua, ub]⟩], rfl⟩, Sum.inr (11 + st.1.length), rfl, (by intro u hu; cases hu; simp), ?_⟩
                  · intro h hh
                    simp only [List.mem_append, List.mem_singleton] at hh
                    rcases hh with hh | rfl
                    · exact hfan h hh
                    · exact ⟨by simp, by simp⟩
                  · intro x hx
                    simp only [evalVal, Sum.elim_inr]
                    rw [wires_snoc]
                    have hwl : ((Circuit.mk st.1 0).wires (pre x)).length = 11 + st.1.length := by
                      rw [wires_len]; simp [pre]
                    rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self]
                    simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, hb, evalVal, Sum.elim_inr, List.getD_cons_zero]
            · simp at hilen
          · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · have hst : step st ⟨.or, []⟩ = (st.1, st.2 ++ [Sum.inl false]) := rfl
              rw [hst]
              refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl false, rfl, (by intro u h; cases h), ?_⟩
              intro x _; rfl
            · have hst : step st ⟨.or, [a]⟩ = (st.1, st.2 ++ [st.2.getD a (Sum.inl false)]) := rfl
              rw [hst]
              refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, st.2.getD a (Sum.inl false), rfl, fun u hu => hbd a u hu, ?_⟩
              intro x hx
              simp only [List.map_cons, List.map_nil, heval x hx a]
              exact Bool.or_false _
            · cases ha : st.2.getD a (Sum.inl false) with
              | inl ca =>
                cases ca
                · have hst : step st ⟨.or, [a, b]⟩ = (st.1, st.2 ++ [st.2.getD b (Sum.inl false)]) := by
                    simp only [step, stepOr2, List.map_cons, List.map_nil, ha]
                  rw [hst]
                  refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, st.2.getD b (Sum.inl false), rfl, fun u hu => hbd b u hu, ?_⟩
                  intro x hx
                  simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, evalVal, Sum.elim_inl, id_eq]
                  exact Bool.or_false _
                · have hst : step st ⟨.or, [a, b]⟩ = (st.1, st.2 ++ [Sum.inl true]) := by
                    simp only [step, stepOr2, List.map_cons, List.map_nil, ha]
                  rw [hst]
                  refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl true, rfl, (by intro u h; cases h), ?_⟩
                  intro x hx
                  simp only [List.map_cons, List.map_nil, heval x hx a, ha, evalVal, Sum.elim_inl, id_eq]
                  rfl
              | inr ua =>
                cases hb : st.2.getD b (Sum.inl false) with
                | inl cb =>
                  cases cb
                  · have hst : step st ⟨.or, [a, b]⟩ = (st.1, st.2 ++ [Sum.inr ua]) := by
                      simp only [step, stepOr2, List.map_cons, List.map_nil, ha, hb]
                    rw [hst]
                    refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inr ua, rfl, (fun u hu => by cases hu; exact hbd a ua ha), ?_⟩
                    intro x hx
                    simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, hb, evalVal, Sum.elim_inl, Sum.elim_inr, id_eq]
                    exact Bool.or_false _
                  · have hst : step st ⟨.or, [a, b]⟩ = (st.1, st.2 ++ [Sum.inl true]) := by
                      simp only [step, stepOr2, List.map_cons, List.map_nil, ha, hb]
                    rw [hst]
                    refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl true, rfl, (by intro u h; cases h), ?_⟩
                    intro x hx
                    simp only [List.map_cons, List.map_nil, heval x hx b, hb, evalVal, Sum.elim_inl, id_eq]
                    exact Bool.or_true _
                | inr ub =>
                  have hst : step st ⟨.or, [a, b]⟩ = (st.1 ++ [⟨.or, [ua, ub]⟩], st.2 ++ [Sum.inr (11 + st.1.length)]) := by
                    simp only [step, stepOr2, List.map_cons, List.map_nil, ha, hb]
                  rw [hst]
                  refine ⟨?_, by simp, by simp, ⟨[⟨.or, [ua, ub]⟩], rfl⟩, Sum.inr (11 + st.1.length), rfl, (by intro u hu; cases hu; simp), ?_⟩
                  · intro h hh
                    simp only [List.mem_append, List.mem_singleton] at hh
                    rcases hh with hh | rfl
                    · exact hfan h hh
                    · exact ⟨by simp, by simp⟩
                  · intro x hx
                    simp only [evalVal, Sum.elim_inr]
                    rw [wires_snoc]
                    have hwl : ((Circuit.mk st.1 0).wires (pre x)).length = 11 + st.1.length := by
                      rw [wires_len]; simp [pre]
                    rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self]
                    simp only [List.map_cons, List.map_nil, heval x hx a, heval x hx b, ha, hb, evalVal, Sum.elim_inr, List.getD_cons_zero]
            · simp at hilen
          · rcases ins with _ | ⟨a, rest⟩
            · have hst : step st ⟨.not, []⟩ = (st.1, st.2 ++ [Sum.inl true]) := rfl
              rw [hst]
              refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl true, rfl, (by intro u h; cases h), ?_⟩
              intro x _; rfl
            · cases ha : st.2.getD a (Sum.inl false) with
              | inl ca =>
                have hst : step st ⟨.not, a :: rest⟩ = (st.1, st.2 ++ [Sum.inl (!ca)]) := by
                  simp only [step, List.map_cons, ha]
                rw [hst]
                refine ⟨hfan, by simp, by simp, ⟨[], by simp⟩, Sum.inl (!ca), rfl, (by intro u h; cases h), ?_⟩
                intro x hx
                simp only [List.map_cons, heval x hx a, ha, evalVal, Sum.elim_inl, id_eq]
                rfl
              | inr ua =>
                have hst : step st ⟨.not, a :: rest⟩ = (st.1 ++ [⟨.not, [ua]⟩], st.2 ++ [Sum.inr (11 + st.1.length)]) := by
                  simp only [step, List.map_cons, ha]
                rw [hst]
                refine ⟨?_, by simp, by simp, ⟨[⟨.not, [ua]⟩], rfl⟩, Sum.inr (11 + st.1.length), rfl, (by intro u hu; cases hu; simp), ?_⟩
                · intro h hh
                  simp only [List.mem_append, List.mem_singleton] at hh
                  rcases hh with hh | rfl
                  · exact hfan h hh
                  · exact ⟨by simp, by simp⟩
                · intro x hx
                  simp only [evalVal, Sum.elim_inr]
                  rw [wires_snoc]
                  have hwl : ((Circuit.mk st.1 0).wires (pre x)).length = 11 + st.1.length := by
                    rw [wires_len]; simp [pre]
                  rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self]
                  simp only [List.map_cons, List.map_nil, heval x hx a, ha, evalVal, Sum.elim_inr, List.getD_cons_zero]
                  rfl
        obtain ⟨hfan', hlen', hsz', ⟨tail, htail⟩, ⟨outv, houtv, houtbd, houtev⟩⟩ := hstep_core
        refine ⟨hfan', ?_, ?_, ?_, ?_, ?_⟩
        · rw [hlen', hlen]; simp; omega
        · rw [List.filter_append, List.length_append, List.length_append, List.length_singleton]
          by_cases hk : (reads g).any killed = true
          · rw [hkill_any hk]
            simp only [List.filter_cons, hk, ↓reduceIte, List.filter_nil, List.length_singleton]
            omega
          · simp [hk]
            omega
        · intro i hi hki
          rw [houtv, List.getD_append _ _ _ _ (by omega)]
          exact hkill i hi hki
        · intro i u hu
          rw [houtv] at hu
          by_cases hi : i < st.2.length
          · rw [List.getD_append _ _ _ _ hi] at hu
            have h1 := hbd i u hu
            have h2 : st.1.length ≤ (step st g).1.length := by rw [htail]; simp
            omega
          · by_cases heq : i = st.2.length
            · subst heq
              rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at hu
              exact houtbd u (by simpa using hu)
            · rw [List.getD_eq_default _ _ (by simp; omega)] at hu
              cases hu
        · intro x hx i
          rw [wires_snoc, houtv]
          have hwl : ((Circuit.mk pref 0).wires (pre x)).length = st.2.length := by
            rw [wires_len, hlen]; simp [pre]
          by_cases hi : i < st.2.length
          · rw [List.getD_append _ _ _ _ (hwl ▸ hi), List.getD_append _ _ _ _ hi, heval x hx i]
            cases hcur : st.2.getD i (Sum.inl false) with
            | inl c => rfl
            | inr u =>
              simp only [evalVal, htail]
              have h1 : (Circuit.mk (st.1 ++ tail) 0).wires (pre x) =
                  (Circuit.mk tail 0).wires ((Circuit.mk st.1 0).wires (pre x)) :=
                List.foldl_append
              rw [h1]
              symm
              apply wires_keep
              rw [wires_len]
              have hu := hbd i u hcur
              simp [pre]
              omega
          · by_cases heq : i = st.2.length
            · subst heq
              rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self,
                  List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
              simpa using houtev x hx
            · rw [List.getD_eq_default _ _ (by simp [hwl]; omega),
                  List.getD_eq_default _ _ (by simp; omega)]
              rfl
    obtain ⟨hfan, _, hsz, _, _, heval⟩ := inv E.gates hE
    set st := E.gates.foldl step ([], initEnv)
    cases hout : st.2.getD E.output (Sum.inl false) with
    | inl b =>
      exfalso
      have hconst : ∀ x : Fin 10 → Bool, x v = false → edge x = b := by
        intro x hx
        rw [← hcomp x]
        have h1 := heval x hx E.output
        rw [hout] at h1
        exact h1
      have h0 : edge (fun _ => false) = b := hconst (fun _ => false) rfl
      have hex : ∃ x : Fin 10 → Bool, x v = false ∧ edge x = true := by
        let e1 : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
        let e2 : Fin 10 → Bool := fun j => decide (j = 2 ∨ j = 3)
        let e3 : Fin 10 → Bool := fun j => decide (j = 5 ∨ j = 7)
        by_cases h1 : e1 v = false
        · exact ⟨e1, h1, by decide⟩
        · by_cases h2 : e2 v = false
          · exact ⟨e2, h2, by decide⟩
          · refine ⟨e3, ?_, by decide⟩
            have h : ∀ u : Fin 10, e1 u = true → e2 u = true → e3 u = false := by decide
            exact h v (Bool.eq_true_of_not_eq_false h1) (Bool.eq_true_of_not_eq_false h2)
      obtain ⟨x1, hx1, he1⟩ := hex
      have hfalse : edge (fun _ => false) = false := by decide
      have htrue := hconst x1 hx1
      rw [hfalse] at h0
      rw [he1] at htrue
      rw [← h0] at htrue
      cases htrue
    | inr out' =>
      refine ⟨⟨st.1, out'⟩, hfan, ?_, ?_⟩
      · change st.1.length + 4 ≤ E.gates.length
        omega
      · intro x hx
        have h1 := heval x hx E.output
        rw [hout] at h1
        exact h1.symm
  have drop_extra :
      ∀ (E : Circuit), FanInTwo E → (∀ x : Fin 10 → Bool, E.eval (pre x) = edge x) →
        (∀ g ∈ E.gates, 10 ∉ reads g) →
        ∃ E0 : Circuit, FanInTwo E0 ∧ E0.size = E.size ∧
          (∀ x : Fin 10 → Bool, E0.eval (List.ofFn x) = E.eval (pre x)) ∧
          (∀ v : Fin 10,
            (E0.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length =
            (E.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length) := by
    intro E hE hcomp hno10
    have hout10 : E.output ≠ 10 := by
      intro ho
      let x0 : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
      have h1 : E.eval (pre x0) = (pre x0).getD 10 false := by
        change ((Circuit.mk E.gates 0).wires (pre x0)).getD E.output false = _
        rw [ho]
        exact wires_keep E.gates (pre x0) 10 (by simp [pre])
      rw [hcomp x0] at h1
      have hbad : edge x0 ≠ (pre x0).getD 10 false := by decide
      exact hbad h1
    let sd (i : ℕ) : ℕ := if i < 10 then i else i - 1
    let mg (g : Gate) : Gate := ⟨g.op, (reads g).map sd⟩
    let E0 : Circuit := ⟨E.gates.map mg, sd E.output⟩
    have hfan0 : FanInTwo E0 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hlen⟩ := hE g' hg'
      refine ⟨hop, ?_⟩
      simp only [mg, List.length_map, reads]
      cases g'.op <;> simp [List.length_take] <;> omega
    have hrun : ∀ (gs : List Gate) (u w : List Bool),
        u.length = w.length + 1 → 10 ≤ w.length →
        (∀ g ∈ gs, 10 ∉ reads g) →
        (∀ i, i ≠ 10 → w.getD (sd i) false = u.getD i false) →
        ∀ i, i ≠ 10 →
          ((Circuit.mk (gs.map mg) 0).wires w).getD (sd i) false =
            ((Circuit.mk gs 0).wires u).getD i false := by
      intro gs
      induction gs with
      | nil => intro u w _ _ _ agree i hi; exact agree i hi
      | cons g rest ih =>
        intro u w hlen h10 hno agree
        have hg10 : 10 ∉ reads g := hno g (List.mem_cons_self)
        have hstep : (mg g).op.eval ((mg g).inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => u.getD i false) := by
          have hmap : (reads g).map (fun i => w.getD (sd i) false) =
              (reads g).map (fun i => u.getD i false) := by
            apply List.map_congr_left
            intro i hi
            exact agree i (fun h => hg10 (h ▸ hi))
          simp only [mg, List.map_map, Function.comp_def, hmap]
          rcases g with ⟨op, ins⟩
          cases op
          · rfl
          · rfl
          · rcases ins with _ | ⟨a, _⟩ <;> rfl
          · rfl
          · rfl
        change ∀ i, i ≠ 10 →
          ((Circuit.mk (rest.map mg) 0).wires (w ++ [_])).getD (sd i) false =
            ((Circuit.mk rest 0).wires (u ++ [_])).getD i false
        rw [hstep]
        apply ih _ _ (by simp [hlen]) (by simp; omega) (fun h hh => hno h (List.mem_cons_of_mem _ hh))
        intro i hi
        by_cases hiu : i < u.length
        · have hiw : sd i < w.length := by simp only [sd]; split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hiw, List.getD_append _ _ _ _ hiu]
          exact agree i hi
        · have h1 : sd i = w.length + (i - u.length) := by simp only [sd]; split_ifs <;> omega
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          have h2 : sd i - w.length = i - u.length := by omega
          rw [h2]
    have hev0 : ∀ x : Fin 10 → Bool, E0.eval (List.ofFn x) = E.eval (pre x) := by
      intro x
      apply hrun E.gates (pre x) (List.ofFn x) (by simp [pre]) (by simp) hno10 _ E.output hout10
      intro i hi
      by_cases h10 : i < 10
      · simp only [sd, h10, ↓reduceIte]
        rw [List.getD_append _ _ _ _ (by simp; omega)]
      · have hgt : 10 < i := by omega
        rw [List.getD_eq_default _ _ (by simp [sd, h10]; omega),
            List.getD_eq_default _ _ (by simp [pre]; omega)]
    have hfilt : ∀ v : Fin 10,
        (E0.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length =
        (E.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length := by
      intro v
      have hgo : ∀ gs : List Gate, (∀ g ∈ gs, 10 ∉ reads g) →
          ((gs.map mg).filter fun g => (reads g).any fun i => decide (i = v.val)).length =
          (gs.filter fun g => (reads g).any fun i => decide (i = v.val)).length := by
        intro gs
        induction gs with
        | nil => intro _; rfl
        | cons g rest ih =>
          intro hno
          have hg10 : 10 ∉ reads g := hno g List.mem_cons_self
          have hrm : reads (mg g) = (reads g).map sd := by
            rcases g with ⟨op, ins⟩
            cases op <;> simp [mg, reads]
          have hany : ((reads (mg g)).any fun i => decide (i = v.val)) =
              ((reads g).any fun i => decide (i = v.val)) := by
            rw [hrm, List.any_map]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, Function.comp_apply, decide_eq_true_eq]
            constructor
            · rintro ⟨i, hi, heq⟩
              refine ⟨i, hi, ?_⟩
              have hi10 : i ≠ 10 := fun h => hg10 (h ▸ hi)
              simp only [sd] at heq
              split_ifs at heq with hlt
              · exact heq
              · omega
            · rintro ⟨i, hi, rfl⟩
              refine ⟨v.val, hi, ?_⟩
              simp [sd, v.isLt]
          simp only [List.map_cons, List.filter_cons, hany]
          split_ifs <;> simp [ih (fun h hh => hno h (List.mem_cons_of_mem _ hh))]
      exact hgo E.gates hno10
    exact ⟨E0, hfan0, List.length_map mg, hev0, hfilt⟩
  have lift_extra :
      ∀ (D0 : Circuit), FanInTwo D0 →
        ∃ D : Circuit, FanInTwo D ∧ D.size = D0.size ∧
          ∀ x : Fin 10 → Bool, D.eval (pre x) = D0.eval (List.ofFn x) := by
    intro D0 hD0
    let su (i : ℕ) : ℕ := if i < 10 then i else i + 1
    let mg (g : Gate) : Gate := ⟨g.op, g.inputs.map su⟩
    let D : Circuit := ⟨D0.gates.map mg, su D0.output⟩
    refine ⟨D, ?_, List.length_map mg, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hD0 g' hg').1, by simpa [mg] using (hD0 g' hg').2⟩
    have run : ∀ (gs : List Gate) (u w : List Bool),
        w.length = u.length + 1 → 10 ≤ u.length →
        (∀ i, w.getD (su i) false = u.getD i false) →
        ∀ i, ((Circuit.mk (gs.map mg) 0).wires w).getD (su i) false =
          ((Circuit.mk gs 0).wires u).getD i false := by
      intro gs
      induction gs with
      | nil => intro u w _ _ agree i; exact agree i
      | cons g rest ih =>
        intro u w hlen h10 agree
        have hstep : (mg g).op.eval ((mg g).inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => u.getD i false) := by
          simp only [mg, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mg) 0).wires (w ++ [_])).getD (su i) false =
          ((Circuit.mk rest 0).wires (u ++ [_])).getD i false
        rw [hstep]
        apply ih _ _ (by simp [hlen]) (by simp; omega)
        intro i
        by_cases hiu : i < u.length
        · have hiw : su i < w.length := by simp only [su]; split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hiw, List.getD_append _ _ _ _ hiu]
          exact agree i
        · have h1 : su i = w.length + (i - u.length) := by simp only [su]; split_ifs <;> omega
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          have h2 : su i - w.length = i - u.length := by omega
          rw [h2]
    intro x
    apply run D0.gates (List.ofFn x) (pre x) (by simp [pre]) (by simp) _ D0.output
    intro i
    by_cases h10 : i < 10
    · simp only [su, h10, ↓reduceIte]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
    · rw [List.getD_eq_default _ _ (by simp [pre, su, h10]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  dsimp only
  intro C p hC hsize hcomp
  have hbij : Function.Bijective p := bij_of_computes C p hcomp
  let eqp := Equiv.ofBijective p hbij
  obtain ⟨E, hE, hEsize, hEeval⟩ := rewire_perm C p hC
  have hEcomp : ∀ x : Fin 10 → Bool, E.eval (pre x) = edge x := fun x =>
    (hEeval x).trans (hcomp x)
  have hEbd : E.size ≤ 18 := hEsize.le.trans hsize
  have hgoal : ∃ (v : Fin 10) (D : Circuit), FanInTwo D ∧ D.size + 4 ≤ E.size ∧
      ∀ x : Fin 10 → Bool, x v = false → D.eval (pre x) = E.eval (pre x) := by
    by_cases hhi : ∃ v : Fin 10,
        4 ≤ (E.gates.filter fun g => (reads g).any fun i =>
          decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))).length
    · obtain ⟨v, hv⟩ := hhi
      obtain ⟨D, hD, hDsz, hDev⟩ := elim_high E v hE hEcomp hv
      exact ⟨v, D, hD, hDsz, hDev⟩
    · have hlo : ∀ v : Fin 10,
          (E.gates.filter fun g => (reads g).any fun i =>
            decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))).length ≤ 3 := by
        intro v
        have hnot : ¬ 4 ≤ (E.gates.filter fun g => (reads g).any fun i =>
            decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))).length := fun h => hhi ⟨v, h⟩
        omega
      by_cases h10 : ∃ g ∈ E.gates, 10 ∈ reads g
      · exact usesExtra E hE hEbd hEcomp h10 hlo
      · have hno10 : ∀ g ∈ E.gates, 10 ∉ reads g := fun g hg h => h10 ⟨g, hg, h⟩
        obtain ⟨E0, hE0, hE0sz, hE0ev, hE0f⟩ := drop_extra E hE hEcomp hno10
        have hE0lo : ∀ v : Fin 10,
            (E0.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length ≤ 3 := by
          intro v
          rw [hE0f v]
          have hsub : (E.gates.filter fun g => (reads g).any fun i => decide (i = v.val)).length ≤
              (E.gates.filter fun g => (reads g).any fun i =>
                decide (i = v.val ∨ ((v = 0 ∨ v = 2) ∧ i = 10))).length := by
            have hgo : ∀ (gs : List Gate) (p1 p2 : Gate → Bool),
                (∀ g, p1 g = true → p2 g = true) →
                (gs.filter p1).length ≤ (gs.filter p2).length := by
              intro gs p1 p2 himp
              induction gs with
              | nil => exact le_refl 0
              | cons g rest ih =>
                simp only [List.filter_cons]
                cases h1 : p1 g
                · cases p2 g <;> simp <;> omega
                · rw [himp g h1]; simp; omega
            apply hgo
            intro g hg
            obtain ⟨i, hi, heq⟩ := List.any_eq_true.mp hg
            exact List.any_eq_true.mpr ⟨i, hi, decide_eq_true (Or.inl (of_decide_eq_true heq))⟩
          exact hsub.trans (hlo v)
        obtain ⟨v, D0, hD0, hD0sz, hD0ev⟩ :=
          pureCircuit E0 hE0 (hE0sz.le.trans hEbd) (fun x => (hE0ev x).trans (hEcomp x)) hE0lo
        obtain ⟨D, hD, hDsz, hDev⟩ := lift_extra D0 hD0
        refine ⟨v, D, hD, by omega, fun x hx => ?_⟩
        rw [hDev x, hD0ev x hx, hE0ev x]
  obtain ⟨v, D, hD, hDsz, hDev⟩ := hgoal
  obtain ⟨D', hD', hD'sz, hD'ev⟩ := rewire_inv D p eqp.symm (fun i => eqp.apply_symm_apply i) hD
  refine ⟨v, D', hD', by omega, fun x hx => ?_⟩
  rw [hD'ev x, hDev x hx, hEeval x]
