import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_7891_586
    (rawObstruction : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 C → C.size ≤ 18 →
      let f := fun r : ℕ => PEqualNP.MetaComplexity.circuitFun 10 C (fun i => r.testBit i.val)
      (∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), f r = true) →
      ∃ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), f r = true)
    (guardedError : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
      PEqualNP.TopForm.IsAO2 10 C → 16 ≤ C.size ∧ C.size ≤ 18 →
      (w ≠ 0 ∧ w < 10 + C.size ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        10 + j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      let x := fun (r : ℕ) (i : Fin 10) => r.testBit i.val
      let f := fun r => PEqualNP.MetaComplexity.circuitFun 10 C (x r)
      let xoff := fun r => Function.update (x r) (0 : Fin 10) false
      let d := fun r => (C.wires (List.ofFn (xoff r))).getD w false
      let N : List ℕ := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
      let M : List ℕ := [69,201,385,521,773]
      (∀ r ∈ ([2,16,32] : List ℕ), d r = true) →
      (∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), f r = true) →
      (∀ r ∈ N, PEqualNP.MetaComplexity.circuitFun 10 C (xoff r) = false) →
      (∃ r ∈ M, f r = true) →
      ∃ r ∈ M, f r = true ∧ d r = true) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) && x7 x8));         (∀ x9 ∈ [(2 : ℕ), (16 : ℕ), (32 : ℕ)], x7 x9 = Bool.true) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false)) := by
  classical
  intro C w shape size schedule
  dsimp only
  intro neighbors accepted
  let P : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320,528,576,640]
  let N : List ℕ := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
  let M : List ℕ := [69,201,385,521,773]
  let x (r : ℕ) (i : Fin 10) : Bool := r.testBit i.val
  let xo (r : ℕ) := Function.update (x r) (0 : Fin 10) false
  let d (r : ℕ) := (C.wires (List.ofFn (xo r))).getD w false
  let f := PEqualNP.MetaComplexity.circuitFun 10 C
  let change0 (r : ℕ) := Function.update (x r) (0 : Fin 10) (x r 0 && d r)
  change ∀ r ∈ ([2,16,32] : List ℕ), d r = true at neighbors
  change (∀ r ∈ P, f (change0 r) = true) ∧ (∀ r ∈ N, f (change0 r) = false) at accepted
  have keep {r : ℕ} (h : (x r 0 && d r) = x r 0) : change0 r = x r :=
    Function.update_eq_self_iff.mpr h
  have positiveCases : ∀ r ∈ P, x r 0 = false ∨
      ∃ j ∈ ([2,16,32] : List ℕ), xo r = xo j := by
    intro r hr
    simp only [P,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨2, by decide, by decide⟩
    | exact Or.inr ⟨16, by decide, by decide⟩
    | exact Or.inr ⟨32, by decide, by decide⟩
  have rawPos : ∀ r ∈ P, f (x r) = true := by
    intro r hr
    have eq : change0 r = x r := by
      rcases positiveCases r hr with off | ⟨j,hj,eq⟩
      · exact keep (by rw [off]; rfl)
      · have on : d r = true := by
          change (C.wires (List.ofFn (xo r))).getD w false = true
          rw [eq]
          exact neighbors j hj
        exact keep (by rw [on,Bool.and_true])
    exact eq ▸ accepted.1 r hr
  let R := fun (a b : List Bool) => a.length = b.length ∧
    ∀ i, a.getD i false = true → b.getD i false = true
  let push := fun (a : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]
  have stepMono (g : PEqualNP.CircuitLowerBounds.Gate)
      (op : g.op = .and ∨ g.op = .or) (a b : List Bool)
      (rel : R a b) : R (push a g) (push b g) := by
    obtain ⟨len, yes⟩ := rel
    have gateYes : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
      rcases op with op | op
      · rw [op]
        change (g.inputs.map fun i => a.getD i false).all id = true →
          (g.inputs.map fun i => b.getD i false).all id = true
        simp only [List.all_map,Function.comp_apply,id_eq,List.all_eq_true]
        intro h i hi
        exact yes _ (h i hi)
      · rw [op]
        change (g.inputs.map fun i => a.getD i false).any id = true →
          (g.inputs.map fun i => b.getD i false).any id = true
        simp only [List.any_map,Function.comp_apply,id_eq,List.any_eq_true]
        rintro ⟨i,hi,h⟩
        exact ⟨i,hi,yes _ h⟩
    refine ⟨by simp [push,len], fun i ha => ?_⟩
    unfold push at ha ⊢
    rcases lt_trichotomy i a.length with low | atEnd | high
    · rw [List.getD_append _ _ _ _ low] at ha
      rw [List.getD_append _ _ _ _ (len ▸ low)]
      exact yes _ ha
    · subst i
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at ha
      rw [len,List.getD_append_right _ _ _ _ (le_refl _)]
      simp at ha ⊢
      exact gateYes ha
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ha
      simp at ha
  have foldMono (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (op : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ a b, R a b → R (gs.foldl push a) (gs.foldl push b) := by
    induction gs with
    | nil => intro a b h; exact h
    | cons g gs ih =>
      intro a b rel
      simp only [List.foldl_cons]
      exact ih (fun g' hg' => op g' (List.mem_cons_of_mem _ hg')) _ _
        (stepMono g (op g (by simp)) a b rel)
  have mon (a b : Fin 10 → Bool) (ab : ∀ i, a i ≤ b i) (yes : f a = true) : f b = true := by
    have inputs : R (List.ofFn a) (List.ofFn b) := by
      refine ⟨by simp, fun i h => ?_⟩
      by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa),List.getElem_ofFn] at h ⊢
        have le := ab ⟨i,hi⟩
        rw [h] at le
        cases hb : b ⟨i,hi⟩
        · rw [hb] at le
          exact False.elim ((show ¬ true ≤ false by decide) le)
        · rfl
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)] at h
        contradiction
    exact (foldMono C.gates shape.1 _ _ inputs).2 C.output yes
  have clearedNeg : ∀ r ∈ N, f (xo r) = false := by
    intro r hr
    cases h : f (xo r)
    · rfl
    · have below (i : Fin 10) : xo r i ≤ change0 r i := by
        by_cases hi : i = 0
        · subst i
          exact Bool.false_le _
        · simp only [xo,change0,Function.update_of_ne hi,le_refl]
      exact False.elim (Bool.false_ne_true ((accepted.2 r hr).symm.trans (mon _ _ below h)))
  have splitNeg : ∀ r ∈ N, x r 0 = false ∨ r ∈ M := by
    intro r hr
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have inNeg : ∀ r ∈ M, r ∈ N := by
    intro r hr
    simp only [M,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have oddError : ∃ r ∈ M, f (x r) = true := by
    obtain ⟨r,hr,yes⟩ := rawObstruction C shape size.2 rawPos
    rcases splitNeg r hr with off | h
    · have eq : xo r = x r := Function.update_eq_self_iff.mpr off.symm
      exact False.elim (Bool.false_ne_true ((clearedNeg r hr).symm.trans (eq.symm ▸ yes)))
    · exact ⟨r,h,yes⟩
  obtain ⟨r,hr,yes,on⟩ := guardedError C w shape size schedule neighbors rawPos clearedNeg oddError
  change d r = true at on
  change f (x r) = true at yes
  have eq : change0 r = x r := keep (by rw [on,Bool.and_true])
  exact Bool.false_ne_true ((accepted.2 r (inNeg r hr)).symm.trans (eq.symm ▸ yes))
