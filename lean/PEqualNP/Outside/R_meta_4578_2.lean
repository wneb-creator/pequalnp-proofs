import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.TopForm

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4578_2
    (normalize : ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C →
      ∃ D : Circuit, IsAO2 26 D ∧ ComputesIncidence singerLines3 D ∧ D.size ≤ C.size)
    (degOne : ∀ D : Circuit, IsAO2 26 D → ComputesIncidence singerLines3 D →
      (HasLineDegree 26 (Finset.range 13) D 1 ∨ HasLineDegree 26 (Finset.Ico 13 26) D 1) →
      64 ≤ D.size)
    (degTwo : ∀ D : Circuit, IsAO2 26 D → ComputesIncidence singerLines3 D →
      (∃ j < D.gates.length, (D.gates[j]?).map Gate.op = some .and ∧
        2 ≤ (D.lineDegrees 26 (Finset.range 13)).getD (26 + j) 0) →
      (∃ k < D.gates.length, (D.gates[k]?).map Gate.op = some .and ∧
        2 ≤ (D.lineDegrees 26 (Finset.Ico 13 26)).getD (26 + k) 0) →
      64 ≤ D.size) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => ∃ x5 ∈ x3, ∃ x6 ∈ x4, x1 x5 x6; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x4 {x6} {x7} = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x2 x4 x7 x8 = Bool.true → x3 x7 x8) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x4 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x4 (1 : ℕ) → (64 : ℕ) ≤ x4.size := by
  intro I value edge C mono hits sound _ _
  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ I p l := by decide +kernel
  have same (X Y : Finset (Fin 13)) : C.eval (incidenceInput X Y) = value C X Y := by
    let z : Fin 26 → Bool :=
      fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ X)) (fun l : Fin 13 => decide (l ∈ Y)) i
    have h : List.ofFn z = incidenceInput X Y := by
      change List.ofFn z = List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ Y))
      rw [List.ofFn_add (n := 13) (m := 13)]
      simp [z, Fin.addCases]
    change C.eval _ = C.eval (List.ofFn z)
    rw [h]
  have evMono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
      (h : ∀ i, U.getD i false = true → V.getD i false = true) :
      g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
    rcases hg with h1 | h1
    · rw [h1]
      change (g.inputs.map fun i => U.getD i false).all id = true →
        (g.inputs.map fun i => V.getD i false).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      intro hu x hmem
      obtain ⟨i, hi, hx⟩ := hmem
      subst hx
      exact h i (hu _ ⟨i, hi, rfl⟩)
    · rw [h1]
      change (g.inputs.map fun i => U.getD i false).any id = true →
        (g.inputs.map fun i => V.getD i false).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      intro hmem
      obtain ⟨x, hx1, hx2⟩ := hmem
      obtain ⟨i, hi, rfl⟩ := hx1
      exact ⟨_, ⟨i, hi, rfl⟩, h i hx2⟩
  have foldMono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) U).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) V).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ U V _ h i; exact h i
    | cons g gs ih =>
      intro hgs U V hl h i
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [hl]
      · intro k hk
        rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ hlt] at hk
          rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
          exact h k hk
        · subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
          rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
          exact evMono g (hgs g (List.mem_cons_self ..)) U V h hk
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
          exact absurd hk (by simp)
  have hComp : ComputesIncidence singerLines3 C := by
    intro X Y
    by_cases hf : incidenceFun singerLines3 X Y = true
    · rw [hf]
      obtain ⟨p, hp, l, hl, hi⟩ := of_decide_eq_true hf
      have hPair : C.eval (incidenceInput {p} {l}) = true :=
        (same {p} {l}).trans (hits p l ((incidence p l).mp hi))
      have hOps : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
        simpa using (mono g hg).1
      have hLen : (incidenceInput {p} {l}).length = (incidenceInput X Y).length := by
        change (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13))))).length =
          (List.ofFn (fun a : Fin 13 => decide (a ∈ X)) ++
          List.ofFn (fun b : Fin 13 => decide (b ∈ Y))).length
        simp
      have hLe : ∀ i, (incidenceInput {p} {l}).getD i false = true →
          (incidenceInput X Y).getD i false = true := by
        intro i hi'
        by_cases h1 : i < 13
        · have hA : (incidenceInput {p} {l}).getD i false = decide (⟨i, h1⟩ ∈ ({p} : Finset (Fin 13))) := by
            change (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
              List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13))))).getD i false = _
            rw [List.getD_append _ _ _ _ (by simp [h1]), List.getD_eq_getElem?_getD,
              List.getElem?_ofFn, dite_eq_left h1]
            rfl
          have hB : (incidenceInput X Y).getD i false = decide (⟨i, h1⟩ ∈ X) := by
            change (List.ofFn (fun a : Fin 13 => decide (a ∈ X)) ++
              List.ofFn (fun b : Fin 13 => decide (b ∈ Y))).getD i false = _
            rw [List.getD_append _ _ _ _ (by simp [h1]), List.getD_eq_getElem?_getD,
              List.getElem?_ofFn, dite_eq_left h1]
            rfl
          rw [hA] at hi'
          rw [hB]
          have hEq : (⟨i, h1⟩ : Fin 13) = p := Finset.mem_singleton.mp (of_decide_eq_true hi')
          exact decide_eq_true (hEq ▸ hp)
        · by_cases h2 : i < 26
          · have h3 : i - 13 < 13 := by omega
            have hA : (incidenceInput {p} {l}).getD i false = decide (⟨i - 13, h3⟩ ∈ ({l} : Finset (Fin 13))) := by
              change (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
                List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13))))).getD i false = _
              rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
                List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h3]
              rfl
            have hB : (incidenceInput X Y).getD i false = decide (⟨i - 13, h3⟩ ∈ Y) := by
              change (List.ofFn (fun a : Fin 13 => decide (a ∈ X)) ++
                List.ofFn (fun b : Fin 13 => decide (b ∈ Y))).getD i false = _
              rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
                List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h3]
              rfl
            rw [hA] at hi'
            rw [hB]
            have hEq : (⟨i - 13, h3⟩ : Fin 13) = l := Finset.mem_singleton.mp (of_decide_eq_true hi')
            exact decide_eq_true (hEq ▸ hl)
          · have hDef : (incidenceInput {p} {l}).getD i false = false := by
              change (List.ofFn (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
                List.ofFn (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13))))).getD i false = false
              exact List.getD_eq_default _ _ (by simp; omega)
            rw [hDef] at hi'
            exact absurd hi' (by simp)
      exact foldMono C.gates hOps (incidenceInput {p} {l}) (incidenceInput X Y) hLen hLe C.output hPair
    · have hf0 : incidenceFun singerLines3 X Y = false := Bool.eq_false_iff.mpr hf
      rw [hf0]
      apply Bool.eq_false_iff.mpr
      intro hT
      obtain ⟨p, hp, l, hl, hi⟩ := sound X Y ((same X Y).symm.trans hT)
      exact hf (decide_eq_true ⟨p, hp, l, hl, (incidence p l).mpr hi⟩)
  obtain ⟨D, hAO2, hDComp, hSize⟩ := normalize C mono hComp
  have findAnd (M : Finset ℕ) (hHigh : ¬ HasLineDegree 26 M D 1) :
      ∃ j < D.gates.length, (D.gates[j]?).map Gate.op = some .and ∧
        2 ≤ (D.lineDegrees 26 M).getD (26 + j) 0 := by
    let init : List ℕ := (List.range 26).map fun i => if i ∈ M then 1 else 0
    let degs : List Gate → List ℕ := fun gs => gs.foldl (fun d g => d ++ [g.lineDegree d]) init
    have degsLen : ∀ gs : List Gate, (degs gs).length = 26 + gs.length := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => simp [degs, init]
      | append_singleton gs g ih =>
        have hStep : degs (gs ++ [g]) = degs gs ++ [g.lineDegree (degs gs)] := by
          simp [degs, List.foldl_append]
        rw [hStep, List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
        omega
    have degsPre : ∀ (gs hs : List Gate) (i : ℕ), i < (degs gs).length →
        (degs (gs ++ hs)).getD i 0 = (degs gs).getD i 0 := by
      intro gs hs
      induction hs using List.reverseRecOn with
      | nil => intro i _; simp
      | append_singleton hs g ih =>
        intro i hi
        have hStep : degs (gs ++ (hs ++ [g])) = degs (gs ++ hs) ++ [g.lineDegree (degs (gs ++ hs))] := by
          rw [← List.append_assoc]
          simp [degs, List.foldl_append]
        rw [hStep, List.getD_append _ _ _ _ (by rw [degsLen] at hi ⊢; simp; omega)]
        exact ih i hi
    have foldrMaxLe : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 1) → l.foldr max 0 ≤ 1 := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro h
        simp only [List.foldr_cons]
        have ha : a ≤ 1 := h a (List.mem_cons_self ..)
        have ht : t.foldr max 0 ≤ 1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
        omega
    by_contra hNone
    push Not at hNone
    have allLe : ∀ (gs : List Gate), (∃ hs, D.gates = gs ++ hs) → ∀ i, (degs gs).getD i 0 ≤ 1 := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _ i
        by_cases hi : i < 26
        · simp only [degs, List.foldl_nil, init, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range hi, Option.map_some, Option.getD_some]
          by_cases hM : i ∈ M
          · rw [ite_eq_left hM]
          · rw [ite_eq_right hM]; omega
        · rw [List.getD_eq_default _ _ (by simp [degs, init]; omega)]
          omega
      | append_singleton gs g ih =>
        rintro ⟨hs, hEq⟩ i
        have hStep : degs (gs ++ [g]) = degs gs ++ [g.lineDegree (degs gs)] := by
          simp [degs, List.foldl_append]
        have hPrev : ∀ k, (degs gs).getD k 0 ≤ 1 := ih ⟨g :: hs, by simpa [List.append_assoc] using hEq⟩
        rw [hStep]
        rcases Nat.lt_trichotomy i (degs gs).length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ hlt]
          exact hPrev i
        · subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          have hgMem : g ∈ D.gates := by rw [hEq]; simp
          rcases hAO2.1 g hgMem with hAnd | hOr
          · have hIdx : gs.length < D.gates.length := by rw [hEq]; simp
            have hGet : D.gates[gs.length]? = some g := by
              have hEq' : D.gates = gs ++ g :: hs := by simpa [List.append_assoc] using hEq
              rw [hEq', List.getElem?_append_right (le_refl _)]
              simp
            have hMap : (D.gates[gs.length]?).map Gate.op = some .and := by rw [hGet, Option.map_some, hAnd]
            have hLt : (D.lineDegrees 26 M).getD (26 + gs.length) 0 < 2 := hNone gs.length hIdx hMap
            have hAt : (D.lineDegrees 26 M).getD (26 + gs.length) 0 = g.lineDegree (degs gs) := by
              change (degs D.gates).getD (26 + gs.length) 0 = g.lineDegree (degs gs)
              have hLtLen : 26 + gs.length < (degs (gs ++ [g])).length := by
                rw [degsLen, List.length_append, List.length_singleton]
                omega
              rw [hEq, degsPre (gs ++ [g]) hs (26 + gs.length) hLtLen,
                hStep, List.getD_append_right _ _ _ _ (le_of_eq (degsLen gs)), degsLen gs, Nat.sub_self,
                List.getD_cons_zero]
            omega
          · rcases g with ⟨op, ins⟩
            dsimp only at hOr
            subst hOr
            change (ins.map fun i => (degs gs).getD i 0).foldr max 0 ≤ 1
            apply foldrMaxLe
            intro x hx
            obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
            exact hPrev w
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          omega
    have hOut : D.lineDeg 26 M ≤ 1 := by
      change (degs D.gates).getD D.output 0 ≤ 1
      exact allLe D.gates ⟨[], by simp⟩ D.output
    exact hHigh hOut
  have hD64 : 64 ≤ D.size := by
    by_cases h1 : HasLineDegree 26 (Finset.range 13) D 1 ∨ HasLineDegree 26 (Finset.Ico 13 26) D 1
    · exact degOne D hAO2 hDComp h1
    · push Not at h1
      exact degTwo D hAO2 hDComp (findAnd (Finset.range 13) h1.1) (findAnd (Finset.Ico 13 26) h1.2)
  omega
