import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5198_3
    (hZero : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (0 : ℕ) → (64 : ℕ) ≤ x3.size)
    (hOne : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size)
    (hClean : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x5 x6 ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → (x3.wires (x1 x7)).getD ((26 : ℕ) + x5) Bool.false = Bool.false) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ (x6.size < x3.size ∨ x6.size = x3.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x6 < PEqualNP.TopForm.andPairs (26 : ℕ) x3))
    (hMany : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x6.size = x3.size → PEqualNP.TopForm.andPairs (26 : ℕ) x3 ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x6) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ (x8 x9 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x8 x9 → ∃ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 ∧ (x3.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (64 : ℕ) ≤ x3.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  classical
  intro S X W G A nest C a b hM hRB ha hb hpos hquad _ _ _
  let qrow : Finset (Fin 13) → List Bool := fun Q =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)
  let Valid : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun E =>
    PEqualNP.MetaComplexity.Monotone2 E ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 E ∧
    (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
      E.eval ((List.ofFn fun q : Fin 13 => decide (q = p)) ++
        List.ofFn fun q : Fin 13 => decide (q = l)) = true) ∧
    (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
      E.eval (qrow Q) = false)
  let g0 : PEqualNP.CircuitLowerBounds.Gate :=
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates ++ [g0], output := 26 + C.size }
  have hC'sz : C'.size = C.size + 1 := by
    change (C.gates ++ [g0]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  have hgen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) M).length =
        M.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro M
      simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs' ih =>
      intro M
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hwlen : ∀ L : List Bool, (C.wires L).length = L.length + C.size := by
    intro L
    change (C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L).length =
      L.length + C.gates.length
    exact hgen C.gates L
  have hor2 : ∀ (u v : Bool),
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or [u, v] = (u || v) := by
    intro u v
    cases u <;> cases v <;> rfl
  have hw : ∀ L : List Bool, C'.wires L =
      C.wires L ++ [(C.wires L).getD a false || (C.wires L).getD b false] := by
    intro L
    have h1 : C'.wires L = (C.gates ++ [g0]).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L := rfl
    have h2 : C.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L = C.wires L := rfl
    rw [h1, List.foldl_append, h2, List.foldl_cons, List.foldl_nil]
    change C.wires L ++ [PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or
      [(C.wires L).getD a false, (C.wires L).getD b false]] = _
    rw [hor2]
  have hev : ∀ L : List Bool, L.length = 26 →
      C'.eval L = ((C.wires L).getD a false || (C.wires L).getD b false) := by
    intro L hL26
    have he : C'.eval L = (C'.wires L).getD (26 + C.size) false := rfl
    have hidx : 26 + C.size = (C.wires L).length := by
      rw [hwlen L, hL26]
    rw [he, hw L, hidx, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have hM' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    obtain h1 | h2 := List.mem_append.mp hg
    · exact hM g h1
    · have hgeq : g = g0 := List.mem_singleton.mp h2
      rw [hgeq]
      refine ⟨Or.inr rfl, ?_⟩
      change ([a, b] : List ℕ).length ≤ 2
      exact Nat.le_refl 2
  have hRB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' := by
    intro j hj
    have hj' : j < C.size + 1 := by
      rw [← hC'sz]
      exact hj
    by_cases hlt : j < C.size
    · have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        change (C.gates ++ [g0]).getD j _ = C.gates.getD j _
        exact List.getD_append _ _ _ _ hlt
      intro i hi
      rw [hgt] at hi
      exact hRB j hlt i hi
    · have hjEq : j = C.size := by omega
      rw [hjEq]
      intro i hi
      have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' C.size = g0 := by
        change (C.gates ++ [g0]).getD C.gates.length _ = g0
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hgt] at hi
      have hi' : i ∈ ([a, b] : List ℕ) := hi
      obtain rfl | hi2 := List.mem_cons.mp hi'
      · exact ha
      · have hbi : i = b := List.mem_singleton.mp hi2
        rw [hbi]
        exact hb
  have hpos' : ∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
      C'.eval ((List.ofFn fun q : Fin 13 => decide (q = p)) ++
        List.ofFn fun q : Fin 13 => decide (q = l)) = true := by
    intro p l hpl
    have hL : (List.ofFn fun q : Fin 13 => decide (q = p)) ++
        (List.ofFn fun q : Fin 13 => decide (q = l)) = X {p} {l} := by
      have h1 : (List.ofFn fun q : Fin 13 => decide (q = p)) =
          (List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) := by
        apply congrArg List.ofFn
        funext q
        exact decide_eq_decide.mpr Finset.mem_singleton.symm
      have h2 : (List.ofFn fun q : Fin 13 => decide (q = l)) =
          (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13)))) := by
        apply congrArg List.ofFn
        funext q
        exact decide_eq_decide.mpr Finset.mem_singleton.symm
      change _ = (List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
        (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13))))
      rw [h1, h2]
    have hlen26 : (X {p} {l}).length = 26 := by
      change ((List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
        (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13))))).length = 26
      rw [List.length_append, List.length_ofFn, List.length_ofFn]
    rw [hL, hev _ hlen26]
    obtain ha1 | hb1 := hpos p l hpl
    · change (C.wires (X {p} {l})).getD a false = true at ha1
      rw [ha1, Bool.true_or]
    · change (C.wires (X {p} {l})).getD b false = true at hb1
      rw [hb1, Bool.or_true]
  have hquad' : ∀ Q : Finset (Fin 13),
      PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
      C'.eval (qrow Q) = false := by
    intro Q hQ
    have hlen26 : (qrow Q).length = 26 := by
      change ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))).length = 26
      rw [List.length_append, List.length_ofFn, List.length_ofFn]
    rw [hev _ hlen26]
    obtain ⟨ha0, hb0⟩ := hquad Q hQ
    change (C.wires (qrow Q)).getD a false = false at ha0
    change (C.wires (qrow Q)).getD b false = false at hb0
    rw [ha0, hb0]
    rfl
  have hValidC' : Valid C' := ⟨hM', hRB', hpos', hquad'⟩
  have hexSize : ∃ n : ℕ, ∃ E : PEqualNP.CircuitLowerBounds.Circuit, Valid E ∧ E.size = n :=
    ⟨C'.size, C', hValidC', rfl⟩
  let m : ℕ := Nat.find hexSize
  have hmLe : m ≤ C'.size := Nat.find_min' hexSize ⟨C', hValidC', rfl⟩
  have hexPairs : ∃ k : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      Valid D ∧ D.size = m ∧ PEqualNP.TopForm.andPairs 26 D = k := by
    obtain ⟨E, hVE, hEm⟩ := Nat.find_spec hexSize
    exact ⟨PEqualNP.TopForm.andPairs 26 E, E, hVE, hEm, rfl⟩
  obtain ⟨D, hVD, hDm, hDk⟩ := Nat.find_spec hexPairs
  have hMinSize : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, Valid E → D.size ≤ E.size := by
    intro E hVE
    rw [hDm]
    exact Nat.find_min' hexSize ⟨E, hVE, rfl⟩
  have hMinPairs : ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
      Valid E → E.size = D.size →
      PEqualNP.TopForm.andPairs 26 D ≤ PEqualNP.TopForm.andPairs 26 E := by
    intro E hVE hEq
    rw [hDk]
    exact Nat.find_min' hexPairs ⟨E, hVE, hEq.trans hDm, rfl⟩
  have h64D : 64 ≤ D.size := by
    by_cases hk0 : PEqualNP.TopForm.andPairs 26 D = 0
    · exact hZero D hVD hk0
    · by_cases hk1 : PEqualNP.TopForm.andPairs 26 D = 1
      · exact hOne D hVD hMinSize hk1
      · have hk2 : 2 ≤ PEqualNP.TopForm.andPairs 26 D := by omega
        have hDirty : ∀ (i j : ℕ),
            (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.InCone 26 D i j →
            ∃ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q ∧
              (D.wires (qrow Q)).getD (26 + i) false = true := by
          intro i j hi hj hcone
          by_contra hno
          have hallFalse : ∀ Q : Finset (Fin 13),
              PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
              (D.wires (qrow Q)).getD (26 + i) false = false := by
            intro Q hQ
            by_cases hval : (D.wires (qrow Q)).getD (26 + i) false = true
            · exact False.elim (hno ⟨Q, hQ, hval⟩)
            · exact Bool.eq_false_iff.mpr hval
          obtain ⟨E, hVE, hbetter⟩ := hClean D hVD ⟨i, j, hi, hj, hcone, hallFalse⟩
          have hle := hMinSize E hVE
          obtain hlt | hEqLt := hbetter
          · omega
          · obtain ⟨heq, hplt⟩ := hEqLt
            have hple := hMinPairs E hVE heq
            omega
        exact hMany D hVD hMinSize hMinPairs hk2 hDirty
  omega
