import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1749_3
    (h1 :
      have D : Fin 13 → Bool := fun d => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9);
      have OK : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        (∀ p l : Fin 13, D (p - l) = true →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
        ∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, {p ∈ Q | D (p - l) = true}.card ≤ 2) →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun v : Fin 13 => decide (∀ r ∈ Q, D (r - v) = false)) = false;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        OK C →
        ¬ (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone 26 C i j) →
        64 ≤ C.size)
    (h2 :
      have D : Fin 13 → Bool := fun d => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9);
      have isQuad : Finset (Fin 13) → Prop := fun Q =>
        Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | D (p - l) = true}.card ≤ 2;
      have qIn : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun v : Fin 13 => decide (∀ r ∈ Q, D (r - v) = false);
      have OK : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        (∀ p l : Fin 13, D (p - l) = true →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
        ∀ Q : Finset (Fin 13), isQuad Q → C.eval (qIn Q) = false;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        OK C →
        (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone 26 C i j ∧
          ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (qIn Q)).getD (26 + i) false = false) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C' ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
          OK C' ∧
          (C'.size < C.size ∨ (C'.size = C.size ∧ PEqualNP.TopForm.andPairs 26 C' < PEqualNP.TopForm.andPairs 26 C)))
    (h3' :
      have D : Fin 13 → Bool := fun d => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9);
      have isQuad : Finset (Fin 13) → Prop := fun Q =>
        Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | D (p - l) = true}.card ≤ 2;
      have qIn : Finset (Fin 13) → List Bool := fun Q =>
        (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun v : Fin 13 => decide (∀ r ∈ Q, D (r - v) = false);
      have OK : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
        (∀ p l : Fin 13, D (p - l) = true →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
        ∀ Q : Finset (Fin 13), isQuad Q → C.eval (qIn Q) = false;
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        OK C →
        C.size < 64 →
        (∀ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.InCone 26 C i j →
          ∃ Q : Finset (Fin 13), isQuad Q ∧ (C.wires (qIn Q)).getD (26 + i) false = true) →
        64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size := by
  intro x1 x2 x3 C0 hM0 hR0 hOK0 hsz0 _
  let D : Fin 13 → Bool := fun d => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9)
  let isQuad : Finset (Fin 13) → Prop := fun Q =>
    Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | D (p - l) = true}.card ≤ 2
  let qIn : Finset (Fin 13) → List Bool := fun Q =>
    (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun v : Fin 13 => decide (∀ r ∈ Q, D (r - v) = false)
  let OK : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
    (∀ p l : Fin 13, D (p - l) = true →
      C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
    ∀ Q : Finset (Fin 13), isQuad Q → C.eval (qIn Q) = false
  have hD_iff : ∀ d : Fin 13, d ∈ x1 ↔ D d = true := by
    intro d
    change d ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9) = true
    simp
  have hD_not : ∀ d : Fin 13, d ∉ x1 ↔ D d = false := by
    intro d
    rw [hD_iff d]
    cases D d <;> simp
  have hfilt_eq : ∀ (Q : Finset (Fin 13)) (l : Fin 13),
      {p ∈ Q | p - l ∈ x1} = {p ∈ Q | D (p - l) = true} :=
    fun Q l => Finset.filter_congr fun p _ => hD_iff (p - l)
  have hqIn_eq : ∀ Q : Finset (Fin 13),
      ((List.ofFn fun u : Fin 13 => Decidable.decide (u ∈ Q)) ++
        List.ofFn fun v : Fin 13 => Decidable.decide (∀ r ∈ Q, r - v ∉ x1)) = qIn Q := by
    intro Q
    apply congrArg (List.append _)
    apply congrArg List.ofFn
    funext v
    exact decide_eq_decide.mpr (forall₂_congr fun r _ => hD_not (r - v))
  have toOK : ∀ C, x2 C → OK C := by
    intro C hC
    refine ⟨fun p l hpl => hC.1 p l ((hD_iff _).mpr hpl), fun Q hQ => ?_⟩
    rw [← hqIn_eq Q]
    exact hC.2 Q hQ.1 (fun l => by rw [hfilt_eq]; exact hQ.2 l)
  have ofOK : ∀ C, OK C → x2 C := by
    intro C hC
    refine ⟨fun p l hpl => hC.1 p l ((hD_iff _).mp hpl), fun Q hQ1 hQ2 => ?_⟩
    rw [hqIn_eq Q]
    exact hC.2 Q ⟨hQ1, fun l => by rw [← hfilt_eq]; exact hQ2 l⟩
  have h3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      OK C →
      C.size < 64 →
      (∀ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.EdgeOwnership.InCone 26 C i j →
        ∃ Q : Finset (Fin 13), isQuad Q ∧ (C.wires (qIn Q)).getD (26 + i) false = true) →
      (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C i j) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
        OK C' ∧ C'.size < C.size := by
    intro C hm hr hOK hsz hdirty _
    exact absurd (h3' C hm hr hOK hsz hdirty) (by omega)
  let s := C0.size
  have hs : s < 64 := hsz0
  have hind : ∀ k : ℕ, ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      OK C →
      C.size = s →
      PEqualNP.TopForm.andPairs 26 C = k →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
        OK C' ∧ C'.size < s := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C hM hR hOK hCsz hk
      by_cases hnest : x3 C
      · by_cases hsound : ∃ i j : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            PEqualNP.EdgeOwnership.InCone 26 C i j ∧
            ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (qIn Q)).getD (26 + i) false = false
        · obtain ⟨C1, hM1, hR1, hOK1, hdec⟩ := h2 C hM hR hOK hsound
          rcases hdec with hlt | ⟨heq, hap⟩
          · exact ⟨C1, hM1, hR1, hOK1, by omega⟩
          · exact ih (PEqualNP.TopForm.andPairs 26 C1) (by omega) C1 hM1 hR1 hOK1 (by omega) rfl
        · have hdirty : ∀ i j : ℕ,
              (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              PEqualNP.EdgeOwnership.InCone 26 C i j →
              ∃ Q : Finset (Fin 13), isQuad Q ∧ (C.wires (qIn Q)).getD (26 + i) false = true := by
            intro i j hi hj hcone
            by_contra hnone
            apply hsound
            refine ⟨i, j, hi, hj, hcone, ?_⟩
            intro Q hQ
            cases hval : (C.wires (qIn Q)).getD (26 + i) false
            · rfl
            · exact absurd ⟨Q, hQ, hval⟩ hnone
          obtain ⟨C1, hM1, hR1, hOK1, hlt⟩ := h3 C hM hR hOK (by omega) hdirty hnest
          exact ⟨C1, hM1, hR1, hOK1, by omega⟩
      · have hOK1 : (∀ p l : Fin 13, D (p - l) = true →
            C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
            ∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, {p ∈ Q | D (p - l) = true}.card ≤ 2) → C.eval (qIn Q) = false :=
          ⟨hOK.1, fun Q h1' h2' => hOK.2 Q ⟨h1', h2'⟩⟩
        have hge := h1 C hM hR hOK1 hnest
        omega
  obtain ⟨C', hM', hR', hOK', hlt'⟩ :=
    hind (PEqualNP.TopForm.andPairs 26 C0) C0 hM0 hR0 (toOK C0 hOK0) rfl rfl
  exact ⟨C', hM', hR', ofOK C' hOK', hlt'⟩
