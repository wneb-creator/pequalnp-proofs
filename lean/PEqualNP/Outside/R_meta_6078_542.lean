import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6078_542
    (shared :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let F := fun x : Fin 26 → Bool =>
        ∃ p l, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        C.size = 65 → PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) → C.output = 90 →
        C.gates[64]? = some ⟨.and, [a,b]⟩ →
        (∀ p l, E p l →
          let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          PEqualNP.BlindGate.wireValue C 26 x a = true ∧
            PEqualNP.BlindGate.wireValue C 26 x b = true) →
        (∀ x, Maximal (fun y => ¬ F y) x →
          PEqualNP.BlindGate.wireValue C 26 x (if x 13 then a else b) = false) →
        (∃ i < 64, 26 ≤ a ∧ 26 ≤ b ∧
          PEqualNP.SplitCount.InConeOrSelf 26 C i (a - 26) ∧
          PEqualNP.SplitCount.InConeOrSelf 26 C i (b - 26)) →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
          D.size ≤ 63 ∧ PEqualNP.TopForm.IsAO2 26 D ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧ u ≠ v ∧ u < 26 + D.size ∧ v < 26 + D.size ∧
          ∀ x : Fin 26 → Bool,
            PEqualNP.BlindGate.wireValue D 26 x u = PEqualNP.BlindGate.wireValue C 26 x a ∧
            PEqualNP.BlindGate.wireValue D 26 x v = PEqualNP.BlindGate.wireValue C 26 x b)
    (separate :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let F := fun x : Fin 26 → Bool =>
        ∃ p l, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        C.size = 65 → PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) → C.output = 90 →
        C.gates[64]? = some ⟨.and, [a,b]⟩ →
        (∀ p l, E p l →
          let x : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          PEqualNP.BlindGate.wireValue C 26 x a = true ∧
            PEqualNP.BlindGate.wireValue C 26 x b = true) →
        (∀ x, Maximal (fun y => ¬ F y) x →
          PEqualNP.BlindGate.wireValue C 26 x (if x 13 then a else b) = false) →
        ¬ (∃ i < 64, 26 ≤ a ∧ 26 ≤ b ∧
          PEqualNP.SplitCount.InConeOrSelf 26 C i (a - 26) ∧
          PEqualNP.SplitCount.InConeOrSelf 26 C i (b - 26)) →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
          D.size ≤ 63 ∧ PEqualNP.TopForm.IsAO2 26 D ∧
          (∀ g ∈ D.gates, g.inputs.Nodup) ∧ u ≠ v ∧ u < 26 + D.size ∧ v < 26 + D.size ∧
          ∀ x : Fin 26 → Bool,
            PEqualNP.BlindGate.wireValue D 26 x u = PEqualNP.BlindGate.wireValue C 26 x a ∧
            PEqualNP.BlindGate.wireValue D 26 x v = PEqualNP.BlindGate.wireValue C 26 x b) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x6 : ℕ),   (x3.size ≤ (65 : ℕ) ∧       PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧         (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧           x3.output = (26 : ℕ) + x4 ∧             x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧               (∀ (x7 x8 : Fin (13 : ℕ)),                   x1 x7 x8 →                     have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧                 ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) →     ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x6 := by
  dsimp only at shared separate ⊢
  intro C j a b h
  obtain ⟨hsize, hform, hn, hout, hj, hedge, hmax⟩ := h
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) :
      (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have keeps (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have jlt : j < C.gates.length := by
    by_contra! hh
    rw [List.getElem?_eq_none hh] at hj
    contradiction
  have atj : PEqualNP.MetaComplexity.NestedCover.gateAt C j = ⟨.and, [a,b]⟩ := by
    change C.gates.getD j ⟨.or, []⟩ = ⟨.and, [a,b]⟩
    simp [List.getD_eq_getElem?_getD, hj]
  have ha : a < 26 + j :=
    hform.2.1 j jlt a (by rw [atj]; simp)
  have hb : b < 26 + j :=
    hform.2.1 j jlt b (by rw [atj]; simp)
  by_cases hprefix : j < 64
  · let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take (j + 1), C.output⟩
    have dlen : D.gates.length = j+1 := by
      simp [D, Nat.min_eq_left (by omega : j+1 ≤ C.gates.length)]
    have dg (k : ℕ) (hk : k < D.gates.length) :
        PEqualNP.MetaComplexity.NestedCover.gateAt D k =
          PEqualNP.MetaComplexity.NestedCover.gateAt C k := by
      change (C.gates.take (j+1)).getD k ⟨.or, []⟩ = C.gates.getD k ⟨.or, []⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega : k < j+1)]
    have hdform : PEqualNP.TopForm.IsAO2 26 D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact hform.1 g (List.mem_of_mem_take hg)
      · intro k hk i hi
        rw [dg k hk] at hi
        exact hform.2.1 k (by omega) i hi
      · intro g hg
        exact hform.2.2 g (List.mem_of_mem_take hg)
    have deq (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26 + j) :
        PEqualNP.BlindGate.wireValue D 26 x i =
          PEqualNP.BlindGate.wireValue C 26 x i := by
      change ((C.gates.take (j+1)).foldl step (List.ofFn x)).getD i false =
        (C.gates.foldl step (List.ofFn x)).getD i false
      conv_rhs => rw [← List.take_append_drop (j+1) C.gates, List.foldl_append]
      symm
      apply keeps
      rw [len]
      simp only [List.length_ofFn, List.length_take]
      omega
    refine ⟨D, j, a, b, ?_, hdform, ?_, hout, ?_, fun x => ⟨deq x a ha, deq x b hb⟩⟩
    · change D.gates.length ≤ 64
      omega
    · intro g hg
      exact hn g (List.mem_of_mem_take hg)
    · change (C.gates.take (j+1))[j]? = _
      simpa only [List.getElem?_take_of_lt (by omega : j < j+1)] using hj
  have hlen : C.gates.length ≤ 65 := hsize
  have j64 : j = 64 := by omega
  subst j
  have csize : C.size = 65 := by
    change C.gates.length = 65
    omega
  have compressed : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
      D.size ≤ 63 ∧ PEqualNP.TopForm.IsAO2 26 D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ u ≠ v ∧ u < 26 + D.size ∧ v < 26 + D.size ∧
      ∀ x : Fin 26 → Bool,
        PEqualNP.BlindGate.wireValue D 26 x u = PEqualNP.BlindGate.wireValue C 26 x a ∧
        PEqualNP.BlindGate.wireValue D 26 x v = PEqualNP.BlindGate.wireValue C 26 x b := by
    classical
    by_cases common : ∃ i < 64, 26 ≤ a ∧ 26 ≤ b ∧
        PEqualNP.SplitCount.InConeOrSelf 26 C i (a - 26) ∧
        PEqualNP.SplitCount.InConeOrSelf 26 C i (b - 26)
    · exact shared C a b csize hform hn hout hj hedge hmax common
    · exact separate C a b csize hform hn hout hj hedge hmax common
  obtain ⟨D, u, v, dsize, dform, dn, huv, hu, hv, hvalues⟩ := compressed
  let root : PEqualNP.CircuitLowerBounds.Gate := ⟨.and, [u,v]⟩
  let A : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨D.gates ++ [root], 26 + D.size⟩
  have ds : D.gates.length ≤ 63 := dsize
  have alen : A.gates.length = D.gates.length + 1 := by simp [A]
  have ag (k : ℕ) (hk : k < D.gates.length) :
      PEqualNP.MetaComplexity.NestedCover.gateAt A k =
        PEqualNP.MetaComplexity.NestedCover.gateAt D k := by
    change (D.gates ++ [root]).getD k ⟨.or, []⟩ = D.gates.getD k ⟨.or, []⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have ar : PEqualNP.MetaComplexity.NestedCover.gateAt A D.gates.length = root := by
    change (D.gates ++ [root]).getD D.gates.length ⟨.or, []⟩ = root
    simp [List.getD_eq_getElem?_getD]
  have aform : PEqualNP.TopForm.IsAO2 26 A := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hr | hr
      · exact dform.1 g hr
      · cases List.mem_singleton.mp hr
        exact Or.inl rfl
    · intro k hk i hi
      by_cases hlt : k < D.gates.length
      · rw [ag k hlt] at hi
        exact dform.2.1 k hlt i hi
      · have e : k = D.gates.length := by omega
        subst k
        rw [ar] at hi
        simp [root] at hi
        rcases hi with rfl | rfl
        · exact hu
        · exact hv
    · intro g hg
      rcases List.mem_append.mp hg with hr | hr
      · exact dform.2.2 g hr
      · cases List.mem_singleton.mp hr
        rfl
  have aeq (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26 + D.size) :
      PEqualNP.BlindGate.wireValue A 26 x i =
        PEqualNP.BlindGate.wireValue D 26 x i := by
    change ((D.gates ++ [root]).foldl step (List.ofFn x)).getD i false =
      (D.gates.foldl step (List.ofFn x)).getD i false
    rw [List.foldl_append]
    apply keeps
    change i < 26 + D.gates.length at hi
    simpa only [len, List.length_ofFn] using hi
  refine ⟨A, D.size, u, v, ?_, aform, ?_, rfl, ?_, fun x =>
    ⟨(aeq x u hu).trans (hvalues x).1, (aeq x v hv).trans (hvalues x).2⟩⟩
  · change A.gates.length ≤ 64
    omega
  · intro g hg
    rcases List.mem_append.mp hg with hr | hr
    · exact dn g hr
    · cases List.mem_singleton.mp hr
      simpa [root] using huv
  · change (D.gates ++ [root])[D.gates.length]? = some root
    simp
