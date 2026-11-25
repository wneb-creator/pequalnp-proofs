import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1904_137
    (singletonNormalization :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  G.edgeFinset.Nonempty →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ C.size ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n D j (PEqualNP.EdgeOwnership.pairInput v v) = false)
    (singletonBudget :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  G.edgeFinset.Nonempty →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
    (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput v v) = false) →
    ∃ U : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G U ∧
      G.edgeFinset.card + U.card ≤ C.size + 1)
    (coverBuilder :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)),
  (∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    D.size ≤ G.edgeFinset.card + U.card - 1 ∧
    ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  intro n G inst htri hsquare
  by_cases hE : G.edgeFinset.Nonempty
  · have toGraph (C : PEqualNP.CircuitLowerBounds.Circuit)
        (h : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) :
        PEqualNP.MetaComplexity.circuitFun n C =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext x
      change C.eval (List.ofFn x) =
        (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
         decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true))
      simpa using h x
    let Fits (k : ℕ) : Prop := ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      C.size = k
    obtain ⟨C0, hm0, hex0, _, _⟩ :=
      coverBuilder n G Finset.univ (fun a _ _ => Or.inl (Finset.mem_univ a))
    have hEx : ∃ k, Fits k := ⟨C0.size, C0, hm0, toGraph C0 hex0, rfl⟩
    obtain ⟨K, hmK, hFK, hk⟩ := Nat.find_spec hEx
    have leastK (C : PEqualNP.CircuitLowerBounds.Circuit)
        (hm : PEqualNP.MetaComplexity.Monotone2 C)
        (hF : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
        K.size ≤ C.size := by
      rw [hk]
      exact Nat.find_min' hEx (show Fits C.size from ⟨C, hm, hF, rfl⟩)
    obtain ⟨M, hmM, hFM, hMK, hsingle⟩ :=
      singletonNormalization n G htri hsquare hE K hmK hFK
    have hminM : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n M := by
      refine ⟨hmM, ?_⟩
      intro C hm hF
      exact hMK.trans (leastK C hm (hF.trans hFM))
    obtain ⟨U, hU, hcost⟩ := singletonBudget n G htri hsquare hE M hminM hFM hsingle
    obtain ⟨D, hmD, hexD, hsizeD, hhonestD⟩ := coverBuilder n G U hU
    refine ⟨D, hmD, hexD, ?_, hhonestD⟩
    intro C hmC hexC
    have hDM : D.size ≤ M.size := by omega
    exact hDM.trans (hMK.trans (leastK C hmC (toGraph C hexC)))
  · have hEmpty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hCov : ∀ a b : Fin n, G.Adj a b → a ∈ (∅ : Finset (Fin n)) ∨ b ∈ (∅ : Finset (Fin n)) := by
      intro a b hab
      exact (hE ⟨s(a, b), by simpa using hab⟩).elim
    obtain ⟨D, hmD, hexD, hsizeD, hhonestD⟩ := coverBuilder n G ∅ hCov
    refine ⟨D, hmD, hexD, ?_, hhonestD⟩
    intro C _ _
    simp only [hEmpty, Finset.card_empty, Nat.add_zero, Nat.zero_sub] at hsizeD
    omega
