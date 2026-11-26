import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5075_575
    (hStrip : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ D : PEqualNP.AndCount.AndCountCircuit n,
        D.WellFormed ∧
        D.size ≤ {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ∧
        (∀ (i : Fin D.size) (v : Fin n), D.gateVal {v} i = false) ∧
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ U : Finset (Fin n), U.Nonempty →
          D.eval U = PEqualNP.MetaComplexity.circuitFun n C (fun k => decide (k ∈ U))))
    (hCoreElim : ∀ (n : ℕ) (D : PEqualNP.AndCount.AndCountCircuit n),
      D.WellFormed → D.outVars = ∅ →
      (∀ (i : Fin D.size) (v : Fin n), D.gateVal {v} i = false) →
      (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
      ∃ (X : Finset (Fin n)) (D' : PEqualNP.AndCount.AndCountCircuit n),
        X.card + D'.size ≤ D.size ∧
        D'.WellFormed ∧ D'.outVars = ∅ ∧
        (∀ (i : Fin D'.size) (v : Fin n), D'.gateVal {v} i = false) ∧
        (∀ i : Fin D'.size, Disjoint (D'.leftVars i) (D'.rightVars i)) ∧
        (∀ i : Fin D'.size, Disjoint (D'.leftVars i) X ∧ Disjoint (D'.rightVars i) X) ∧
        (∀ i : Fin D'.size, (2 ≤ (D'.leftVars i).card ∨ (D'.leftGates i).Nonempty) ∧
          (2 ≤ (D'.rightVars i).card ∨ (D'.rightGates i).Nonempty)) ∧
        (∀ U : Finset (Fin n), Disjoint U X → D'.eval U = D.eval U))
    (hCorePG23 : ∀ (X : Finset (Fin (13 + 13))) (D : PEqualNP.AndCount.AndCountCircuit (13 + 13)),
      D.WellFormed → D.outVars = ∅ → 2 ≤ D.size → X.card + D.size ≤ 12 →
      (∀ (i : Fin D.size) (v : Fin (13 + 13)), D.gateVal {v} i = false) →
      (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
      (∀ i : Fin D.size, Disjoint (D.leftVars i) X ∧ Disjoint (D.rightVars i) X) →
      (∀ i : Fin D.size, (2 ≤ (D.leftVars i).card ∨ (D.leftGates i).Nonempty) ∧
        (2 ≤ (D.rightVars i).card ∨ (D.rightGates i).Nonempty)) →
      (∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
        Fin.castAdd 13 p ∉ X → Fin.natAdd 13 l ∉ X →
        D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
      (∀ S : Finset (Fin 13),
        (∀ p ∉ S, ∃ l : Fin 13, (∀ q ∈ S, ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)) ∧
          (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) →
        (¬∃ l : Fin 13, ∀ p ∈ S, p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
        (¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)) →
          p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
        D.eval (S.image (Fin.castAdd 13) ∪
          (Finset.univ.filter (fun l : Fin 13 =>
            ∀ q ∈ S, ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9))).image (Fin.natAdd 13)) = false) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → ∃ (x5 : Finset (Fin ((13 : ℕ) + (13 : ℕ)))), (∀ (x6 x7 : Fin (13 : ℕ)), x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)) → Fin.castAdd (13 : ℕ) x6 ∈ x5 ∨ Fin.natAdd (13 : ℕ) x7 ∈ x5) ∧ x5.card ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hmono hpos hneg
  let k : ℕ := {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard
  by_cases hk : 13 ≤ k
  · refine ⟨Finset.univ.image (Fin.castAdd 13), ?_, ?_⟩
    · intro p _ _
      exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ p))
    · rw [Finset.card_image_of_injective _ (Fin.castAdd_injective 13 13), Finset.card_fin]
      exact hk
  · exfalso
    have hk12 : k ≤ 12 := by omega
    have hfuel0 (D : PEqualNP.AndCount.AndCountCircuit (13 + 13)) (U : Finset (Fin (13 + 13)))
        (i : Fin D.size) : D.gateValFuel U 0 i = false := rfl
    have hfuelS (D : PEqualNP.AndCount.AndCountCircuit (13 + 13)) (U : Finset (Fin (13 + 13)))
        (d : ℕ) (i : Fin D.size) :
        D.gateValFuel U (d + 1) i =
          (PEqualNP.AndCount.AndCountCircuit.sideTrue U (D.leftVars i) (D.leftGates i) i
            (D.gateValFuel U d) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (D.rightVars i) (D.rightGates i) i
            (D.gateValFuel U d)) := rfl
    have hgateVal_eq (D : PEqualNP.AndCount.AndCountCircuit (13 + 13)) (U : Finset (Fin (13 + 13)))
        (i : Fin D.size) : D.gateVal U i = D.gateValFuel U D.size i := rfl
    have heval_eq (D : PEqualNP.AndCount.AndCountCircuit (13 + 13)) (U : Finset (Fin (13 + 13))) :
        D.eval U = decide ((∃ v ∈ D.outVars, v ∈ U) ∨ ∃ j ∈ D.outGates, D.gateVal U j = true) := rfl
    have hside_eq (U B : Finset (Fin (13 + 13))) (k : ℕ) (F : Finset (Fin k)) (i : Fin k)
        (val : Fin k → Bool) :
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
          decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := rfl
    have hmonoD (D : PEqualNP.AndCount.AndCountCircuit (13 + 13))
        (U V : Finset (Fin (13 + 13))) (hUV : U ⊆ V) :
        D.eval U = true → D.eval V = true := by
      have hfuel : ∀ d : ℕ, ∀ i : Fin D.size,
          D.gateValFuel U d i = true → D.gateValFuel V d i = true := by
        intro d
        induction d with
        | zero =>
          intro i h
          rw [hfuel0] at h
          cases h
        | succ d ih =>
          intro i h
          rw [hfuelS] at h ⊢
          rw [Bool.and_eq_true] at h ⊢
          have hside : ∀ (B : Finset (Fin (13 + 13))) (F : Finset (Fin D.size)),
              PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (D.gateValFuel U d) = true →
              PEqualNP.AndCount.AndCountCircuit.sideTrue V B F i (D.gateValFuel V d) = true := by
            intro B F hs
            rw [hside_eq] at hs ⊢
            rw [decide_eq_true_eq] at hs ⊢
            rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjval⟩
            · exact Or.inl ⟨v, hvB, hUV hvU⟩
            · exact Or.inr ⟨j, hjF, hji, ih j hjval⟩
          exact ⟨hside _ _ h.1, hside _ _ h.2⟩
      intro h
      rw [heval_eq] at h ⊢
      rw [decide_eq_true_eq] at h ⊢
      rcases h with ⟨v, hvO, hvU⟩ | ⟨j, hjO, hjval⟩
      · exact Or.inl ⟨v, hvO, hUV hvU⟩
      · exact Or.inr ⟨j, hjO, hfuel D.size j hjval⟩
    have hdiffD (D : PEqualNP.AndCount.AndCountCircuit (13 + 13))
        (X U : Finset (Fin (13 + 13))) (hout : D.outVars = ∅)
        (hdisjX : ∀ i : Fin D.size, Disjoint (D.leftVars i) X ∧ Disjoint (D.rightVars i) X) :
        D.eval U = D.eval (U \ X) := by
      have hfuel : ∀ d : ℕ, ∀ i : Fin D.size,
          D.gateValFuel U d i = D.gateValFuel (U \ X) d i := by
        intro d
        induction d with
        | zero =>
          intro i
          rw [hfuel0, hfuel0]
        | succ d ih =>
          intro i
          rw [hfuelS, hfuelS]
          have hside : ∀ (B : Finset (Fin (13 + 13))) (F : Finset (Fin D.size)),
              Disjoint B X →
              PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (D.gateValFuel U d) =
              PEqualNP.AndCount.AndCountCircuit.sideTrue (U \ X) B F i (D.gateValFuel (U \ X) d) := by
            intro B F hBX
            rw [hside_eq, hside_eq]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq]
            constructor
            · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjval⟩)
              · refine Or.inl ⟨v, hvB, Finset.mem_sdiff.mpr ⟨hvU, ?_⟩⟩
                exact Finset.disjoint_left.mp hBX hvB
              · exact Or.inr ⟨j, hjF, hji, (ih j).symm.trans hjval⟩
            · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjval⟩)
              · exact Or.inl ⟨v, hvB, (Finset.mem_sdiff.mp hvU).1⟩
              · exact Or.inr ⟨j, hjF, hji, (ih j).trans hjval⟩
          rw [hside _ _ (hdisjX i).1, hside _ _ (hdisjX i).2]
      rw [heval_eq, heval_eq, hout]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
      constructor
      · rintro ⟨j, hjO, hjval⟩
        exact ⟨j, hjO, (hfuel D.size j).symm.trans hjval⟩
      · rintro ⟨j, hjO, hjval⟩
        exact ⟨j, hjO, (hfuel D.size j).trans hjval⟩
    let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let genSet : Finset (Fin 13) → Finset (Fin (13 + 13)) := fun S =>
      S.image (Fin.castAdd 13) ∪
        (Finset.univ.filter (fun l : Fin 13 => ∀ q ∈ S, ¬ I q l)).image (Fin.natAdd 13)
    let isEdge : Fin (13 + 13) → Fin (13 + 13) → Prop := fun u v =>
      ∃ p l : Fin 13, I p l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p))
    let incB : Fin 13 → Fin 13 → Bool := fun p l =>
      (p == l) || (p == l + 1) || (p == l + 3) || (p == l + 9)
    let genRaw : List (List (Fin 13)) :=
      [[0, 1, 2], [3, 4, 5], [6, 8, 12], [7, 9, 10, 11], [2, 4, 7], [0, 4, 6, 9],
       [0, 3, 8, 11], [3, 10, 12], [2, 5, 8, 10], [1, 6, 7], [1, 2, 9, 12],
       [5, 6, 11], [7, 8, 9], [0, 4, 10, 12], [2, 3, 6], [1, 10, 11], [5, 7, 12],
       [4, 11, 12], [1, 3, 4, 8], [0, 3, 7], [0, 5, 9], [2, 3, 9], [0, 1, 5],
       [1, 6, 10], [0, 2, 11]]
    let edgeB : Fin (13 + 13) → Fin (13 + 13) → Bool := fun u v =>
      (List.finRange 13).any fun p => (List.finRange 13).any fun l =>
        incB p l && ((u == Fin.castAdd 13 p && v == Fin.natAdd 13 l) ||
          (u == Fin.natAdd 13 l && v == Fin.castAdd 13 p))
    let inGenB : List (Fin 13) → Fin (13 + 13) → Bool := fun L u =>
      (List.finRange 13).any (fun p => (u == Fin.castAdd 13 p) && L.contains p) ||
      (List.finRange 13).any (fun l => (u == Fin.natAdd 13 l) && L.all (fun q => !incB q l))
    have hGenValidB : genRaw.all (fun L =>
        ((List.finRange 13).all fun p => L.contains p ||
          (List.finRange 13).any fun l => L.all (fun q => !incB q l) && incB p l) &&
        ((List.finRange 13).all fun l => !L.all (fun p => incB p l)) &&
        ((List.finRange 13).all fun p =>
          !((List.finRange 13).all fun l => !L.all (fun q => !incB q l) || incB p l))) = true := by
      decide +kernel
    have hCovB : (List.finRange (13 + 13)).all (fun u => (List.finRange (13 + 13)).all (fun v =>
        edgeB u v || genRaw.any (fun L => inGenB L u && inGenB L v))) = true := by
      decide +kernel
    have hDiffsB : (([0, 1, 3, 9] : List (Fin 13)).all fun d1 =>
        ([0, 1, 3, 9] : List (Fin 13)).all fun d2 =>
          ([0, 1, 3, 9] : List (Fin 13)).all fun d3 =>
            ([0, 1, 3, 9] : List (Fin 13)).all fun d4 =>
              (d1 == d2) || (d1 - d2 != d3 - d4) || (d1 == d3)) = true := by
      decide +kernel
    have hinc_iff (p l : Fin 13) : incB p l = true ↔ I p l := by
      simp only [incB, Bool.or_eq_true, beq_iff_eq, I, or_assoc]
    have hGenValid : ∀ L ∈ genRaw,
        (∀ p ∉ L.toFinset, ∃ l : Fin 13, (∀ q ∈ L.toFinset, ¬ I q l) ∧ I p l) ∧
        (¬ ∃ l : Fin 13, ∀ p ∈ L.toFinset, I p l) ∧
        (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ L.toFinset, ¬ I q l) → I p l) := by
      intro L hL
      have hLall := List.all_eq_true.mp hGenValidB L hL
      rw [Bool.and_eq_true, Bool.and_eq_true] at hLall
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        have hpB := List.all_eq_true.mp hLall.1.1 p (List.mem_finRange p)
        rw [Bool.or_eq_true] at hpB
        rcases hpB with hcont | hex
        · exact False.elim (hp (List.mem_toFinset.mpr (List.contains_iff_mem.mp hcont)))
        · rw [List.any_eq_true] at hex
          rcases hex with ⟨l, _, hl⟩
          rw [Bool.and_eq_true] at hl
          refine ⟨l, ?_, (hinc_iff p l).mp hl.2⟩
          intro q hq
          have hqB := List.all_eq_true.mp hl.1 q (List.mem_toFinset.mp hq)
          rw [Bool.not_eq_true'] at hqB
          intro hI
          rw [(hinc_iff q l).mpr hI] at hqB
          cases hqB
      · rintro ⟨l, hl⟩
        have hlB := List.all_eq_true.mp hLall.1.2 l (List.mem_finRange l)
        rw [Bool.not_eq_true'] at hlB
        have htrue : L.all (fun p => incB p l) = true :=
          List.all_eq_true.mpr (fun p hp => (hinc_iff p l).mpr (hl p (List.mem_toFinset.mpr hp)))
        rw [htrue] at hlB
        cases hlB
      · rintro ⟨p, hp⟩
        have hpB := List.all_eq_true.mp hLall.2 p (List.mem_finRange p)
        rw [Bool.not_eq_true'] at hpB
        have htrue : (List.finRange 13).all
            (fun l => !L.all (fun q => !incB q l) || incB p l) = true := by
          refine List.all_eq_true.mpr (fun l _ => ?_)
          rw [Bool.or_eq_true]
          by_cases hmiss : ∀ q ∈ L.toFinset, ¬ I q l
          · exact Or.inr ((hinc_iff p l).mpr (hp l hmiss))
          · push Not at hmiss
            rcases hmiss with ⟨q, hqL, hqI⟩
            refine Or.inl ?_
            have hfalse : L.all (fun q => !incB q l) = false := by
              rw [Bool.eq_false_iff]
              intro hnot
              have hqB := List.all_eq_true.mp hnot q (List.mem_toFinset.mp hqL)
              rw [Bool.not_eq_true', (hinc_iff q l).mpr hqI] at hqB
              cases hqB
            rw [hfalse]
            rfl
        rw [htrue] at hpB
        cases hpB
    have hNonEdgeCov : ∀ u v : Fin (13 + 13), ¬ isEdge u v →
        ∃ L ∈ genRaw, u ∈ genSet L.toFinset ∧ v ∈ genSet L.toFinset := by
      intro u v hno
      have huvB := List.all_eq_true.mp
        (List.all_eq_true.mp hCovB u (List.mem_finRange u)) v (List.mem_finRange v)
      rw [Bool.or_eq_true] at huvB
      rcases huvB with hedge | hcov
      · exfalso
        apply hno
        rw [List.any_eq_true] at hedge
        rcases hedge with ⟨p, _, hp⟩
        rw [List.any_eq_true] at hp
        rcases hp with ⟨l, _, hl⟩
        rw [Bool.and_eq_true] at hl
        have hl2 := hl.2
        rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hl2
        refine ⟨p, l, (hinc_iff p l).mp hl.1, ?_⟩
        rcases hl2 with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · exact Or.inl ⟨beq_iff_eq.mp hu, beq_iff_eq.mp hv⟩
        · exact Or.inr ⟨beq_iff_eq.mp hu, beq_iff_eq.mp hv⟩
      · rw [List.any_eq_true] at hcov
        rcases hcov with ⟨L, hLmem, hLuv⟩
        rw [Bool.and_eq_true] at hLuv
        have hinSet : ∀ w : Fin (13 + 13), inGenB L w = true → w ∈ genSet L.toFinset := by
          intro w hw
          rw [Bool.or_eq_true] at hw
          rcases hw with hpt | hln
          · rw [List.any_eq_true] at hpt
            rcases hpt with ⟨p, _, hp⟩
            rw [Bool.and_eq_true] at hp
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr (List.contains_iff_mem.mp hp.2),
              (beq_iff_eq.mp hp.1).symm⟩
          · rw [List.any_eq_true] at hln
            rcases hln with ⟨l, _, hl⟩
            rw [Bool.and_eq_true] at hl
            refine Finset.mem_union_right _ ?_
            refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩,
              (beq_iff_eq.mp hl.1).symm⟩
            intro q hq
            have hqB := List.all_eq_true.mp hl.2 q (List.mem_toFinset.mp hq)
            rw [Bool.not_eq_true'] at hqB
            intro hI
            rw [(hinc_iff q l).mpr hI] at hqB
            cases hqB
        exact ⟨L, hLmem, hinSet u hLuv.1, hinSet v hLuv.2⟩
    have hNoC4_pts : ∀ p1 p2 l1 l2 : Fin 13,
        p1 ≠ p2 → l1 ≠ l2 → I p1 l1 → I p1 l2 → I p2 l1 → ¬ I p2 l2 := by
      intro p1 p2 l1 l2 hp hl h11 h12 h21 h22
      have hdiff_mem : ∀ p l : Fin 13, I p l → p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
        intro p l hI
        rcases hI with h | h | h | h
        · rw [h, sub_self]; simp
        · rw [h]; simp
        · rw [h]; simp
        · rw [h]; simp
      have ha1 := List.all_eq_true.mp hDiffsB _ (hdiff_mem p1 l1 h11)
      have ha2 := List.all_eq_true.mp ha1 _ (hdiff_mem p1 l2 h12)
      have ha3 := List.all_eq_true.mp ha2 _ (hdiff_mem p2 l1 h21)
      have ha4 := List.all_eq_true.mp ha3 _ (hdiff_mem p2 l2 h22)
      rw [Bool.or_eq_true, Bool.or_eq_true] at ha4
      rcases ha4 with (heq12 | hne) | heq13
      · apply hl
        have hs : p1 - l1 = p1 - l2 := beq_iff_eq.mp heq12
        exact sub_right_inj.mp hs
      · exfalso
        have hcon : (p1 - l1) - (p1 - l2) = (p2 - l1) - (p2 - l2) := by
          rw [sub_sub_sub_cancel_left, sub_sub_sub_cancel_left]
        rw [hcon] at hne
        simp only [bne_self_eq_false] at hne
        cases hne
      · apply hp
        have hs : p1 - l1 = p2 - l1 := beq_iff_eq.mp heq13
        exact sub_left_inj.mp hs
    have hCastNeNat (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hNoC4 : ∀ u1 u2 v1 v2 : Fin (13 + 13),
        u1 ≠ u2 → v1 ≠ v2 →
        isEdge u1 v1 → isEdge u1 v2 → isEdge u2 v1 → ¬ isEdge u2 v2 := by
      intro u1 u2 v1 v2 hu hv h11 h12 h21 h22
      rcases h11 with ⟨p1, l1, hp1l1, ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩⟩
      · rcases h12 with ⟨p1', l2, hp1'l2, ⟨hu1', hv2⟩ | ⟨hu1', hv2⟩⟩
        · have hp1eq : p1' = p1 := Fin.castAdd_injective 13 13 (hu1'.symm.trans hu1)
          rw [hp1eq] at hp1'l2
          rcases h21 with ⟨p2, l1', hp2l1', ⟨hu2, hv1'⟩ | ⟨hu2, hv1'⟩⟩
          · have hl1eq : l1' = l1 := Fin.natAdd_injective 13 13 (hv1'.symm.trans hv1)
            rw [hl1eq] at hp2l1'
            rcases h22 with ⟨p2', l2', hp2'l2', ⟨hu2', hv2'⟩ | ⟨hu2', hv2'⟩⟩
            · have hp2eq : p2' = p2 := Fin.castAdd_injective 13 13 (hu2'.symm.trans hu2)
              have hl2eq : l2' = l2 := Fin.natAdd_injective 13 13 (hv2'.symm.trans hv2)
              rw [hp2eq, hl2eq] at hp2'l2'
              have hpne : p1 ≠ p2 := fun h => hu (hu1.trans (h ▸ hu2.symm))
              have hlne : l1 ≠ l2 := fun h => hv (hv1.trans (h ▸ hv2.symm))
              exact hNoC4_pts p1 p2 l1 l2 hpne hlne hp1l1 hp1'l2 hp2l1' hp2'l2'
            · exact hCastNeNat p2 l2' (hu2.symm.trans hu2')
          · exact hCastNeNat p2 l1 (hv1'.symm.trans hv1)
        · exact hCastNeNat p1 l2 (hu1.symm.trans hu1')
      · rcases h12 with ⟨p2, l1', hp2l1', ⟨hu1', hv2⟩ | ⟨hu1', hv2⟩⟩
        · exact hCastNeNat p2 l1 (hu1'.symm.trans hu1)
        · have hl1eq : l1' = l1 := Fin.natAdd_injective 13 13 (hu1'.symm.trans hu1)
          rw [hl1eq] at hp2l1'
          rcases h21 with ⟨p1', l2, hp1'l2, ⟨hu2, hv1'⟩ | ⟨hu2, hv1'⟩⟩
          · exact hCastNeNat p1 l2 (hv1.symm.trans hv1')
          · have hp1eq : p1' = p1 := Fin.castAdd_injective 13 13 (hv1'.symm.trans hv1)
            rw [hp1eq] at hp1'l2
            rcases h22 with ⟨p2', l2', hp2'l2', ⟨hu2', hv2'⟩ | ⟨hu2', hv2'⟩⟩
            · exact hCastNeNat p2' l2 (hu2'.symm.trans hu2)
            · have hl2eq : l2' = l2 := Fin.natAdd_injective 13 13 (hu2'.symm.trans hu2)
              have hp2eq : p2' = p2 := Fin.castAdd_injective 13 13 (hv2'.symm.trans hv2)
              rw [hp2eq, hl2eq] at hp2'l2'
              have hpne : p1 ≠ p2 := fun h => hv (hv1.trans (h ▸ hv2.symm))
              have hlne : l1 ≠ l2 := fun h => hu (hu1.trans (h ▸ hu2.symm))
              exact hNoC4_pts p1 p2 l1 l2 hpne hlne hp1l1 hp1'l2 hp2l1' hp2'l2'
    obtain ⟨D, hD_wf, hD_size, hD_sing, hD_disj, hD_eq⟩ := hStrip (13 + 13) C hmono
    have hD_pos : ∀ p l : Fin 13, I p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
      intro p l hI
      rw [hD_eq {Fin.castAdd 13 p, Fin.natAdd 13 l} (Finset.insert_nonempty _ _)]
      have hfun : (fun k : Fin (13 + 13) =>
            decide (k ∈ ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin (13 + 13))))) =
          fun k : Fin (13 + 13) => Decidable.decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l) := by
        funext k
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      rw [hfun]
      exact hpos p l hI
    have hD_neg : ∀ S : Finset (Fin 13),
        (∀ p ∉ S, ∃ l : Fin 13, (∀ q ∈ S, ¬ I q l) ∧ I p l) →
        (¬ ∃ l : Fin 13, ∀ p ∈ S, I p l) →
        (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬ I q l) → I p l) →
        D.eval (genSet S) = false := by
      intro S h1 h2 h3
      have hne : (genSet S).Nonempty := by
        by_cases hS : S.Nonempty
        · rcases hS with ⟨p, hp⟩
          exact ⟨Fin.castAdd 13 p, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
        · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
          refine ⟨Fin.natAdd 13 0, Finset.mem_union_right _ ?_⟩
          refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, ?_⟩)
          intro q hq
          rw [hSempty] at hq
          exact False.elim (Finset.notMem_empty q hq)
      rw [hD_eq (genSet S) hne]
      have hsub := hneg S h1 ⟨h2, h3⟩
      rw [← hsub]
      apply congrArg (PEqualNP.MetaComplexity.circuitFun (13 + 13) C)
      funext k
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, genSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, eq_comm, and_comm, I]
    have hD_outVars : D.outVars = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => ?_)
      have hno : ¬ isEdge v v := by
        rintro ⟨p, l, _, ⟨hp, hl⟩ | ⟨hl, hp⟩⟩
        · exact hCastNeNat p l (hp.symm.trans hl)
        · exact hCastNeNat p l (hp.symm.trans hl)
      rcases hNonEdgeCov v v hno with ⟨L, hLmem, hvL, _⟩
      have htrue : D.eval (genSet L.toFinset) = true := by
        rw [heval_eq, decide_eq_true_eq]
        exact Or.inl ⟨v, hv, hvL⟩
      have hvalid := hGenValid L hLmem
      have hfalse := hD_neg L.toFinset hvalid.1 hvalid.2.1 hvalid.2.2
      rw [htrue] at hfalse
      cases hfalse
    obtain ⟨X, D', hXD'_size, hD'_wf, hD'_out, hD'_sing, hD'_disj, hD'_disjX, hD'_core, hD'_eq⟩ :=
      hCoreElim (13 + 13) D hD_wf hD_outVars hD_sing hD_disj
    have hD'_pos : ∀ p l : Fin 13, I p l →
        Fin.castAdd 13 p ∉ X → Fin.natAdd 13 l ∉ X →
        D'.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
      intro p l hI hp hl
      have hdisj : Disjoint ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin (13 + 13))) X := by
        refine Finset.disjoint_left.mpr (fun w hw => ?_)
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      rw [hD'_eq _ hdisj]
      exact hD_pos p l hI
    have hD'_neg : ∀ S : Finset (Fin 13),
        (∀ p ∉ S, ∃ l : Fin 13, (∀ q ∈ S, ¬ I q l) ∧ I p l) →
        (¬ ∃ l : Fin 13, ∀ p ∈ S, I p l) →
        (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬ I q l) → I p l) →
        D'.eval (genSet S) = false := by
      intro S h1 h2 h3
      by_contra hnot
      rw [Bool.not_eq_false] at hnot
      rw [hdiffD D' X (genSet S) hD'_out hD'_disjX, hD'_eq _ Finset.sdiff_disjoint] at hnot
      have hDtrue := hmonoD D (genSet S \ X) (genSet S) Finset.sdiff_subset hnot
      have hDfalse := hD_neg S h1 h2 h3
      rw [hDtrue] at hDfalse
      cases hDfalse
    have hMatching : (∀ p l : Fin 13, I p l → Fin.castAdd 13 p ∈ X ∨ Fin.natAdd 13 l ∈ X) →
        13 ≤ X.card := by
      intro hcov
      let f : Fin 13 → Fin (13 + 13) := fun p =>
        if Fin.castAdd 13 p ∈ X then Fin.castAdd 13 p else Fin.natAdd 13 p
      have hfmem : ∀ p : Fin 13, f p ∈ X := by
        intro p
        dsimp only [f]
        by_cases hp : Fin.castAdd 13 p ∈ X
        · rw [if_pos hp]; exact hp
        · rw [if_neg hp]
          rcases hcov p p (Or.inl rfl) with hp' | hl'
          · exact False.elim (hp hp')
          · exact hl'
      have hfinj : ∀ p q : Fin 13, f p = f q → p = q := by
        intro p q hpq
        dsimp only [f] at hpq
        by_cases hp : Fin.castAdd 13 p ∈ X <;> by_cases hq : Fin.castAdd 13 q ∈ X
        · rw [if_pos hp, if_pos hq] at hpq; exact Fin.castAdd_injective 13 13 hpq
        · rw [if_pos hp, if_neg hq] at hpq; exact False.elim (hCastNeNat p q hpq)
        · rw [if_neg hp, if_pos hq] at hpq; exact False.elim (hCastNeNat q p hpq.symm)
        · rw [if_neg hp, if_neg hq] at hpq; exact Fin.natAdd_injective 13 13 hpq
      have hle : (Finset.univ : Finset (Fin 13)).card ≤ X.card :=
        Finset.card_le_card_of_injOn f (fun p _ => hfmem p) (fun p _ q _ h => hfinj p q h)
      simpa only [Finset.card_fin] using hle
    have hD'_ge2 : 2 ≤ D'.size := by
      by_contra hlt
      have hle1 : D'.size ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with hzero | hone
      · have hX13 : 13 ≤ X.card := by
          refine hMatching (fun p l hI => ?_)
          by_contra hneither
          push Not at hneither
          have htrue := hD'_pos p l hI hneither.1 hneither.2
          rw [heval_eq, hD'_out, decide_eq_true_eq] at htrue
          rcases htrue with ⟨v, hv, _⟩ | ⟨j, _, _⟩
          · exact Finset.notMem_empty v hv
          · have := j.isLt; omega
        have hk_bound : k ≤ 12 := hk12
        have hD_le : D.size ≤ k := hD_size
        omega
      · have hne0 : 0 < D'.size := by omega
        let z : Fin D'.size := ⟨0, hne0⟩
        have hz_out : z ∈ D'.outGates := by
          by_contra hznot
          have hX13 : 13 ≤ X.card := by
            refine hMatching (fun p l hI => ?_)
            by_contra hneither
            push Not at hneither
            have htrue := hD'_pos p l hI hneither.1 hneither.2
            rw [heval_eq, hD'_out, decide_eq_true_eq] at htrue
            rcases htrue with ⟨v, hv, _⟩ | ⟨j, hj, _⟩
            · exact Finset.notMem_empty v hv
            · have hjeq : j = z := Fin.ext (by omega)
              rw [hjeq] at hj
              exact hznot hj
          have hD_le : D.size ≤ k := hD_size
          omega
        have hz_lg : D'.leftGates z = ∅ := by
          refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
          have hltj := (hD'_wf z).1 j hj
          change j.val < z.val at hltj
          omega
        have hz_rg : D'.rightGates z = ∅ := by
          refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
          have hltj := (hD'_wf z).2 j hj
          change j.val < z.val at hltj
          omega
        have hcardL : 2 ≤ (D'.leftVars z).card := by
          rcases (hD'_core z).1 with h | h
          · exact h
          · rw [hz_lg] at h; exact False.elim (Finset.not_nonempty_empty h)
        have hcardR : 2 ≤ (D'.rightVars z).card := by
          rcases (hD'_core z).2 with h | h
          · exact h
          · rw [hz_rg] at h; exact False.elim (Finset.not_nonempty_empty h)
        have hAllEdge : ∀ u ∈ D'.leftVars z, ∀ v ∈ D'.rightVars z, isEdge u v := by
          intro u hu v hv
          by_contra hno
          have hgz : D'.gateVal {u, v} z = true := by
            rw [hgateVal_eq, hone, hfuelS, Bool.and_eq_true]
            refine ⟨?_, ?_⟩
            · rw [hside_eq, decide_eq_true_eq]
              exact Or.inl ⟨u, hu, Finset.mem_insert_self u {v}⟩
            · rw [hside_eq, decide_eq_true_eq]
              exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem (Finset.mem_singleton_self v)⟩
          have hev : D'.eval {u, v} = true := by
            rw [heval_eq, decide_eq_true_eq]
            exact Or.inr ⟨z, hz_out, hgz⟩
          rcases hNonEdgeCov u v hno with ⟨L, hLmem, huL, hvL⟩
          have hsub : ({u, v} : Finset (Fin (13 + 13))) ⊆ genSet L.toFinset := by
            intro w hw
            rw [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have hGtrue := hmonoD D' {u, v} (genSet L.toFinset) hsub hev
          have hvalid := hGenValid L hLmem
          have hGfalse := hD'_neg L.toFinset hvalid.1 hvalid.2.1 hvalid.2.2
          rw [hGtrue] at hGfalse
          cases hGfalse
        rcases Finset.one_lt_card.mp (by omega : 1 < (D'.leftVars z).card) with ⟨u1, hu1, u2, hu2, hune⟩
        rcases Finset.one_lt_card.mp (by omega : 1 < (D'.rightVars z).card) with ⟨v1, hv1, v2, hv2, hvne⟩
        exact hNoC4 u1 u2 v1 v2 hune hvne
          (hAllEdge u1 hu1 v1 hv1) (hAllEdge u1 hu1 v2 hv2)
          (hAllEdge u2 hu2 v1 hv1) (hAllEdge u2 hu2 v2 hv2)
    have hD_le : D.size ≤ k := hD_size
    exact hCorePG23 X D' hD'_wf hD'_out hD'_ge2 (by omega)
      hD'_sing hD'_disj hD'_disjX hD'_core hD'_pos hD'_neg