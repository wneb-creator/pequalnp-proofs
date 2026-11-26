import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_7971_1
    (lastAnd :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x5.size)
    (lastOr :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x5.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (63 : ℕ) ≤ x5.size := by
  intros L1 L2 L3 L4 x5 x6 x7 h1 h2 h3 h4 h5 h6
  have hop : ∀ g ∈ x5.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x5.size = x5.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x5.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x5.gates (x5.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x5.size - (1 : ℕ) < x5.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x5.size - (1 : ℕ))
          = x5.gates[x5.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x5 x6 x7 h1 h2 h3 h4 h5 h6 hand
  · exact lastOr x5 x6 x7 h1 h2 h3 h4 h5 h6 har
