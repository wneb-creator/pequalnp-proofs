import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_7977_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;           have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;           have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});           (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) → (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) → (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) → (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).inputs, (26 : ℕ) ≤ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x18 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;           have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;           have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});           (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) → (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) → (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) → (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).inputs, (26 : ℕ) ≤ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x18 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;           have x9 : ℕ → List Bool → Prop := fun (x9 : ℕ) (x10 : List Bool) => ∃ x11 < x1.size, PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x9 x11 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue x1 x10 ((26 : ℕ) + x11) = Bool.true;           have x10 : ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 : ℕ) (x11 x12 : Fin (13 : ℕ)) => x9 x10 (PEqualNP.GenericRejection.incidenceInput {x11} {x12});           (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x8 x12 → x10 x2 x11 x12 ∨ x10 x3 x11 x12) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x8 x12 → ¬(x9 x2 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)) ∨ x9 x3 (PEqualNP.GenericRejection.incidenceInput x12 (PEqualNP.HeptadCover.missLines x8 x12)))) → (∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x8 x14 ∧ x10 x2 x13 x14 ∧ ¬x10 x3 x13 x14) → (∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x8 x15 ∧ x10 x3 x14 x15 ∧ ¬x10 x2 x14 x15) → (∃ (x15 : Finset ℕ), x15.card = (3 : ℕ) ∧ ∀ x16 ∈ x15, x16 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x16).inputs, (26 : ℕ) ≤ x18 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x18 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size := by
  intros x1 x2 x3 h1 h2 h3 h4 L1 L2 L3 h5 h6 h7 h8 h9
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x1.size = x1.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x1.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x1.gates (x1.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x1.size - (1 : ℕ) < x1.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = x1.gates[x1.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 hand
  · exact lastOr x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 har
