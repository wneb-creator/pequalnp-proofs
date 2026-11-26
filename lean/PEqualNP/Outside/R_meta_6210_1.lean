import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_6210_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x9 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x9)) x8;           have x9 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x9 : ℕ) => {x10 : Fin (13 : ℕ) × Fin (13 : ℕ) | x10.1 ∉ PEqualNP.HeptadCover.singerLines3 x10.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x10.1} {x10.2}) x9 = Bool.true};           (x9 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 → x8 x2 x13 = Bool.false ∨ x8 x3 x13 = Bool.false) → (∃ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 ∧ x8 x2 x14 = Bool.false ∧ x8 x3 x14 = Bool.true) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x8 x3 x15 = Bool.false ∧ x8 x2 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x9 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x9)) x8;           have x9 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x9 : ℕ) => {x10 : Fin (13 : ℕ) × Fin (13 : ℕ) | x10.1 ∉ PEqualNP.HeptadCover.singerLines3 x10.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x10.1} {x10.2}) x9 = Bool.true};           (x9 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 → x8 x2 x13 = Bool.false ∨ x8 x3 x13 = Bool.false) → (∃ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 ∧ x8 x2 x14 = Bool.false ∧ x8 x3 x14 = Bool.true) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x8 x3 x15 = Bool.false ∧ x8 x2 x15 = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x8 : ℕ) (x9 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x9 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x9)) x8;           have x9 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x9 : ℕ) => {x10 : Fin (13 : ℕ) × Fin (13 : ℕ) | x10.1 ∉ PEqualNP.HeptadCover.singerLines3 x10.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x10.1} {x10.2}) x9 = Bool.true};           (x9 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 → x8 x2 x13 = Bool.false ∨ x8 x3 x13 = Bool.false) → (∃ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 ∧ x8 x2 x14 = Bool.false ∧ x8 x3 x14 = Bool.true) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x8 x3 x15 = Bool.false ∧ x8 x2 x15 = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intros x1 x2 x3 h1 h2 h3 h4 L1 L2 h5 h6 h7 h8 h9 h10
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
  · exact lastAnd x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hand
  · exact lastOr x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 har
