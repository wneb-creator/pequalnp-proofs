import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_71
    (hEdgesAll : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq;
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or)).card + (PEqualNP.Core.maximalCores G C).card)
    (hCoverAll : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover
        (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)) : Set (Sym2 (Fin n)))) T' →
      letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq;
      T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and)).card + T'.card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G inst C s T T' hBip hFour hAO hEval hFixed hT hT'
  let : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
    PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hEdges := hEdgesAll n G C s hBip hFour hAO hEval hFixed
  have hCover := hCoverAll n G C s T T' hBip hFour hAO hEval hFixed hT hT'
  let U := (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)
  have sub : U ⊆ Finset.range C.gates.length := by
    intro g hg
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
    rcases Finset.mem_insert.mp hgj with h | h
    · subst g
      exact (Finset.mem_filter.mp hj).1
    · exact (Finset.mem_filter.mp h).1
  have hop : ∀ j ∈ U,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    have hjl := Finset.mem_range.mp (sub hj)
    have gate_eq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hjl]
    rw [gate_eq]
    exact hAO.1 _ (List.getElem_mem hjl)
  have filter_eq :
      U.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.or) =
      U.filter (fun j => ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hor⟩
      exact ⟨hj, by simp [hor]⟩
    · rintro ⟨hj, hnand⟩
      exact ⟨hj, (hop j hj).resolve_left hnand⟩
  have partition :
      (U.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and)).card +
      (U.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.or)).card = U.card := by
    rw [filter_eq]
    exact Finset.card_filter_add_card_filter_not _
  change ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤
    (U.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.or)).card + (PEqualNP.Core.maximalCores G C).card at hEdges
  change T.card ≤ (U.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
    PEqualNP.CircuitLowerBounds.GateOp.and)).card + T'.card at hCover
  change ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
    U.card + (PEqualNP.Core.maximalCores G C).card + T'.card
  omega
