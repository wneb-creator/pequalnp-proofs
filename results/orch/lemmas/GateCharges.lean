import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm

lemma core_union_subset_range {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) :
    (maximalCores G C).biUnion (coneSet n C) ⊆ Finset.range C.gates.length := by
  intro g hg
  obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
  rcases Finset.mem_insert.mp hgj with h | h
  · subst g
    exact (Finset.mem_filter.mp hj).1
  · exact (Finset.mem_filter.mp h).1

lemma core_union_gate_partition {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) [DecidableEq GateOp] (hC : IsAO2 n C) :
    (((maximalCores G C).biUnion (coneSet n C)).filter
      (fun j => (gateAt C j).op = GateOp.and)).card +
    (((maximalCores G C).biUnion (coneSet n C)).filter
      (fun j => (gateAt C j).op = GateOp.or)).card =
    ((maximalCores G C).biUnion (coneSet n C)).card := by
  classical
  let U := (maximalCores G C).biUnion (coneSet n C)
  have hop : ∀ j ∈ U, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    intro j hj
    have hjl := Finset.mem_range.mp (core_union_subset_range G C hj)
    have gate_eq : gateAt C j = C.gates[j] := by
      simp [gateAt, List.getD_eq_getElem?_getD, hjl]
    rw [gate_eq]
    exact hC.1 _ (List.getElem_mem hjl)
  have filter_eq : U.filter (fun j => (gateAt C j).op = GateOp.or) =
      U.filter (fun j => ¬ (gateAt C j).op = GateOp.and) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hor⟩
      exact ⟨hj, by simp [hor]⟩
    · rintro ⟨hj, hnand⟩
      exact ⟨hj, (hop j hj).resolve_left hnand⟩
  change (U.filter (fun j => (gateAt C j).op = GateOp.and)).card +
    (U.filter (fun j => (gateAt C j).op = GateOp.or)).card = U.card
  rw [filter_eq]
  exact Finset.card_filter_add_card_filter_not _

lemma core_cover_of_gate_charges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) [DecidableEq GateOp] (T T' : Finset (Fin n))
    (hC : IsAO2 n C)
    (hEdges : ((maximalCores G C).biUnion (gammaE G C)).card ≤
      (((maximalCores G C).biUnion (coneSet n C)).filter
        (fun j => (gateAt C j).op = GateOp.or)).card + (maximalCores G C).card)
    (hCover : T.card ≤
      (((maximalCores G C).biUnion (coneSet n C)).filter
        (fun j => (gateAt C j).op = GateOp.and)).card + T'.card) :
    ((maximalCores G C).biUnion (gammaE G C)).card + T.card ≤
      ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card + T'.card := by
  have partition := core_union_gate_partition G C hC
  omega

end PEqualNP.Outside.L_meta_2962_aux
