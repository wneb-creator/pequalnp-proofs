import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_670_aux_notzero (C : Circuit)
    (hfan : FanInTwo C) (hz : PEqualNP.NotBracket.notCount C = 0) : Monotone2 C := by
  classical
  intro g hg
  obtain ⟨hop, hlen⟩ := hfan g hg
  refine ⟨?_, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with hop | hop | hop
  · exact Or.inl hop
  · exact Or.inr hop
  · have hmem : g ∈ C.gates.filter (fun v => @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) := by
      simp [List.mem_filter, hg, hop]
    have hnil : C.gates.filter (fun v => @decide (v.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) = [] :=
      List.eq_nil_of_length_eq_zero hz
    rw [hnil] at hmem
    exact (List.not_mem_nil hmem).elim

theorem PEqualNP.Outside.L_meta_670_aux_countsplit (C : Circuit) :
    (C.gates.filter (fun g => @decide (g.op ≠ GateOp.not) (Classical.propDecidable _))).length +
      PEqualNP.NotBracket.notCount C = C.size := by
  classical
  unfold PEqualNP.NotBracket.notCount Circuit.size
  generalize C.gates = gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases h : g.op = GateOp.not
    · simp [h] at *
      omega
    · simp [h] at *
      omega
