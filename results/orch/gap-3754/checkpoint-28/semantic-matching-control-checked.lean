import PEqualNP.Defs

-- Exact transcription of the reviewed cadical-matching4-control.model.json.
-- This seven-gate circuit is a positive control, and is not a least circuit.
namespace PEqualNP.Outside.L_meta_3754.MatchingControl
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

def graph : SimpleGraph (Fin 4) := edgeGraph 4 [(0,1),(2,3)]

instance : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

def candidate : Circuit := ⟨[
  ⟨GateOp.or,[0,2]⟩,
  ⟨GateOp.or,[0,3]⟩,
  ⟨GateOp.or,[1,2]⟩,
  ⟨GateOp.or,[1,3]⟩,
  ⟨GateOp.and,[4,6]⟩,
  ⟨GateOp.and,[5,8]⟩,
  ⟨GateOp.and,[7,9]⟩],10⟩

def witness4 (v : Fin 4) : Bool := decide (v.val=2)
def witness5 (v : Fin 4) : Bool := decide (v.val=0 ∨ v.val=2)

lemma candidate_ao2 : IsAO2 4 candidate := by decide +kernel
lemma candidate_size : candidate.size=7 := by decide +kernel

lemma candidate_semantics : circuitFun 4 candidate=graphFun graph ∅ := by
  have h : ∀x : Fin 4 → Bool,circuitFun 4 candidate x=graphFun graph ∅ x := by
    decide +kernel
  exact funext h

set_option maxRecDepth 100000 in
lemma candidate_fixed : IsLiftFixedPoint graph candidate := by decide +kernel

lemma candidate_gate4_witness :
    4<candidate.gates.length ∧ (gateAt candidate 4).op=GateOp.and ∧
    gateVal 4 candidate 4 witness4=true ∧ graphFun graph ∅ witness4=false := by
  refine ⟨by decide,rfl,?_⟩
  decide +kernel

lemma candidate_gate5_witness :
    5<candidate.gates.length ∧ (gateAt candidate 5).op=GateOp.and ∧
    gateVal 4 candidate 5 witness5=true ∧ graphFun graph ∅ witness5=false := by
  refine ⟨by decide,rfl,?_⟩
  decide +kernel

lemma candidate_gate4_dirty : ¬BelowF graph candidate 4 := by
  intro h
  have hh := h witness4 candidate_gate4_witness.2.2.1
  rw [candidate_gate4_witness.2.2.2] at hh
  exact Bool.false_ne_true hh

lemma candidate_gate5_dirty : ¬BelowF graph candidate 5 := by
  intro h
  have hh := h witness5 candidate_gate5_witness.2.2.1
  rw [candidate_gate5_witness.2.2.2] at hh
  exact Bool.false_ne_true hh

lemma graph_no_four : NoFourCycle graph := by decide +kernel

def color (v : Fin 4) : Bool := decide (v.val%2=1)
lemma graph_bipartite : ∀u v,graph.Adj u v → color u≠color v := by decide +kernel

-- A separate three-gate implementation certifies the positive control is nonminimum.
def clean : Circuit := ⟨[
  ⟨GateOp.and,[0,1]⟩,
  ⟨GateOp.and,[2,3]⟩,
  ⟨GateOp.or,[4,5]⟩],6⟩

lemma clean_ao2 : IsAO2 4 clean := by decide +kernel
lemma clean_size : clean.size=3 := by decide +kernel
lemma clean_semantics : circuitFun 4 clean=graphFun graph ∅ := by
  have h : ∀x : Fin 4 → Bool,circuitFun 4 clean x=graphFun graph ∅ x := by
    decide +kernel
  exact funext h

lemma candidate_not_least : ¬IsLeastAO graph candidate := by
  intro h
  have hh := h.2.2 clean clean_ao2 clean_semantics
  rw [candidate_size,clean_size] at hh
  omega

end PEqualNP.Outside.L_meta_3754.MatchingControl
