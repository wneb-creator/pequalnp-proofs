import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.BankObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

-- This is a nonminimum circuit and does not refute the posted gap.
-- It witnesses the failure of a proposed factorization based only on local properties.

def G : SimpleGraph (Fin 7) where
  Adj a b :=
    (a.val = 5 ∧ (b.val = 0 ∨ b.val = 1 ∨ b.val = 3)) ∨
    (a.val = 6 ∧ (b.val = 0 ∨ b.val = 2 ∨ b.val = 4)) ∨
    (b.val = 5 ∧ (a.val = 0 ∨ a.val = 1 ∨ a.val = 3)) ∨
    (b.val = 6 ∧ (a.val = 0 ∨ a.val = 2 ∨ a.val = 4))
  symm := ⟨by intro a b; tauto⟩
  loopless := ⟨by intro a; omega⟩

instance : DecidableRel G.Adj := by unfold G; infer_instance

def C : Circuit where
  gates := [⟨GateOp.and, [6, 6]⟩, ⟨GateOp.and, [5, 5]⟩,
    ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.or, [14, 1]⟩, ⟨GateOp.or, [14, 2]⟩,
    ⟨GateOp.and, [5, 15]⟩, ⟨GateOp.and, [6, 16]⟩,
    ⟨GateOp.or, [17, 18]⟩]
  output := 19

def color (w : ℕ) : Bool := decide (w < 5)

def cut (D : Circuit) (j : ℕ) : Circuit :=
  { D with gates := D.gates.set j ⟨GateOp.or, []⟩ }

def retain (D : Circuit) (j : ℕ) (b : Fin 2) : Circuit :=
  { D with gates := D.gates.set j ⟨GateOp.or, [opnd D j b, opnd D j b]⟩ }

lemma graph_four_cycle_free : NoFourCycle G := by decide

lemma circuit_model : IsAO2 7 C := by decide

lemma circuit_zero : tCount 7 C color = 0 := by decide

lemma circuit_function : circuitFun 7 C = graphFun G ∅ := by decide

lemma circuit_top_form : TopForm G C := by decide

lemma all_gates_pivotal :
    ∀ j : Fin C.gates.length, ∃ u v : Fin 7, G.Adj u v ∧
      circuitFun 7 (cut C j) (pairInput u v) = false := by decide

lemma all_or_branches_essential :
    ∀ j : Fin C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ b : Fin 2, ∃ u v : Fin 7, G.Adj u v ∧
        circuitFun 7 (retain C j b) (pairInput u v) = false := by
  letI := gateOpDecEq
  decide

lemma exact_top_set : tops G C = {10, 11} := by decide
lemma exact_junk_set : junk G C = {0, 1, 4, 6} := by decide
lemma exact_lambda_set : lam G C = {8, 9} := by decide
lemma exact_outside_lambda : orN G C \ lam G C = {2, 3, 5, 7} := by decide
lemma edge_count : G.edgeFinset.card = 6 := by decide
lemma residual_count : (Ustar G C).card = 2 := by decide
lemma exact_size : C.size = 13 := by decide

def smaller : Circuit where
  gates := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [6, 11]⟩,
    ⟨GateOp.or, [9, 12]⟩]
  output := 13

lemma strictly_smaller_equivalent : IsAO2 7 smaller ∧ tCount 7 smaller color = 0 ∧
    circuitFun 7 smaller = graphFun G ∅ ∧ smaller.size = 7 ∧ smaller.size < C.size := by decide

end PEqualNP.Outside.L_meta_4675.BankObstruction
