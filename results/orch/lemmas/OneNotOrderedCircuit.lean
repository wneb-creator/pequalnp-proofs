import MonotoneEighteen
import PositiveTailExtraction

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd

open PEqualNP.CircuitLowerBounds

def orderedPrefix (a b : Fin 10) : List Gate :=
  [{ op := .and, inputs := [a.val, b.val] }, { op := .not, inputs := [10] }]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma orderedPrefix_table : ∀ a b : Fin 10,
    execute (orderedPrefix a b) inputs =
      inputs ++ [andColumn a b, neg (andColumn a b)] := by
  decide +kernel

lemma output_member (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) :
    graph ∈ execute C.gates inputs := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal C.output r).trans
      ((congrFun computes (sample r)).trans (edge_table r).symm)
  simp only [List.getD_eq_getElem?_getD] at goalEq
  cases h : (execute C.gates inputs)[C.output]? with
  | none =>
    rw [h] at goalEq
    exact False.elim (graph_proper.1 goalEq.symm)
  | some z =>
    rw [h] at goalEq
    exact goalEq ▸ List.mem_of_getElem? h

lemma ordered_circuit_lower (a b : Fin 10) (ab : a ≠ b) (C : Circuit) (gs : List Gate)
    (gatesEq : C.gates = orderedPrefix a b ++ gs)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : ∀ g ∈ gs, isNot g = false)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) : 20 ≤ C.size := by
  have output := output_member C legal computes
  rw [gatesEq] at output
  have table : execute (orderedPrefix a b ++ gs) inputs =
      execute gs (inputs ++ [andColumn a b, neg (andColumn a b)]) := by
    simp only [execute, List.foldl_append]
    exact congrArg (fun w => execute gs w) (orderedPrefix_table a b)
  rw [table] at output
  obtain ⟨k, S, bound, run, sub⟩ := PositiveTail.positive_tail_extract gs
    (inputs ++ [andColumn a b, neg (andColumn a b)])
    (fun g hg => legal g (by rw [gatesEq]; exact List.mem_append_right _ hg))
    mono graph_proper output
  have subset : S ⊆ bank a b := by
    intro w hw
    have mem := sub w hw
    simpa [bank, List.mem_append, List.mem_cons, List.mem_singleton,
      or_assoc, or_left_comm, or_comm] using mem
  have lower := all_positive_tail_lower a b ab subset run
  have size : C.size = gs.length + 2 := by
    simp [Circuit.size, gatesEq, orderedPrefix]
  omega

lemma ordered_circuit_exclusion (a b : Fin 10) (ab : a ≠ b) (C : Circuit) (gs : List Gate)
    (gatesEq : C.gates = orderedPrefix a b ++ gs)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : ∀ g ∈ gs, isNot g = false)
    (small : C.size ≤ 19) :
    PEqualNP.MetaComplexity.circuitFun 10 C ≠ edge := by
  intro computes
  have lower := ordered_circuit_lower a b ab C gs gatesEq legal mono computes
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd
