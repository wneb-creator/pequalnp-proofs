import RectangleRun
import RectangleOrEdge

namespace PEqualNP.Outside.L_meta_2373.RectangleOrEdgeRun

open Live1024

def basis (i : Fin 11) : Sig :=
  Fin.lastCases (bin 1 (inputs.getD 0 zero) (inputs.getD 1 zero))
    (fun j : Fin 10 => inputs.getD j.val zero) i

def positiveRows (r : Fin 15) : Row := Fin.ofNat 1024 (RectangleOrEdge.positiveRows r)
def negativeRows (r : Fin 15) : Row := Fin.ofNat 1024 (RectangleOrEdge.negativeRows r)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_inputs : ∀ (r : Fin 15) (i : Fin 11),
    observe (basis i) (positiveRows r) = RectangleOrEdge.positiveSample r i := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_inputs : ∀ (r : Fin 15) (i : Fin 11),
    observe (basis i) (negativeRows r) = RectangleOrEdge.negativeSample r i := by
  decide +kernel

lemma prefix_bound (i : Fin 11) : RectangleRun.Bounds positiveRows negativeRows
    RectangleOrEdge.weight (observe (basis i)) 4 := by
  intro S T hs ht
  apply RectangleOrEdge.leaf_bound i S T
  · intro r hr
    rw [← positive_inputs]
    exact hs r hr
  · intro c hc
    rw [← negative_inputs]
    exact ht c hc

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_graph : ∀ r, observe graph (positiveRows r) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_graph : ∀ r, observe graph (negativeRows r) = false := by decide +kernel

lemma tight_prefix_exclusion (roots : List Sig) (k : Nat)
    (trace : Run false (observe graph) k (roots.map observe))
    (tight : roots.length = k + 1) (small : roots.length ≤ 19)
    (raw : ∀ v ∈ roots, ∃ i : Fin 11, basis i = v) : False := by
  have bound := RectangleRun.tight_run_uniform positiveRows negativeRows RectangleOrEdge.weight
    trace (by simpa using tight) (cap := 4)
    (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      obtain ⟨i, rfl⟩ := raw a ha
      exact prefix_bound i) positive_graph negative_graph
  change RectangleOrEdge.rect Finset.univ Finset.univ ≤ _ at bound
  rw [RectangleOrEdge.full_weight, List.length_map] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleOrEdgeRun
