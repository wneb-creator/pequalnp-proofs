import FoundationI0I3I4Audit
import I2Standalone
import N0CompleteAudit

namespace PEqualNP.Outside.L_meta_2590_aux.RemainingI1

open DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
lemma i2_graph_iff : ∀ u v, DeskDriver.adj u v ↔ I2Standalone.adj u v := by
  unfold DeskDriver.adj I2Standalone.adj
  decide +kernel

lemma i2_graph_agreement : DeskDriver.adj = I2Standalone.adj := by
  funext u v
  exact propext (i2_graph_iff u v)

lemma n0_graph_agreement : DeskDriver.adj = N0Standalone.N0Exclusive.Adj := rfl

lemma two_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (hlen : D.length ≤ 19)
    (hi : (ineligSet 10 D).card = 2) : False := by
  apply I2Standalone.petersen_two_ineligible_exclusion h _ hlen hi
  change sem_Comp 10 I2Standalone.adj D
  simpa only [← i2_graph_agreement] using hc

lemma neighborhood_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (hlen : D.length ≤ 19)
    (hi : ineligSet 10 D = ({1, 4, 5} : Finset (Fin 10))) : False := by
  apply N0Standalone.N0Closed.neighborhood_ineligible_impossible h _ hi hlen
  change sem_Comp 10 N0Standalone.N0Exclusive.Adj D
  simpa only [← n0_graph_agreement] using hc

lemma circuit_remaining_one (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ D : Dag, StrictLive 10 D ∧ sem_Comp 10 DeskDriver.adj D ∧ D.length ≤ 19 ∧
      (ineligSet 10 D).card = 1 := by
  obtain ⟨D, hD, hc, hlen, hcases⟩ := FoundationI0.circuit_remaining_cases C hm hs hf
  refine ⟨D, hD, hc, hlen, ?_⟩
  rcases hcases with hi | hi | hi
  · exact hi
  · exact (two_ineligible_impossible hD hc hlen hi).elim
  · exact (neighborhood_ineligible_impossible hD hc hlen hi).elim

end PEqualNP.Outside.L_meta_2590_aux.RemainingI1
