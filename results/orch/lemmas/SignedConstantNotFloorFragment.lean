namespace PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.CircuitLowerBounds

lemma constant_not_prefix_floor (floor16 : Lower false inputs graph 16)
    (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (constant : Extended.constantNegations gs Extended.pins)
    (hit : Extended.target ∈ Extended.execute gs Extended.pins) :
    18 ≤ gs.countP (fun g => !Extended.isNot g) := by
  have hp : Extended.proper Extended.target := by unfold Extended.proper; decide +kernel
  have norm : Extended.nrm false = id := by funext a; rfl
  obtain ⟨k,S,hk,run,raw⟩ := Extended.extract_constant_not gs Extended.pins legal constant hp
    (by simpa only [norm, List.map_id_fun, id_eq] using hit)
  have raw' : ∀ a ∈ S, a ∈ Extended.pins := by simpa only [norm, List.map_id_fun, id_eq] using raw
  have floor := atLeastEighteenMono floor16 run raw'
  omega

end PEqualNP.Outside.L_meta_2592.Signed
