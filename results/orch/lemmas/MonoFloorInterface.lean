import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113MonoFloor

open PEqualNP.Outside.L_meta_6581

lemma mono_floor_of_impossible
    (hMono : Impossible false graph 15 inputs.toFinset) : Lower false inputs graph 16 := by
  intro k bank path hit
  have plain : plainWord graph = true := by decide +kernel
  have init : inputs.all plainWord = true := by decide +kernel
  obtain ⟨j, S, hj, run, raw⟩ := reach_live graph_proper plain init path hit
  rw [orbitAllInputs run raw] at run
  by_contra! small
  exact hMono j (by omega) run

end PEqualNP.Outside.Pilot113MonoFloor
