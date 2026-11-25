import PackingOrbitsDefs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingOrbits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairEnds_compat : ∀ i : Fin 325,
    pairEnds i = PackingThree.endpoints ⟨26 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_pair_seeds : ∀ r : Fin 27,
    PackingThree.rootIndices ⟨r.val, by omega⟩ =
      [26 + (roots.getD r.val (0, 0)).1.val, 26 + (roots.getD r.val (0, 0)).2.val] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_pair_seeds : ∀ r : Fin 3,
    PackingThree.rootIndices ⟨27 + r.val, by omega⟩ =
      [26 + (pairRoots.getD r.val 0).val] := by
  decide +kernel

lemma singleton_seed : PackingThree.rootIndices 30 = [0] := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.PackingOrbits
