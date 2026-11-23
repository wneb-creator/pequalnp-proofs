import Compressed1007
import Batteries.Tactic.OpenPrivate

open private necessary from Compressed1007

namespace PEqualNP.Outside.L_meta_670_aux.Base1007

lemma noSmallSubset {m t : Nat} {T : Finset Sig} (hm : m ≤ 12)
    (hT : T ⊆ raw.toFinset) : ¬ Live m t T := by
  intro h
  have he := necessary h (fun a ha => List.mem_toFinset.mp (hT ha))
  rw [← he] at h
  exact noSmallLive hm h

lemma noThetaSubset (i : Fin 4) {m t : Nat} {T : Finset Sig} (hm : m ≤ 10)
    (hT : T ⊆ (raw.map (project i)).toFinset) : ¬ Live m t T := by
  intro h
  apply root_project_impossible i
  refine ⟨m, hm, t, T, h, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hT ha))
  exact Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb, rfl⟩

end PEqualNP.Outside.L_meta_670_aux.Base1007

#print axioms PEqualNP.Outside.L_meta_670_aux.Base1007.noSmallSubset
#print axioms PEqualNP.Outside.L_meta_670_aux.Base1007.noThetaSubset
#print axioms PEqualNP.Outside.L_meta_670_aux.Base1007.noSmallLive
