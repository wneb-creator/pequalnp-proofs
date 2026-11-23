import ClosedDomains12Test

namespace PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thetaInitial_eq :
    (CachedProjection.thetaRaw ++ [Base1007.zero]).toFinset =
      (Base1007.raw.map (Base1007.project 0)).toFinset := by
  decide +kernel

lemma oracles_sound_from_base
    (hsmall : ∀ m ≤ 12, ∀ t T, T ⊆ Base1007.raw.toFinset → ¬ Base1007.Live m t T)
    (htheta : ∀ m ≤ 10, ∀ t T,
      T ⊆ (Base1007.raw.map (Base1007.project 0)).toFinset → ¬ Base1007.Live m t T)
    (q : Fin 12) : (oracles q).Sound := by
  have hb : ∀ i : Fin 12, ∀ m ≤ ProjectionDomains.budget i, ∀ t T,
      T ⊆ (initial i).toFinset → ¬ Base1007.Live m t T := by
    intro i m hm t T hT
    by_cases hi : i.val < 3
    · apply hsmall m (by simpa only [ProjectionDomains.budget, ite_eq_left hi] using hm) t T
      simpa only [initial, ite_eq_left hi] using hT
    · apply htheta m (by simpa only [ProjectionDomains.budget, ite_eq_right hi] using hm) t T
      simpa only [initial, ite_eq_right hi, thetaInitial_eq] using hT
  exact @oracles_sound hb q

end PEqualNP.Outside.L_meta_670_aux.ClosedDomains12

#print axioms PEqualNP.Outside.L_meta_670_aux.ClosedDomains12.oracles_sound_from_base
