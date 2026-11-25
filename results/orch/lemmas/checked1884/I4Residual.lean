import I4Geometry
import ProfileThree

namespace PEqualNP.Outside.L_meta_1884_aux.I4Residual

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_1884_aux.I4Bridge
open PEqualNP.Outside.L_meta_1884_aux.I4Geometry

theorem residual_exactly_three {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) (hsize : D.length ≤ 18)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b) :
    (residualUnits 10 D b).card = 3 ∧ Bzero 10 D = 0 := by
  classical
  have hE := eligibility hI
  have hne := profile_nonempty h hD hI b hb
  have hbudget (c : Fin 10) (hc : c ∈ E) :
      ((E.filter fun x => profile D b x ⊆ profile D b c).biUnion neighbors).card ≤
        (profile D b c).card + 1 := by
    obtain ⟨y, hy, hcy⟩ := finite_geometry.2.2.2.2 c hc
    obtain ⟨pos, hpos⟩ := k4_assigned sem_petersen_gr h hD
    have hh := center_budget h hD b hb hpos hne (hE ▸ hc) (hE ▸ hy) hcy
    rw [centers_biUnion hI b c] at hh
    exact hh
  have hR := ProfileThree.at_least_three E neighbors (profile D b) (residualUnits 10 D b)
    (by rw [finite_geometry.1]; omega)
    (by rw [finite_geometry.2.2.1])
    finite_geometry.2.2.2.1
    (fun x hx => hne x (hE ▸ hx))
    (fun _ _ => Finset.filter_subset _ _) hbudget
  have hcount := card_residual h.1 b hb
  rw [hE, finite_geometry.1] at hcount
  have htotal := surplus_identity h
  rw [totalSurplus_split] at htotal
  omega

end PEqualNP.Outside.L_meta_1884_aux.I4Residual
