import I4Residual
import ProfileEncodingDefs
import ProfileCertificateAnalytic

namespace PEqualNP.Outside.L_meta_1884_aux.I4Finish

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_1884_aux.I4Bridge
open PEqualNP.Outside.L_meta_1884_aux.I4Geometry

theorem edge_table : ∀ i : Fin 4, ∀ e : Fin 6,
    Adj (center i) (vertex e) ↔ i ∈ ProfileCertificate.endpoints e := by
  unfold Adj
  decide +kernel

theorem center_code {D : Dag} (hI : ineligSet 10 D = I)
    (b : Fin 10 → Nat) (f : Fin 6 → Fin 7)
    (hsub : ∀ e d, ProfileCertificate.profile f e ⊆ ProfileCertificate.profile f d ↔
      profile D b (vertex e) ⊆ profile D b (vertex d)) (c : Fin 6) :
    (centers D b (vertex c)).card = (ProfileCertificate.dominated f c).card := by
  classical
  have hset : centers D b (vertex c) = (ProfileCertificate.dominated f c).image center := by
    ext i
    constructor
    · intro hi
      obtain ⟨hi, x, hx, hp, hix⟩ := Finset.mem_filter.mp hi
      obtain ⟨a, rfl⟩ := (center_bijection.2 i).mp (hI ▸ hi)
      obtain ⟨e, rfl⟩ := (vertex_bijection.2 x).mp (eligibility hI ▸ hx)
      refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hsub e c).mpr hp⟩, (edge_table a e).mp hix⟩
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ha
      have hp := (Finset.mem_filter.mp he).2
      refine Finset.mem_filter.mpr ⟨?_, vertex e, ?_, (hsub e c).mp hp,
        (edge_table a e).mpr hae⟩
      · rw [hI]
        exact (center_bijection.2 _).mpr ⟨a, rfl⟩
      · rw [eligibility hI]
        exact (vertex_bijection.2 _).mpr ⟨e, rfl⟩
  rw [hset]
  exact Finset.card_image_of_injOn (fun a _ b _ hab => center_bijection.1 hab)

theorem four_orbit_impossible {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) (hsize : D.length ≤ 18)
    (hI : ineligSet 10 D = I) : False := by
  classical
  obtain ⟨b, hb⟩ := sem_exists_pureBranch sem_petersen_gr h.1 hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_petersen_gr h hD
  have hE := eligibility hI
  have hne := profile_nonempty h hD hI b hb
  have hv (e : Fin 6) : vertex e ∈ eligSet 10 D := by
    rw [hE]
    exact (vertex_bijection.2 _).mpr ⟨e, rfl⟩
  obtain ⟨hR, hz⟩ := I4Residual.residual_exactly_three h hD hsize hI b hb
  obtain ⟨f, hcard, hsub⟩ := ProfileEncoding.encode_profiles (residualUnits 10 D b) hR
    (fun e => profile D b (vertex e))
    (fun _ => Finset.filter_subset _ _) (fun e => hne _ (hv e))
  change ∀ e, (ProfileCertificate.profile f e).card = (profile D b (vertex e)).card at hcard
  change ∀ e d, ProfileCertificate.profile f e ⊆ ProfileCertificate.profile f d ↔
    profile D b (vertex e) ⊆ profile D b (vertex d) at hsub
  have hcc := center_code hI b f hsub
  have budget (c : Fin 6) :
      (ProfileCertificate.dominated f c).card ≤ (ProfileCertificate.profile f c).card + 1 := by
    obtain ⟨y, hy, hcy⟩ := finite_geometry.2.2.2.2 (vertex c) (hE ▸ hv c)
    rw [← hcc c, hcard c]
    exact center_budget h hD b hb hpos hne (hv c) (hE ▸ hy) hcy
  obtain ⟨v, x, c, hsat, hinc, i, hiv, hix, hic⟩ := ProfileCertificate.closure f budget
  have hsat' : (centers D b (vertex v)).card = (profile D b (vertex v)).card + 1 := by
    rw [hcc v, hsat, hcard v]
  have hi : center i ∈ ineligSet 10 D := by
    rw [hI]
    exact (center_bijection.2 _).mpr ⟨i, rfl⟩
  obtain ⟨y, hy, hvy⟩ := finite_geometry.2.2.2.2 (vertex v) (hE ▸ hv v)
  exact I4Full.inclusion_conflict h hD b hb hpos hne hz
    (hv v) (hE ▸ hy) hvy (hv x) (hv c) hi
    ((edge_table i v).mpr hiv) ((edge_table i x).mpr hix)
    (fun h => hic ((edge_table i c).mp h)) hsat' ((hsub x c).mp hinc)

end PEqualNP.Outside.L_meta_1884_aux.I4Finish
