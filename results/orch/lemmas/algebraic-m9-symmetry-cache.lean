import PNPAccepted6659
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux

noncomputable def equality_missing_cap (D : Dag) : Finset (Fin 14) := by
  classical
  exact ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))

theorem equality_occurrence_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    {D : Dag} (h : Strict n D) (P M : Finset (Fin n)) :
    sup_Occ n (relabel σ D) (P.image σ) (M.image σ) ↔ sup_Occ n D P M := by
  classical
  constructor
  · rintro ⟨w,hw⟩
    let v := liftP σ.symm w
    refine ⟨v,Finset.image_injective σ.injective ?_⟩
    rw [Finset.image_inter _ _ σ.injective,← relabel_supp σ h v]
    have inv : liftP σ v = w := tr_liftP_inv' σ w
    rw [inv]
    exact hw
  · rintro ⟨w,hw⟩
    refine ⟨liftP σ w,?_⟩
    rw [relabel_supp σ h w,← Finset.image_inter _ _ σ.injective,hw]

def equality_m9_pair (k : Fin 6) : Finset (Fin 14) := ![{0,1},{0,2},{0,5},{1,2},{1,5},{2,5}] k

def equality_m9_permutation (k : Fin 6) : Fin 14 → Fin 14 :=
  ![hc_ofList [2,5,0,3,4,1,6,12,8,9,13,11,7,10],
    hc_ofList [5,1,2,6,4,0,3,9,12,7,10,11,8,13],
    hc_ofList [2,1,0,4,3,5,6,13,8,9,12,11,10,7],
    hc_ofList [0,5,2,4,3,1,6,10,8,9,7,11,13,12],
    hc_ofList [0,2,1,6,4,5,3,8,7,12,10,11,9,13],
    hc_ofList [0,1,2,3,4,5,6,7,8,9,10,11,12,13]] k

def equality_m9_automorphism (k : Fin 6) : Equiv.Perm (Fin 14) :=
  ⟨equality_m9_permutation k,equality_m9_permutation k,
    by intro i; revert i k; decide +kernel,
    by intro i; revert i k; decide +kernel⟩

theorem equality_m9_automorphism_aut (k : Fin 6) : IsAut (equality_m9_automorphism k) := by
  apply hc_isAut_of
  revert k
  decide +kernel

theorem equality_m9_automorphism_geometry : ∀ k : Fin 6,
    ({0,1,2,5} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5} ∧
    ({0,1,2,5,11} : Finset (Fin 14)).image (equality_m9_automorphism k) = {0,1,2,5,11} ∧
    mx_L.image (equality_m9_automorphism k) = mx_L ∧
    (equality_m9_pair k).image (equality_m9_automorphism k) = {2,5} ∧
    ∀ i : Fin 14, (sem_hw_nb i).image (equality_m9_automorphism k) =
      sem_hw_nb (equality_m9_automorphism k i) := by
  decide +kernel

theorem equality_m9_missing_relabel {D : Dag} (h : Strict 14 D) (k : Fin 6) :
    equality_missing_cap (relabel (equality_m9_automorphism k) D) =
      (equality_missing_cap D).image (equality_m9_automorphism k) := by
  classical
  let σ := equality_m9_automorphism k
  have geo := equality_m9_automorphism_geometry k
  have member (i : Fin 14) : σ i ∈ ({0,1,2,5} : Finset (Fin 14)) ↔
      i ∈ ({0,1,2,5} : Finset (Fin 14)) := by
    constructor
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ := by
        rw [geo.1]
        exact hi
      obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 im
      exact σ.injective equal ▸ hj
    · intro hi
      have im : σ i ∈ ({0,1,2,5} : Finset (Fin 14)).image σ :=
        Finset.mem_image.2 ⟨i,hi,rfl⟩
      rwa [geo.1] at im
  have transfer (i : Fin 14) :
      σ i ∈ equality_missing_cap (relabel σ D) ↔ i ∈ equality_missing_cap D := by
    have occurrence := equality_occurrence_relabel σ h mx_L (sem_hw_nb i)
    rw [geo.2.2.1,geo.2.2.2.2 i] at occurrence
    simp only [equality_missing_cap,Finset.mem_filter]
    exact and_congr (member i) (not_congr occurrence)
  ext j
  constructor
  · intro hj
    refine Finset.mem_image.2 ⟨σ.symm j,?_,σ.apply_symm_apply j⟩
    apply (transfer (σ.symm j)).1
    simpa only [Equiv.apply_symm_apply] using hj
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hj
    exact (transfer i).2 hi

theorem equality_m9_any_two_missing_of_canonical
    (canonical : ∀ {D : Dag}, StrictLive 14 D → Correct D → totalSurplus 14 D ≤ 14 →
      ineligSet 14 D = {0,1,2,5,11} → equality_missing_cap D = {2,5} → False)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (two : (equality_missing_cap D).card = 2) : False := by
  classical
  have sub : equality_missing_cap D ⊆ ({0,1,2,5} : Finset (Fin 14)) := Finset.filter_subset _ _
  have shapes : ∀ M : Finset (Fin 14), M ⊆ ({0,1,2,5} : Finset (Fin 14)) →
      M.card = 2 → ∃ k : Fin 6, M = equality_m9_pair k := by
    have enumeration : ({0,1,2,5} : Finset (Fin 14)).powersetCard 2 =
        Finset.univ.image equality_m9_pair := by decide +kernel
    intro M subset card
    have member := Finset.mem_powersetCard.2 ⟨subset,card⟩
    rw [enumeration] at member
    obtain ⟨k,_,equal⟩ := Finset.mem_image.1 member
    exact ⟨k,equal.symm⟩
  obtain ⟨k,hM⟩ := shapes _ sub two
  obtain ⟨h',hD',_,total,_,_,_,ineligible⟩ :=
    heawood_relabel (equality_m9_automorphism k) (equality_m9_automorphism_aut k) h hD
  apply canonical h' hD'
    (by rw [total]; exact h14)
  · rw [ineligible,hI]
    exact (equality_m9_automorphism_geometry k).2.1
  · rw [equality_m9_missing_relabel h.1 k,hM]
    exact (equality_m9_automorphism_geometry k).2.2.2.1

end PEqualNP.Outside.L_meta_6659_aux
