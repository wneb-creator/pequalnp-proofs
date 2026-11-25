namespace PEqualNP.Outside.L_meta_6659_aux

def q2f_line_embed (i : Fin 7) : Fin 14 := Fin.natAdd 7 i
def q2f_point (i : Fin 3) : Fin 7 := ![0,1,3] i

lemma q2f_line_geometry :
    Function.Injective q2f_line_embed ∧
    Finset.univ.image q2f_line_embed = sem_hw_opp 0 ∧
    q2f_missingTriple.image q2f_line_embed = sem_hw_nb (os_pt 2) ∧
    ∀ i : Fin 3, (q2f_triple i).image q2f_line_embed = sem_hw_nb (os_pt (q2f_point i)) ∧
      os_pt (q2f_point i) ∈ ({0,1,3} : Finset (Fin 14)) := by
  decide +kernel

lemma q2f_circuit_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6}) :
    ∃ S : Finset (Fin 7), q2f_missingTriple ⊂ S ∧
      ∃ s : Fin 15, ∃ a b c : Fin 10, cap7_decode (q2f_superCode s) = S ∧
      ∀ m ∈ q2f_codes s a b c,
        sup_Occ 14 D (sem_hw_opp 0) ((cap7_decode m).image q2f_line_embed) ∧
        2 ≤ (cap7_decode m).card ∧
        ((cap7_decode m).card = 2 → ∃ i : Fin 3, cap7_decode m ⊆ q2f_triple i) := by
  classical
  let P := sem_hw_opp 0
  let f := q2f_line_embed
  let Q := fun M : Finset (Fin 7) => sup_Occ 14 D P (M.image f)
  have inj := q2f_line_geometry.1
  have range := q2f_line_geometry.2.1
  have base (i : Fin 3) : Q (q2f_triple i) := by
    change sup_Occ 14 D P ((q2f_triple i).image f)
    rw [(q2f_line_geometry.2.2.2 i).1]
    by_contra absent
    have member : q2f_point i ∈ equality_missing_points D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,absent⟩
    rw [hM] at member
    exact (by decide +kernel : ∀ i : Fin 3,
      q2f_point i ∉ ({2,4,5,6} : Finset (Fin 7))) i member
  have parents (i : Fin 3) : q2f_Parent Q (q2f_triple i) := by
    change equality_mask_parent Q (q2f_triple i)
    exact equality_occurring_parent_pull h.1 f inj P range _ (q2f_triple_card i) (base i)
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hi : os_pt 2 ∈ ineligSet 14 D := by rw [hI]; decide
  let A := supp 14 D (src D (pos (os_pt 2))) ∩ P
  have hA : sup_Occ 14 D P A := ⟨src D (pos (os_pt 2)),rfl⟩
  have neighbors : sem_hw_nb (os_pt 2) ⊆ A := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(hpos.1 (os_pt 2) hi).2.2.1 x (hw_mem_nb.mp hx),os_nb_sub 2 hx⟩
  have absent : ¬ sup_Occ 14 D P (sem_hw_nb (os_pt 2)) := by
    have hm : (2 : Fin 7) ∈ equality_missing_points D := by rw [hM]; decide
    exact (Finset.mem_filter.mp hm).2
  let S := equality_mask_pull f A
  have back : S.image f = A := equality_mask_pull_image f P range (sup_occ_sub hA)
  have strict : q2f_missingTriple ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · apply (Finset.image_subset_image_iff inj).mp
      rw [q2f_line_geometry.2.2.1,back]
      exact neighbors
    · intro equal
      apply absent
      rw [← q2f_line_geometry.2.2.1,equal,back]
      exact hA
  have hS : Q S := by change sup_Occ 14 D P (S.image f); rwa [back]
  obtain ⟨s,a,b,c,eq,good⟩ := q2f_choose_family Q base parents S strict hS
  exact ⟨S,strict,s,a,b,c,eq,good⟩

lemma q2f_image_good {D : Dag} (C : Finset (Fin 128))
    (good : ∀ m ∈ C,
      sup_Occ 14 D (sem_hw_opp 0) ((cap7_decode m).image q2f_line_embed) ∧
      2 ≤ (cap7_decode m).card ∧
      ((cap7_decode m).card = 2 → ∃ i : Fin 3, cap7_decode m ⊆ q2f_triple i)) :
    ∀ M ∈ C.image (fun m => (cap7_decode m).image q2f_line_embed),
      sup_Occ 14 D (sem_hw_opp 0) M ∧ 2 ≤ M.card ∧
      (M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i) := by
  classical
  intro M hMY
  obtain ⟨m,hmC,rfl⟩ := Finset.mem_image.mp hMY
  have gm := good m hmC
  refine ⟨gm.1,?_,?_⟩
  · rw [Finset.card_image_of_injective _ q2f_line_geometry.1]
    exact gm.2.1
  · intro pair
    rw [Finset.card_image_of_injective _ q2f_line_geometry.1] at pair
    obtain ⟨i,sub⟩ := gm.2.2 pair
    refine ⟨os_pt (q2f_point i),(q2f_line_geometry.2.2.2 i).2,?_⟩
    have sub' := Finset.image_subset_image sub (f := q2f_line_embed)
    rwa [(q2f_line_geometry.2.2.2 i).1] at sub'

lemma q2f_circuit_allowed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6}) (hplus : Bplus 14 D ≤ 13)
    (s : Fin 15) (a b c : Fin 10) (large : 7 ≤ (q2f_codes s a b c).card)
    (good : ∀ m ∈ q2f_codes s a b c,
      sup_Occ 14 D (sem_hw_opp 0) ((cap7_decode m).image q2f_line_embed) ∧
      2 ≤ (cap7_decode m).card ∧
      ((cap7_decode m).card = 2 → ∃ i : Fin 3, cap7_decode m ⊆ q2f_triple i)) :
    (q2f_codes s a b c).card ≤ 7 ∧
    ∀ w, q2f_allowed s a b c
      (cap7_encode (equality_mask_pull q2f_line_embed (supp 14 D w ∩ sem_hw_opp 0))) = true := by
  classical
  let f := q2f_line_embed
  let P := sem_hw_opp 0
  let Y := (q2f_codes s a b c).image (fun m => (cap7_decode m).image f)
  have inj := q2f_line_geometry.1
  have range := q2f_line_geometry.2.1
  have card : Y.card = (q2f_codes s a b c).card :=
    Finset.card_image_of_injective _ ((Finset.image_injective inj).comp cap7_decode_injective)
  have goodY : ∀ M ∈ Y, sup_Occ 14 D P M ∧ 2 ≤ M.card ∧
      (M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i) :=
    q2f_image_good _ good
  have bound := equality_line_q2_mask_bound h hD hI hM hplus Y goodY
  refine ⟨by rw [card] at bound; exact bound,?_⟩
  intro w
  let M := supp 14 D w ∩ P
  let A := equality_mask_pull f M
  have back : A.image f = M := equality_mask_pull_image f P range Finset.inter_subset_right
  have pullCard : A.card = M.card := by
    rw [← Finset.card_image_of_injective _ inj,back]
  have alternatives := equality_line_q2_occurring_allowed h hD hI hM hplus Y
    (by rw [card]; exact large) goodY M ⟨w,rfl⟩
  rcases alternatives with small | member | ⟨pair,outside⟩
  · apply q2f_or_true_iff.mpr
    left
    apply q2f_small_of_one s a b c _
    change cap7_card (cap7_encode A) ≤ 1
    rw [cap7_card_correct,cap7_decode_encode,pullCard]
    exact small
  · obtain ⟨m,hm,eq⟩ := Finset.mem_image.mp member
    have same : cap7_encode A = m := by
      apply cap7_decode_injective
      rw [cap7_decode_encode]
      apply Finset.image_injective inj
      exact back.trans eq.symm
    change q2f_allowed s a b c (cap7_encode A) = true
    rw [same]
    exact q2f_or_true_iff.mpr (Or.inr ((q2f_mem_iff s a b c m).mpr hm))
  · have two : cap7_card (cap7_encode A) = 2 := by
      rw [cap7_card_correct,cap7_decode_encode,pullCard,pair]
    have out : q2f_outside (cap7_encode A) = true := by
      apply (q2f_outside_correct _).mpr
      rw [cap7_decode_encode]
      refine ⟨pullCard.trans pair,?_⟩
      intro i sub
      apply outside _ (q2f_line_geometry.2.2.2 i).2
      have sub' := Finset.image_subset_image sub (f := f)
      rw [back] at sub'
      change M ⊆ (q2f_triple i).image q2f_line_embed at sub'
      rw [(q2f_line_geometry.2.2.2 i).1] at sub'
      exact sub'
    change q2f_allowed s a b c (cap7_encode A) = true
    simp only [q2f_allowed,q2f_small,two,out,decide_true,Bool.true_or,Bool.and_true,Bool.or_true]

lemma q2f_circuit_large_masks {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6}) (hplus : Bplus 14 D ≤ 13)
    (certificate : ∀ s a b c, q2f_certificate s a b c = true) :
    ∃ S : Finset (Fin 7), q2f_missingTriple ⊂ S ∧ ∀ w,
      let M := equality_mask_pull q2f_line_embed (supp 14 D w ∩ sem_hw_opp 0)
      M.card ≤ 2 ∨ M = cap7_decode 11 ∨ M = cap7_decode 69 ∨
        M = cap7_decode 49 ∨ M = S := by
  obtain ⟨S,strict,s,a,b,c,eq,good⟩ := q2f_circuit_family h hD hI hM
  have cert := certificate s a b c
  obtain ⟨bound,allowed⟩ := q2f_circuit_allowed h hD hI hM hplus s a b c
    (q2f_certificate_card s a b c cert) good
  have shape := q2f_occurring_shape h.1 q2f_line_embed q2f_line_geometry.1
    (sem_hw_opp 0) q2f_line_geometry.2.1 s a b c cert bound
    (fun m hm => (good m hm).1) allowed
  refine ⟨S,strict,?_⟩
  intro w
  have result := q2f_allowed_shape s a b c shape _ (allowed w)
  simp only [cap7_card_correct,cap7_decode_encode] at result
  rcases result with low | e | e | e | e
  · exact Or.inl low
  · exact Or.inr (Or.inl (by rw [← e,cap7_decode_encode]))
  · exact Or.inr (Or.inr (Or.inl (by rw [← e,cap7_decode_encode])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← e,cap7_decode_encode]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [← eq,← e,cap7_decode_encode]))))

end PEqualNP.Outside.L_meta_6659_aux
