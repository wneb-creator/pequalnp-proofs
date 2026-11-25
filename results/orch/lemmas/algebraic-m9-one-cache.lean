import AlgebraicM9Complete
import PNPCapSevenBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux

noncomputable def equality_mask_pull (f : Fin 7 → Fin 14) (M : Finset (Fin 14)) :
    Finset (Fin 7) := by
  classical
  exact Finset.univ.filter (fun k => f k ∈ M)

theorem equality_mask_pull_image (f : Fin 7 → Fin 14) (P : Finset (Fin 14))
    (range : Finset.univ.image f = P) {M : Finset (Fin 14)} (sub : M ⊆ P) :
    (equality_mask_pull f M).image f = M := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 ha
    exact (Finset.mem_filter.1 hk).2
  · intro ha
    have hp : a ∈ Finset.univ.image f := by rw [range]; exact sub ha
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,ha⟩,rfl⟩

def equality_mask_parent (Q : Finset (Fin 7) → Prop) (T : Finset (Fin 7)) : Prop :=
  (∃ A, Q A ∧ A.card = 2 ∧ A ⊆ T) ∨
    (∃ A, Q A ∧ A.card = 4 ∧ T ⊆ A) ∨
    (∃ A B, A ≠ B ∧ Q A ∧ Q B ∧ A.card = 5 ∧ B.card = 5 ∧
      T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T)

theorem equality_occurring_parent_pull_subset {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (injective : Function.Injective f) (P R : Finset (Fin 14)) (subrange : P ⊆ R)
    (range : Finset.univ.image f = R) (T : Finset (Fin 7)) (hT : T.card = 3)
    (occur : sup_Occ 14 D P (T.image f)) :
    equality_mask_parent (fun M => sup_Occ 14 D P (M.image f)) T := by
  classical
  have p7 : P.card ≤ 7 := by
    have bound := Finset.card_le_card subrange
    rw [← range,Finset.card_image_of_injective _ injective] at bound
    simpa only [Finset.card_univ,Fintype.card_fin] using bound
  have imageCard : (T.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ injective]
    exact hT
  have back (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).image f = A :=
    equality_mask_pull_image f R range (fun x hx => subrange (sup_occ_sub hA hx))
  have card (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).card = A.card := by
    rw [← Finset.card_image_of_injective _ injective,back A hA]
  rcases sup_triple_parent hS p7 imageCard occur with
    ⟨A,hA,ca,sa⟩ | ⟨A,hA,ca,sa⟩ | ⟨A,B,ne,hA,hB,ca,cb,_,_,inter⟩
  · refine Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · refine Or.inr (Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩)
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · have eq : equality_mask_pull f A ∩ equality_mask_pull f B = T := by
      apply Finset.image_injective injective
      rw [Finset.image_inter _ _ injective,back A hA,back B hB,inter]
    refine Or.inr (Or.inr ⟨equality_mask_pull f A,equality_mask_pull f B,?_,?_,?_,?_,?_,?_,?_,eq⟩)
    · intro same
      apply ne
      rw [← back A hA,← back B hB,same]
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · change sup_Occ 14 D P ((equality_mask_pull f B).image f)
      rwa [back B hB]
    · rw [card A hA,ca]
    · rw [card B hB,cb]
    · rw [← eq]
      exact Finset.inter_subset_left
    · rw [← eq]
      exact Finset.inter_subset_right

theorem equality_count_mask_family {n : ℕ} {D : Dag} (hS : Strict n D)
    (P : Finset (Fin n)) (L Y : Finset (Finset (Fin n)))
    (hY : ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ n D P M)
    (hYpair : ∀ M ∈ Y, M.card = 2 → ∃ T ∈ L, M ⊆ T)
    (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL : ∀ f ∈ Lab, ∀ T ∈ L, (U f ∩ T).card ≤ 1) :
    Y.card + E.card + Lab.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  classical
  choose! wit hwit using hw
  let S := Lab.filter (fun f => ∀ M, M ⊆ U f → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M)
  have hSL : S ⊆ Lab := Finset.filter_subset _ _
  have hno : ∀ f ∈ Lab \ S, ∃ M, M ⊆ U f ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ n D P M := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  let X := (Lab \ S).image pr
  have hXpair : ∀ M ∈ X, M.card = 2 ∧ sup_Occ n D P M ∧ ∀ T ∈ L, ¬ M ⊆ T := by
    intro M hM
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.1 hM
    obtain ⟨hsub,hcard,_,hocc⟩ := hpr f hf
    refine ⟨hcard,hocc,?_⟩
    intro T hT hMT
    have lower := Finset.card_le_card (Finset.subset_inter hsub hMT)
    have upper := hUL f (Finset.mem_sdiff.1 hf).1 T hT
    omega
  have disjoint : Disjoint Y X := by
    apply Finset.disjoint_left.2
    intro M hMY hMX
    obtain ⟨T,hT,hMT⟩ := hYpair M hMY (hXpair M hMX).1
    exact (hXpair M hMX).2.2 T hT hMT
  have hX : Y.card + X.card ≤ (sup_big n D P).card := by
    have bound := sup_card_le_big hS P (Y ∪ X) (by
      intro M hM
      rcases Finset.mem_union.1 hM with hMY | hMX
      · exact hY M hMY
      · exact ⟨(hXpair M hMX).1.ge,(hXpair M hMX).2.1⟩)
    rwa [Finset.card_union_of_disjoint disjoint] at bound
  have hcnt := sup_count hS P E hE Lab S U wit hwit hSL (fun f hf =>
    sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
  have hfib : (Lab \ S).card ≤ 2 * X.card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g,hg⟩ := hne
      rw [Finset.mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine Finset.card_le_card (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
      simp
  have split := Finset.card_sdiff_add_card_eq_card hSL
  omega

theorem equality_hw_mask_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (P : Finset (Fin 14))
    (hPl : P ⊆ sem_hw_opp 0) (hPe : P ⊆ eligSet 14 D) (Oc Ct I : Finset (Fin 14))
    (hOc : ∀ i ∈ Oc, sem_hw_nb i ⊆ P ∧ sup_Occ 14 D P (sem_hw_nb i))
    (hCt : ∀ c ∈ Ct, c ∉ Oc ∧ ((sem_hw_nb c ∩ P).card ≤ 2 ∨
      (sem_hw_nb c ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb c))))
    (hI : ∀ i ∈ I, i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P)
    (Y : Finset (Finset (Fin 14)))
    (hY : ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ 14 D P M)
    (hYpair : ∀ M ∈ Y, M.card = 2 → ∃ i ∈ Oc, M ⊆ sem_hw_nb i) :
    Y.card + I.card + (Ct.biUnion (fun c => sem_hw_nb c ∩ P)).card +
      (eligSet 14 D).card ≤ 2 * P.card + Bplus 14 D := by
  classical
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  have hPi : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b :=
    fun a ha b hb => sem_hw_opp_indep 0 a (hPl ha) b (hPl hb)
  obtain ⟨E, hEc, hE⟩ := sup_assigned_exits hG h hC P I (fun i hi =>
    ⟨(hI i hi).1, sem_hw_nb i, (hI i hi).2, (degree_three i).ge, fun a ha => hw_mem_nb.1 ha⟩)
  have hlab : ∀ f ∈ Ct.biUnion (fun c => sem_hw_nb c ∩ P), ∃ c ∈ Ct, f ∈ sem_hw_nb c ∩ P :=
    fun f hf => Finset.mem_biUnion.1 hf
  choose! ct hct using hlab
  have hmain := equality_count_mask_family h.1 P (Oc.image sem_hw_nb) Y hY
    (fun M hM hM2 => by
      obtain ⟨i,hi,hsub⟩ := hYpair M hM hM2
      exact ⟨sem_hw_nb i,Finset.mem_image.2 ⟨i,hi,rfl⟩,hsub⟩)
    E hE (Ct.biUnion (fun c => sem_hw_nb c ∩ P)) (fun f => sem_hw_nb (ct f) ∩ P)
    (fun f hf => by
      obtain ⟨hc, hfc⟩ := hct f hf
      refine sup_wit_exists hG h.1 hC (X := insert (ct f) (P \ (sem_hw_nb (ct f) ∩ P)))
        Finset.inter_subset_right ?_ ?_ (fun a ha => Finset.mem_insert_of_mem ha) hfc
        ⟨ct f, Finset.mem_insert_self _ _, adj_symm (hw_mem_nb.1 (Finset.mem_inter.1 hfc).1)⟩
      · rcases (hCt _ hc).2 with h2 | ⟨h2, h4⟩
        · exact Or.inl h2
        · rw [Finset.inter_eq_left.2 h2]; exact Or.inr ⟨degree_three _, h4⟩
      · have hno : ∀ a ∈ P \ (sem_hw_nb (ct f) ∩ P), ¬ Adj (ct f) a := by
          intro a ha hadj
          rw [Finset.mem_sdiff, Finset.mem_inter, hw_mem_nb] at ha
          exact ha.2 ⟨hadj, ha.1⟩
        intro a ha b hb
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · exact adj_irrefl _
        · exact hno b hb
        · exact fun hab => hno a ha (adj_symm hab)
        · exact hPi a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1)
    (fun f hf T hT => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hT
      have := sup_hw_inter (ct f) i (fun hij => (hCt _ (hct f hf).1).1 (hij ▸ hi)) P
      rwa [show Finset.univ.filter (fun z => Adj i z) ∩ P = sem_hw_nb i from
        Finset.inter_eq_left.2 (hOc i hi).1] at this)
  have h4 := carrier_flow_union h P (by rw [heawood_supp_out hD]; simp)
  have h5 := surplus_carrierT_le h.1 b hb P
  rw [Finset.inter_eq_left.2 hPe] at h5
  rw [hEc] at hmain
  omega

def equality_m9_full_line (i : Fin 7) : Fin 14 := Fin.natAdd 7 i

theorem equality_m9_one_missing_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) :
    ∃ Y : Finset (Finset (Fin 14)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ 14 D mx_L M ∧
        (M.card = 2 → ∃ i ∈ ({0,1,2} : Finset (Fin 14)), M ⊆ sem_hw_nb i) := by
  classical
  let f := equality_m9_full_line
  let Q := fun M : Finset (Fin 7) => sup_Occ 14 D mx_L (M.image f)
  have inj : Function.Injective f := by
    intro i j equal
    apply Fin.ext
    have eq := congrArg (Fin.val : Fin 14 → ℕ) equal
    change 7+i.val = 7+j.val at eq
    omega
  have range : Finset.univ.image f = sem_hw_opp 0 := by decide +kernel
  have subrange : mx_L ⊆ sem_hw_opp 0 := by decide
  have geometry : (∀ i : Fin 3, (cap7_triple i).image f = sem_hw_nb (![0,1,2] i)) ∧
      cap7_missing.image f = sem_hw_nb 5 := by decide +kernel
  have occurs (i : Fin 14) (hi : i ∈ ({0,1,2} : Finset (Fin 14))) :
      sup_Occ 14 D mx_L (sem_hw_nb i) := by
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨(by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have base (i : Fin 3) : Q (cap7_triple i) := by
    change sup_Occ 14 D mx_L ((cap7_triple i).image f)
    rw [geometry.1 i]
    exact occurs _ ((by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i)
  have parents (i : Fin 3) : cap7_Parent Q (cap7_triple i) := by
    change equality_mask_parent Q (cap7_triple i)
    exact equality_occurring_parent_pull_subset h.1 f inj mx_L (sem_hw_opp 0)
      subrange range (cap7_triple i) (cap7_triple_card i) (base i)
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have ineligible : (5 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  let A := supp 14 D (src D (pos 5)) ∩ mx_L
  have hA : sup_Occ 14 D mx_L A := ⟨src D (pos 5),rfl⟩
  have subA : A ⊆ sem_hw_opp 0 := fun x hx => subrange (Finset.mem_inter.1 hx).2
  let S := equality_mask_pull f A
  have back : S.image f = A := equality_mask_pull_image f (sem_hw_opp 0) range subA
  have neighbors : sem_hw_nb 5 ⊆ A := by
    intro x hx
    exact Finset.mem_inter.2 ⟨(hpos.1 _ ineligible).2.2.1 x (hw_mem_nb.1 hx),mx_cap 5 (by decide) hx⟩
  have absent : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have strict : cap7_missing ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.2
    constructor
    · apply (Finset.image_subset_image_iff inj).1
      rw [geometry.2,back]
      exact neighbors
    · intro equal
      apply absent
      rw [← geometry.2,equal,back]
      exact hA
  have hS : Q S := by change sup_Occ 14 D mx_L (S.image f); rwa [back]
  obtain ⟨Y,large,good⟩ := cap7_seven_occurring Q base parents S strict hS
  refine ⟨Y.image (fun M => M.image f),?_,?_⟩
  · rw [Finset.card_image_of_injective _ (Finset.image_injective inj)]
    exact large
  · intro M hMY
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.1 hMY
    refine ⟨?_,(good T hT).1,?_⟩
    · rw [Finset.card_image_of_injective _ inj]
      exact (good T hT).2.1
    · intro pair
      rw [Finset.card_image_of_injective _ inj] at pair
      obtain ⟨i,sub⟩ := (good T hT).2.2 pair
      refine ⟨![0,1,2] i,?_,?_⟩
      · exact (by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i
      · have imageSub := Finset.image_subset_image sub (f := f)
        rwa [geometry.1 i] at imageSub

theorem equality_m9_one_missing_five_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) : False := by
  classical
  obtain ⟨Y,large,good⟩ := equality_m9_one_missing_family h hD hI hM
  have eligible : mx_L ⊆ eligSet 14 D := by
    intro x hx
    by_contra no
    exact mx_el x hx (hI ▸ sem_mem_inelig.2 no)
  have occurs : ∀ i ∈ ({0,1,2} : Finset (Fin 14)),
      sem_hw_nb i ⊆ mx_L ∧ sup_Occ 14 D mx_L (sem_hw_nb i) := by
    intro i hi
    have cap : i ∈ ({0,1,2,5} : Finset (Fin 14)) := (by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi
    refine ⟨mx_cap i cap,?_⟩
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2 ⟨cap,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have centers : ∀ c ∈ ({3,4,6} : Finset (Fin 14)), c ∉ ({0,1,2} : Finset (Fin 14)) ∧
      ((sem_hw_nb c ∩ mx_L).card ≤ 2 ∨
        (sem_hw_nb c ⊆ mx_L ∧ ¬ sup_Occ 14 D mx_L (sem_hw_nb c))) := by
    intro c hc
    exact ⟨fun hi => (mx_ctr c hc).1 ((by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),
      Or.inl (mx_ctr c hc).2⟩
  have ineligible : ∀ i ∈ ({0,1,2,5} : Finset (Fin 14)),
      i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ mx_L := by
    intro i hi
    exact ⟨by rw [hI]; exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi,mx_cap i hi⟩
  have bound := equality_hw_mask_family h hD mx_L (by decide) eligible {0,1,2} {3,4,6}
    {0,1,2,5} occurs centers ineligible Y
    (fun M hMY => ⟨(good M hMY).1,(good M hMY).2.1⟩)
    (fun M hMY pair => (good M hMY).2.2 pair)
  have ec := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at ec
  rw [show ({0,1,2,5} : Finset (Fin 14)).card = 4 from rfl,mx_lab,
    show mx_L.card = 6 from rfl] at bound
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,Finset.card_singleton] at zero
  have total := totalSurplus_split 14 D
  omega

end PEqualNP.Outside.L_meta_6659_aux
