import PNPAccepted6659
import PNPQ2FClosureComplete
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace PEqualNP.Outside.L_meta_6659_aux
noncomputable def equality_missing_points (D : Dag) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter
    (fun k => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))

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

theorem equality_line_q2_mask_bound {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6})
    (hplus : Bplus 14 D ≤ 13) (Y : Finset (Finset (Fin 14)))
    (good : ∀ M ∈ Y, sup_Occ 14 D (sem_hw_opp 0) M ∧ 2 ≤ M.card ∧
      (M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i)) :
    Y.card ≤ 7 := by
  classical
  let P := sem_hw_opp 0
  let Oc := ({0,1,3} : Finset (Fin 14))
  let Ct := (({2,4,5,6} : Finset (Fin 7)).image os_pt)
  have eligible : P ⊆ eligSet 14 D := by
    intro x hx
    by_contra hn
    have hi := sem_mem_inelig.2 hn
    rw [hI] at hi
    exact Finset.disjoint_left.1
      (by decide : Disjoint P ({0,1,2,3} : Finset (Fin 14))) hx hi
  have disjoint : Disjoint Oc Ct := by decide
  have occurs : ∀ i ∈ Oc, sem_hw_nb i ⊆ P ∧ sup_Occ 14 D P (sem_hw_nb i) := by
    intro i hi
    have geo : ∀ i ∈ ({0,1,3} : Finset (Fin 14)), ∃ q : Fin 7,
        os_pt q = i ∧ q ∉ ({2,4,5,6} : Finset (Fin 7)) := by decide +kernel
    obtain ⟨q,rfl,hq⟩ := geo i hi
    refine ⟨os_nb_sub q,?_⟩
    by_contra absent
    have hm : q ∈ equality_missing_points D := Finset.mem_filter.2 ⟨Finset.mem_univ _,absent⟩
    exact hq (hM ▸ hm)
  have centers : ∀ c ∈ Ct, c ∉ Oc ∧ ((sem_hw_nb c ∩ P).card ≤ 2 ∨
      (sem_hw_nb c ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb c))) := by
    intro c hc
    refine ⟨fun ho => Finset.disjoint_left.1 disjoint ho hc,Or.inr ?_⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.1 hc
    refine ⟨os_nb_sub q,?_⟩
    have hm : q ∈ equality_missing_points D := by rw [hM]; exact hq
    exact (Finset.mem_filter.1 hm).2
  have ineligible : ∀ i ∈ ({0,1,2,3} : Finset (Fin 14)),
      i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P := by
    intro i hi
    refine ⟨by rw [hI]; exact hi,?_⟩
    exact (by decide +kernel : ∀ i ∈ ({0,1,2,3} : Finset (Fin 14)),
      sem_hw_nb i ⊆ sem_hw_opp 0) i hi
  have bound := equality_hw_mask_family h hD P (Finset.Subset.refl _) eligible Oc Ct
    {0,1,2,3} occurs centers ineligible Y
    (fun M hMY => ⟨(good M hMY).2.1,(good M hMY).1⟩)
    (fun M hMY h2 => (good M hMY).2.2 h2)
  have pc : P.card = 7 := by decide
  have ic : ({0,1,2,3} : Finset (Fin 14)).card = 4 := rfl
  have union : (Ct.biUnion (fun c => sem_hw_nb c ∩ P)).card = 6 := by decide
  have ec := inelig_card_add 14 D
  rw [hI,ic] at ec
  rw [pc,ic,union] at bound
  omega

theorem equality_line_q2_occurring_allowed {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6}) (hplus : Bplus 14 D ≤ 13)
    (Y : Finset (Finset (Fin 14))) (large : 7 ≤ Y.card)
    (good : ∀ M ∈ Y, sup_Occ 14 D (sem_hw_opp 0) M ∧ 2 ≤ M.card ∧
      (M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i))
    (M : Finset (Fin 14)) (occ : sup_Occ 14 D (sem_hw_opp 0) M) :
    M.card ≤ 1 ∨ M ∈ Y ∨ (M.card = 2 ∧
      ∀ i ∈ ({0,1,3} : Finset (Fin 14)), ¬ M ⊆ sem_hw_nb i) := by
  classical
  by_cases small : M.card ≤ 1
  · exact Or.inl small
  by_cases member : M ∈ Y
  · exact Or.inr (Or.inl member)
  right
  right
  by_contra hn
  have pair : M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i := by
    intro two
    by_contra no
    apply hn
    refine ⟨two,?_⟩
    intro i hi sub
    exact no ⟨i,hi,sub⟩
  have bound := equality_line_q2_mask_bound h hD hI hM hplus (insert M Y) (by
    intro A hA
    rcases Finset.mem_insert.1 hA with rfl | old
    · exact ⟨occ,by omega,pair⟩
    · exact good A old)
  rw [Finset.card_insert_of_notMem member] at bound
  omega

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

theorem equality_occurring_parent_pull {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (injective : Function.Injective f) (P : Finset (Fin 14))
    (range : Finset.univ.image f = P) (T : Finset (Fin 7)) (hT : T.card = 3)
    (occur : sup_Occ 14 D P (T.image f)) :
    equality_mask_parent (fun M => sup_Occ 14 D P (M.image f)) T := by
  classical
  have p7 : P.card ≤ 7 := by
    rw [← range,Finset.card_image_of_injective _ injective]
    simp
  have imageCard : (T.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ injective]
    exact hT
  have back (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).image f = A :=
    equality_mask_pull_image f P range (sup_occ_sub hA)
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

end PEqualNP.Outside.L_meta_6659_aux
namespace PEqualNP.Outside.L_meta_6659_aux

lemma support_mask_closed {n : ℕ} {D : Dag} (hS : Strict n D)
    (P : Finset (Fin n)) (Allowed Closed : Finset (Fin n) → Prop)
    (allowed : ∀ w, Allowed (supp n D w ∩ P))
    (empty : Closed ∅) (singletons : ∀ i : Fin n, i ∈ P → Closed {i})
    (unions : ∀ A B, Closed A → Closed B → Allowed (A ∪ B) → Closed (A ∪ B))
    (intersections : ∀ A B, Closed A → Closed B → Allowed (A ∩ B) → Closed (A ∩ B)) :
    ∀ w, Closed (supp n D w ∩ P) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · rw [supp_input D ⟨w,input⟩]
      by_cases member : (⟨w,input⟩ : Fin n) ∈ P
      · simpa [member] using singletons ⟨w,input⟩ member
      · simpa [member] using empty
    · by_cases valid : w < n+D.length
      · obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
        have hj : j<D.length := by omega
        obtain ⟨ha,hb,_⟩ := hS j hj
        cases ht : tag D j with
        | false =>
          have mask : supp n D (n+j) ∩ P =
              (supp n D (opA D j) ∩ P) ∪ (supp n D (opB D j) ∩ P) := by
            rw [supp_gate hS j hj,ht]
            ext v
            simp only [Bool.false_eq_true,ite_false,Finset.mem_inter,Finset.mem_union]
            tauto
          rw [mask]
          exact unions _ _ (ih _ ha) (ih _ hb) (by rw [← mask]; exact allowed _)
        | true =>
          have mask : supp n D (n+j) ∩ P =
              (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) := by
            rw [supp_gate hS j hj,ht]
            ext v
            simp only [ite_true,Finset.mem_inter]
            tauto
          rw [mask]
          exact intersections _ _ (ih _ ha) (ih _ hb) (by rw [← mask]; exact allowed _)
      · simpa only [supp_ge (n := n) D w (by omega),Finset.empty_inter] using empty

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_pull_union (f : Fin 7 → Fin 14) (A B : Finset (Fin 14)) :
    equality_mask_pull f (A ∪ B) = equality_mask_pull f A ∪ equality_mask_pull f B := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]

lemma q2f_pull_inter (f : Fin 7 → Fin 14) (A B : Finset (Fin 14)) :
    equality_mask_pull f (A ∩ B) = equality_mask_pull f A ∩ equality_mask_pull f B := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]

lemma q2f_pull_image (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (A : Finset (Fin 7)) : equality_mask_pull f (A.image f) = A := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨j,hj,eq⟩
    exact inj eq ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

lemma q2f_actual_closed {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (P : Finset (Fin 14)) (range : Finset.univ.image f = P)
    (s : Fin 15) (a b c : Fin 10) (gen : q2f_generators s a b c = true)
    (allowed : ∀ w, q2f_allowed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true) :
    ∀ w, q2f_closed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true := by
  classical
  apply support_mask_closed hS P
    (fun M => q2f_allowed s a b c (cap7_encode (equality_mask_pull f M)) = true)
    (fun M => q2f_closed s a b c (cap7_encode (equality_mask_pull f M)) = true)
    allowed
  · simpa only [equality_mask_pull, Finset.notMem_empty, Finset.filter_false] using
      q2f_closed_empty s a b c
  · intro i hi
    have member : i ∈ Finset.univ.image f := by rwa [range]
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp member
    have single : equality_mask_pull f {f j} = {j} := by
      simpa only [Finset.image_singleton] using q2f_pull_image f inj {j}
    rw [single]
    exact q2f_closed_singleton s a b c j
  · intro A B ha hb hab
    rw [q2f_pull_union] at hab ⊢
    exact q2f_finset_union s a b c gen _ _ ha hb hab
  · intro A B ha hb hab
    rw [q2f_pull_inter] at hab ⊢
    exact q2f_finset_inter s a b c gen _ _ ha hb hab

lemma q2f_occurring_shape {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (P : Finset (Fin 14)) (range : Finset.univ.image f = P)
    (s : Fin 15) (a b c : Fin 10) (cert : q2f_certificate s a b c = true)
    (bound : (q2f_codes s a b c).card ≤ 7)
    (occurs : ∀ m ∈ q2f_codes s a b c, sup_Occ 14 D P ((cap7_decode m).image f))
    (allowed : ∀ w, q2f_allowed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true) :
    q2f_shape s a b c = true := by
  apply q2f_certificate_shape s a b c cert bound
  intro gen m hm
  obtain ⟨w,hw⟩ := occurs m hm
  have closed := q2f_actual_closed hS f inj P range s a b c gen allowed w
  rw [hw, q2f_pull_image f inj, cap7_encode_decode] at closed
  exact closed

end PEqualNP.Outside.L_meta_6659_aux

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
    simpa only [cap7_card_correct,cap7_decode_encode,pullCard] using small
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
      rwa [back,(q2f_line_geometry.2.2.2 i).1] at sub'
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

