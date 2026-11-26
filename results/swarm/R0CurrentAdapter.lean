import R1StandaloneAudit
import H8R0CompactAudit

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma petersen_tight_merges_empty {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) (x : Fin 10) :
    merges 10 D (carrierT 10 D {x}) = ∅ := by
  by_cases hx : x = 0
  · subst x
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := sem_inelig_consumer petersen_graph_ok h hC hz
    exact hm
  · obtain ⟨b, hb⟩ := sem_exists_pureBranch petersen_graph_ok h.1 hC
    have hw := petersen_tight_nonzero_exit_card h hC hz hB x hx
    have hs := surplus_carrierT_le h.1 b hb {x}
    have hf := carrier_flow_union h {x} (by rw [sem_supp_out petersen_graph_ok hC]; simp)
    have hi : (({x} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    rw [Finset.card_singleton] at hf
    apply Finset.card_eq_zero.mp
    omega

lemma h3_tight_typed_sources_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ r : Fin 10 → ℕ × Bool, Function.Injective r ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r) ∧
      (∀ i : Fin 10, (r i).1 < D.length ∧ tag D (r i).1 = true ∧
        supp 10 D (10 + (r i).1) = ∅) ∧
      (∀ j, j < D.length → Disjoint (supp 10 D (opA D j)) (supp 10 D (opB D j))) ∧
      ∀ j, j < D.length → tag D j = true →
        (∃ i : Fin 10, r i = (j, false) ∧
          supp 10 D (opA D j) = SideGeometry.side i ∧
          supp 10 D (opB D j) = SideGeometry.side (SideGeometry.opposite i)) ∨
        (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)  := by
  obtain ⟨r, hinj, hopp, hsources, hW, hvalid, htypes⟩ :=
    h3_all_two_typed_sources_exist h hC hz (petersen_tight_nonzero_exit_card h hC hz hB)
  have hm := petersen_tight_merges_empty h hC hz hB
  have hd : ∀ j, j < D.length → Disjoint (supp 10 D (opA D j)) (supp 10 D (opB D j)) :=
    fun _ hj => h3_no_merges_inputs_disjoint h.1 hm hj
  refine ⟨r, hinj, hopp, hsources, hW, hvalid, hd, ?_⟩
  intro j hj ht
  rcases htypes j hj ht with hp | he
  · exact Or.inl hp
  · have hzA : supp 10 D (opA D j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Finset.disjoint_left.mp (hd j hj) hx (he ▸ hx)
    exact Or.inr ⟨hzA, he.symm.trans hzA⟩

def h3_evenSide (k : Fin 5) : Fin 10 := ⟨2 * k.val, by omega⟩

def h3_groupGate (r : Fin 10 → ℕ × Bool) (k : Fin 5) : ℕ :=
  (r (h3_evenSide k)).1

lemma h3_evenSide_injective : Function.Injective h3_evenSide := by
  intro k l he
  have := congrArg Fin.val he
  apply Fin.ext
  simp only [h3_evenSide] at this
  omega

lemma h3_evenSide_ne_opposite : ∀ k l : Fin 5,
    h3_evenSide k ≠ SideGeometry.opposite (h3_evenSide l) := by
  unfold h3_evenSide SideGeometry.opposite
  decide +kernel

lemma h3_side_in_pair : ∀ i : Fin 10, ∃ k : Fin 5,
    i = h3_evenSide k ∨ i = SideGeometry.opposite (h3_evenSide k) := by
  unfold h3_evenSide SideGeometry.opposite
  decide +kernel

lemma h3_groupGate_injective (r : Fin 10 → ℕ × Bool) (hinj : Function.Injective r)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) :
    Function.Injective (h3_groupGate r) := by
  intro k l hkl
  rcases sem_same_gate hkl with he | he
  · exact (h3_evenSide_injective (hinj he)).symm
  · have he' : r (h3_evenSide l) = r (SideGeometry.opposite (h3_evenSide k)) := by
      rw [hopp]
      exact he
    exact False.elim (h3_evenSide_ne_opposite l k (hinj he'))

lemma h3_side_gate_is_group (r : Fin 10 → ℕ × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) (i : Fin 10) :
    ∃ k : Fin 5, (r i).1 = h3_groupGate r k := by
  obtain ⟨k, hk | hk⟩ := h3_side_in_pair i
  · exact ⟨k, hk ▸ rfl⟩
  · refine ⟨k, ?_⟩
    rw [hk, hopp]
    rfl

lemma h3_group_supports {D : Dag} (r : Fin 10 → ℕ × Bool)
    (hopp : ∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2))
    (hsources : ∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) (k : Fin 5) :
    (supp 10 D (opA D (h3_groupGate r k)) = SideGeometry.side (h3_evenSide k) ∧
      supp 10 D (opB D (h3_groupGate r k)) =
        SideGeometry.side (SideGeometry.opposite (h3_evenSide k))) ∨
    (supp 10 D (opA D (h3_groupGate r k)) =
        SideGeometry.side (SideGeometry.opposite (h3_evenSide k)) ∧
      supp 10 D (opB D (h3_groupGate r k)) = SideGeometry.side (h3_evenSide k)) := by
  cases hs : (r (h3_evenSide k)).2 with
  | false =>
    have hr : r (h3_evenSide k) = (h3_groupGate r k, false) := Prod.ext rfl hs
    have ho : r (SideGeometry.opposite (h3_evenSide k)) = (h3_groupGate r k, true) := by
      rw [hopp, hr]
      rfl
    exact Or.inl ⟨by simpa only [hr, sb_src_false] using hsources (h3_evenSide k),
      by simpa only [ho, sb_src_true] using hsources (SideGeometry.opposite (h3_evenSide k))⟩
  | true =>
    have hr : r (h3_evenSide k) = (h3_groupGate r k, true) := Prod.ext rfl hs
    have ho : r (SideGeometry.opposite (h3_evenSide k)) = (h3_groupGate r k, false) := by
      rw [hopp, hr]
      rfl
    exact Or.inr ⟨by simpa only [ho, sb_src_false] using hsources (SideGeometry.opposite (h3_evenSide k)),
      by simpa only [hr, sb_src_true] using hsources (h3_evenSide k)⟩

lemma h3_group_dirty_sides :
    SideGeometry.side (h3_evenSide 4) = SideGeometry.mask 200 ∧
    SideGeometry.side (SideGeometry.opposite (h3_evenSide 4)) = SideGeometry.mask 772 := by
  decide +kernel

lemma h3_first_four_groups_pure : ∀ k : Fin 5, k.val < 4 →
    ∀ a ∈ SideGeometry.side (h3_evenSide k),
      ∀ b ∈ SideGeometry.side (SideGeometry.opposite (h3_evenSide k)), petersenAdj a b := by
  unfold h3_evenSide SideGeometry.side SideGeometry.opposite SideGeometry.mask petersenAdj
  decide +kernel

lemma h3_tight_five_gates_exist {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) :
    ∃ (r : Fin 10 → ℕ × Bool) (gate : Fin 5 → ℕ),
      Function.Injective r ∧ Function.Injective gate ∧
      (∀ k, gate k = (r (h3_evenSide k)).1) ∧
      (∀ i, r (SideGeometry.opposite i) = ((r i).1, !(r i).2)) ∧
      (∀ i, supp 10 D (src D (r i)) = SideGeometry.side i) ∧
      (∀ x : Fin 10, exitArcs 10 D (carrierT 10 D {x}) =
        (Finset.univ.filter (fun i : Fin 10 => x ∈ SideGeometry.side i)).image r) ∧
      (∀ k, gate k < D.length ∧ tag D (gate k) = true ∧ supp 10 D (10 + gate k) = ∅) ∧
      (∀ k,
        (supp 10 D (opA D (gate k)) = SideGeometry.side (h3_evenSide k) ∧
          supp 10 D (opB D (gate k)) = SideGeometry.side (SideGeometry.opposite (h3_evenSide k))) ∨
        (supp 10 D (opA D (gate k)) = SideGeometry.side (SideGeometry.opposite (h3_evenSide k)) ∧
          supp 10 D (opB D (gate k)) = SideGeometry.side (h3_evenSide k))) ∧
      ∀ j, j < D.length → tag D j = true →
        (∃ k, j = gate k) ∨ (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅) := by
  obtain ⟨r, hinj, hopp, hsources, hW, hvalid, _, htypes⟩ :=
    h3_tight_typed_sources_exist h hC hz hB
  refine ⟨r, h3_groupGate r, hinj, h3_groupGate_injective r hinj hopp,
    fun _ => rfl, hopp, hsources, hW, ?_, h3_group_supports r hopp hsources, ?_⟩
  · intro k
    exact hvalid (h3_evenSide k)
  · intro j hj ht
    rcases htypes j hj ht with ⟨i, hi, _, _⟩ | hzero
    · left
      obtain ⟨k, hk⟩ := h3_side_gate_is_group r hopp i
      exact ⟨k, by simpa only [hi] using hk⟩
    · exact Or.inr hzero

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma h3_four_ports : ∀ g : Fin 4,
    SideGeometry.side (h3_evenSide ⟨g.val, by omega⟩) =
      PEqualNP.Outside.L_meta_2590.OnceGeometry.port g false ∧
    SideGeometry.side (SideGeometry.opposite (h3_evenSide ⟨g.val, by omega⟩)) =
      PEqualNP.Outside.L_meta_2590.OnceGeometry.port g true := by
  decide +kernel

lemma h3_dirty_ports :
    SideGeometry.side (h3_evenSide 4) =
      PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA ∧
    SideGeometry.side (SideGeometry.opposite (h3_evenSide 4)) =
      PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma h3_out_empty {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    supp 10 D (outW 10 D) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hh := (hC (single v)).mp (mem_supp.mp hv)
  have hf : ∀ v : Fin 10, ¬ sem_Edge petersenAdj (single v) := by
    unfold sem_Edge petersenAdj single
    decide +kernel
  exact hf v hh

lemma h3_six_rows : ∀ r : Fin 6,
    decide (3 ≤ r.val) = true ↔
    sem_Edge petersenAdj (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) := by
  unfold PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput
    PEqualNP.Outside.L_meta_2590.OnceGeometry.rowSet sem_Edge petersenAdj
  decide +kernel

lemma h3_output_mask {D : Dag} (hC : sem_Comp 10 petersenAdj D) :
    PEqualNP.Outside.L_meta_2590.OnceGeometry.wireMask D (outW 10 D) = 56 := by
  have hh : (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) =
      (fun r : Fin 6 => decide (3 ≤ r.val)) := by
    funext r
    apply Bool.eq_iff_iff.mpr
    exact (hC _).trans (h3_six_rows r).symm
  change PEqualNP.Outside.L_meta_2590.OnceGeometry.mask
    (fun r => val D (PEqualNP.Outside.L_meta_2590.OnceGeometry.rowInput r) (outW 10 D)) = 56
  rw [hh]
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma h3_tight_bzero_gt_one {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) : 1 < Bzero 10 D := by
  by_contra hnot
  have hb : Bzero 10 D ≤ 1 := by omega
  obtain ⟨r, gate, hr, hg, hgate, hopp, hsources, hW, hvalid, hports, htypes⟩ :=
    h3_tight_five_gates_exist h hC hz hB
  have hp : ∀ g : Fin 4,
      (supp 10 D (opA D (gate ⟨g.val, by omega⟩)) =
        PEqualNP.Outside.L_meta_2590.OnceGeometry.port g false ∧
       supp 10 D (opB D (gate ⟨g.val, by omega⟩)) =
        PEqualNP.Outside.L_meta_2590.OnceGeometry.port g true) ∨
      (supp 10 D (opA D (gate ⟨g.val, by omega⟩)) =
        PEqualNP.Outside.L_meta_2590.OnceGeometry.port g true ∧
       supp 10 D (opB D (gate ⟨g.val, by omega⟩)) =
        PEqualNP.Outside.L_meta_2590.OnceGeometry.port g false) := by
    intro g
    simpa only [(h3_four_ports g).1, (h3_four_ports g).2] using hports ⟨g.val, by omega⟩
  have hd : PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtySides D (gate 4) := by
    change (supp 10 D (opA D (gate 4)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA ∧
      supp 10 D (opB D (gate 4)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB) ∨
      (supp 10 D (opA D (gate 4)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyB ∧
      supp 10 D (opB D (gate 4)) =
        PEqualNP.Outside.L_meta_2590.FiveGroup.DAGBridge.DirtyA)
    simpa only [h3_dirty_ports.1, h3_dirty_ports.2] using hports 4
  exact PEqualNP.Outside.L_meta_2590.OnceActualLabels.five_gate_target_exclusion
    h.1 hb hg (fun k => ⟨(hvalid k).1,(hvalid k).2.1⟩) hp hd htypes ⟨h3_out_empty hC, h3_output_mask hC⟩

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma h3_tight_size19_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hB : Bplus 10 D = (eligSet 10 D).card) (hs : D.length ≤ 19) : False := by
  have hh := h3_tight_bzero_gt_one h hC hz hB
  have hb := h3_tight_size_budget h hC hz hB hs
  omega

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

namespace PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools

lemma h3_actual_i1_reduction_three {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 petersenAdj D) (hz : (0 : Fin 10) ∈ ineligSet 10 D)
    (hi : (ineligSet 10 D).card = 1) (hs : D.length ≤ 19) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 petersenAdj E ∧
      (0 : Fin 10) ∈ ineligSet 10 E ∧ Bzero 10 E = 0 ∧
      Bplus 10 E = (eligSet 10 E).card + 1 ∧ E.length = D.length ∧
      (h3_saturatedSet 10 E = {1,4} ∨ h3_saturatedSet 10 E = {1,4,5} ∨
        h3_saturatedSet 10 E = {3,6,7})  := by
  obtain ⟨_, hcases⟩ := h3_exact_i1_budget_cases h hC hz hi hs
  have hcard := inelig_card_add 10 D
  rcases hcases with ⟨hp, _⟩ | ⟨hp, hB0⟩
  · exact False.elim (h3_tight_size19_impossible h hC hz (by omega) hs)
  · exact h3_r1_reduction_three h hC hz hB0 (by omega)

end PEqualNP.Outside.L_meta_2590_aux.R1Standalone.DagTools
