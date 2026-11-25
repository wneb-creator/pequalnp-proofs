import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

def conesFrom (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (coneStep n) cs

lemma cones_eq_conesFrom (n : ℕ) (C : Circuit) :
    cones n C = conesFrom n C.gates [] := rfl

lemma conesFrom_append (n : ℕ) (gs₁ gs₂ : List Gate) (cs : List (List ℕ)) :
    conesFrom n (gs₁ ++ gs₂) cs = conesFrom n gs₂ (conesFrom n gs₁ cs) := by
  simp [conesFrom, List.foldl_append]

lemma conesFrom_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (conesFrom n gs cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp [conesFrom]
  | cons g gs ih =>
    simp only [conesFrom, List.foldl_cons] at ih ⊢
    rw [ih]; simp [coneStep]; omega

lemma conesFrom_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (conesFrom n gs cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n cs g).length := by simp [coneStep]; omega
    change (conesFrom n gs (coneStep n cs g)).getD j [] = cs.getD j []
    rw [ih (coneStep n cs g) hj']
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set pre := C.gates.take j
  set gj := C.gates[j]
  set post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := by simp [pre]; omega
  have hcs_len : (conesFrom n pre []).length = j := by rw [conesFrom_len, hpre_len]; simp
  have h1 : cones n C = conesFrom n post (coneStep n (conesFrom n pre []) gj) := by
    rw [cones_eq_conesFrom, hsplit, conesFrom_append]; rfl
  have hlt : j < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]
  rw [h1, conesFrom_getD_lt n post _ j hlt]
  have hmid : (coneStep n (conesFrom n pre []) gj).getD j [] =
      (gj.inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (conesFrom n pre []).getD (w - n) []) := by
    simp only [coneStep, hcs_len, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_of_eq hcs_len), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hmid, gateAt_eq_getElem C j hj]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwlt : w - n < j := by omega
  have hwlt' : w - n < (coneStep n (conesFrom n pre []) gj).length := by
    simp [coneStep, hcs_len]; omega
  congr 1
  rw [conesFrom_getD_lt n post _ (w - n) hwlt']
  simp only [coneStep, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : w - n < (conesFrom n pre []).length)]

lemma InCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD_eq n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, h⟩
    exact ⟨w, hw1, hw2, hw3, h⟩
  · rintro ⟨w, hw1, hw2, hw3, h⟩
    exact ⟨w, ⟨hw1, hw2, hw3⟩, h⟩

lemma InCone_ge_len (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) :
    ¬ InCone n C i j := by
  unfold InCone
  rw [List.getD_eq_default _ _ (by rw [cones_eq_conesFrom, conesFrom_len]; simp; omega)]
  simp

lemma InCone_lt (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < C.gates.length
    · obtain ⟨w, _, hw1, hw2, h'⟩ := (InCone_iff n C i j hj).mp h
      rcases h' with rfl | h'
      · omega
      · have := ih (w - n) (by omega) h'
        omega
    · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_lt_len (n : ℕ) (C : Circuit) {i j : ℕ} (h : InCone n C i j) :
    i < C.gates.length := by
  by_cases hj : j < C.gates.length
  · exact lt_trans (InCone_lt n C h) hj
  · exact (InCone_ge_len n C i j (by omega) h).elim

lemma InCone_of_mem_inputs (n : ℕ) (C : Circuit) {i j : ℕ}
    (hj : j < C.gates.length) (hRB : ReadsBack n C)
    (hm : n + i ∈ (gateAt C j).inputs) : InCone n C i j := by
  rw [InCone_iff n C i j hj]
  have hlt := hRB j hj (n + i) hm
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma InCone_trans (n : ℕ) (C : Circuit) {i j k : ℕ}
    (h1 : InCone n C i j) (h2 : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C j k hk).mp h2
      rw [InCone_iff n C i k hk]
      rcases h' with rfl | h'
      · exact ⟨w, hwm, hw1, hw2, Or.inr h1⟩
      · exact ⟨w, hwm, hw1, hw2, Or.inr (ih (w - n) (by omega) h')⟩
    · exact (InCone_ge_len n C j k (by omega) h2).elim

lemma InOutputCone_of_InCone (n : ℕ) (C : Circuit) {i j : ℕ}
    (h1 : InCone n C i j) (h2 : InOutputCone n C j) : InOutputCone n C i := by
  refine ⟨InCone_lt_len n C h1, ?_⟩
  rcases h2.2 with ho | ⟨hn, hc⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [ho, Nat.add_sub_cancel_left]
    exact h1
  · right
    exact ⟨hn, InCone_trans n C h1 hc⟩

lemma mem_coneSet_iff (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) (i : ℕ) :
    i ∈ coneSet n C c ↔ i = c ∨ InCone n C i c := by
  unfold coneSet
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨InCone_lt_len n C h, h⟩

lemma coneSet_subset_range (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < C.gates.length) :
    coneSet n C c ⊆ Finset.range C.gates.length := by
  intro i hi
  rw [Finset.mem_range]
  rcases (mem_coneSet_iff n C c hc i).mp hi with rfl | h
  · exact hc
  · exact InCone_lt_len n C h

lemma InCone_has_reader (n : ℕ) (C : Circuit) {i c : ℕ} (hc : c < C.gates.length)
    (h : InCone n C i c) :
    ∃ k ∈ coneSet n C c, n + i ∈ (gateAt C k).inputs := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    obtain ⟨w, hwm, hw1, hw2, h'⟩ := (InCone_iff n C i c hc).mp h
    rcases h' with rfl | h'
    · refine ⟨c, (mem_coneSet_iff n C c hc c).mpr (Or.inl rfl), ?_⟩
      rwa [show n + (w - n) = w by omega]
    · have hwlt : w - n < C.gates.length := by omega
      obtain ⟨k, hk, hkin⟩ := ih (w - n) (by omega) hwlt h'
      refine ⟨k, ?_, hkin⟩
      rw [mem_coneSet_iff n C c hc]
      rcases (mem_coneSet_iff n C (w - n) hwlt k).mp hk with rfl | hk'
      · exact Or.inr ((InCone_iff n C (w - n) c hc).mpr ⟨w, hwm, hw1, hw2, Or.inl rfl⟩)
      · exact Or.inr ((InCone_iff n C k c hc).mpr ⟨w, hwm, hw1, hw2, Or.inr hk'⟩)


variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma mem_maximal {j : ℕ} : j ∈ maximalCores G C ↔ IsMaximalCore G C j := by
  simp only [maximalCores, gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

lemma maximal_antichain {i j : ℕ} (hi : i ∈ maximalCores G C)
    (hj : j ∈ maximalCores G C) : ¬ InCone n C i j := by
  exact (mem_maximal.mp hi).2 j (mem_maximal.mp hj).1.1 (mem_maximal.mp hj).1

lemma maximal_in_cone_iff {i j : ℕ} (hi : i ∈ maximalCores G C)
    (hj : j ∈ maximalCores G C) : i ∈ coneSet n C j ↔ i = j := by
  rw [mem_coneSet_iff n C j (mem_maximal.mp hj).1.1]
  exact or_iff_left (maximal_antichain hi hj)

lemma coneSet_mono {i j : ℕ} (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hij : i = j ∨ InCone n C i j) : coneSet n C i ⊆ coneSet n C j := by
  intro k hk
  rw [mem_coneSet_iff n C j hj]
  rcases (mem_coneSet_iff n C i hi k).mp hk with rfl | hk
  · exact hij
  · rcases hij with rfl | hij
    · exact Or.inr hk
    · exact Or.inr (InCone_trans n C hk hij)

lemma core_in_maximal {j : ℕ} (hj : IsCore G C j) :
    ∃ i ∈ maximalCores G C, j = i ∨ InCone n C j i := by
  classical
  let S := (cores G C).filter fun i => j = i ∨ InCone n C j i
  have hjs : j ∈ S := by simp [S, cores, gatesWhere, hj, hj.1]
  let i := S.max' ⟨j,hjs⟩
  have his : i ∈ S := Finset.max'_mem S ⟨j,hjs⟩
  have hi := (Finset.mem_filter.mp his).1
  have hci : IsCore G C i := (Finset.mem_filter.mp hi).2
  refine ⟨i, mem_maximal.mpr ⟨hci, ?_⟩, (Finset.mem_filter.mp his).2⟩
  intro k hk hck hik
  have hjk : j = k ∨ InCone n C j k := by
    right
    rcases (Finset.mem_filter.mp his).2 with hji | hji
    · exact hji ▸ hik
    · exact InCone_trans n C hji hik
  have hks : k ∈ S := by simp only [S, Finset.mem_filter, cores, gatesWhere, Finset.mem_range]; exact ⟨⟨hk,hck⟩,hjk⟩
  have hki : k ≤ i := Finset.le_max' S k hks
  have hik' := InCone_lt n C hik
  omega

lemma core_cones_eq_maximal :
    (cores G C).biUnion (coneSet n C) = (maximalCores G C).biUnion (coneSet n C) := by
  apply Finset.Subset.antisymm
  · intro k hk
    obtain ⟨j,hj,hkj⟩ := Finset.mem_biUnion.mp hk
    have hcj : IsCore G C j := (Finset.mem_filter.mp hj).2
    obtain ⟨i,hi,hji⟩ := core_in_maximal hcj
    exact Finset.mem_biUnion.mpr ⟨i,hi,coneSet_mono hcj.1 (mem_maximal.mp hi).1.1 hji hkj⟩
  · intro k hk
    obtain ⟨i,hi,hki⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨i, by
      have hc := (mem_maximal.mp hi).1
      simp [cores, gatesWhere, hc, hc.1], hki⟩

lemma maximal_subset_union : maximalCores G C ⊆ (maximalCores G C).biUnion (coneSet n C) := by
  intro j hj
  exact Finset.mem_biUnion.mpr ⟨j,hj,by simp [coneSet]⟩

lemma fixed_live_or_below (hf : IsLiftFixedPoint G C) {j : ℕ}
    (hj : InOutputCone n C j) (hor : (gateAt C j).op = GateOp.or)
    (b : Fin 2) (hb : IsImpWire G C (opnd C j b)) : BelowF G C j := by
  by_contra hn
  exact hf ⟨j, hj.1, b, hj, hor, hn, hb⟩

end PEqualNP.Outside.L_meta_2962.Structural
namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma input_port_count (U M : Finset ℕ) (hmu : M ⊆ U)
    (hread : ∀ i ∈ U \ M, ∃ j ∈ U, ∃ b : Fin 2, opnd C j b = n + i) :
    ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card
      ≤ U.card + M.card := by
  classical
  let P := U ×ˢ (Finset.univ : Finset (Fin 2))
  let B := P.filter fun p => opnd C p.1 p.2 < n
  let I := P.filter fun p => ¬opnd C p.1 p.2 < n
  have hsub : U \ M ⊆ I.image (fun p => opnd C p.1 p.2 - n) := by
    intro i hi
    obtain ⟨j,hj,b,hb⟩ := hread i hi
    exact Finset.mem_image.mpr ⟨(j,b), by simp [I,P,hj,hb], by simp [hb]⟩
  have hcard : (U \ M).card ≤ I.card := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hsum : B.card + I.card = 2 * U.card := by
    rw [show B.card + I.card = P.card from Finset.card_filter_add_card_filter_not (s := P) (fun p => opnd C p.1 p.2 < n)]
    simp [P, Nat.mul_comm]
  have hdiff := Finset.card_sdiff_add_card_eq_card hmu
  change B.card ≤ U.card + M.card
  omega

lemma cone_union_reader (ao : IsAO2 n C) {i : ℕ}
    (hi : i ∈ (maximalCores G C).biUnion (coneSet n C) \ maximalCores G C) :
    ∃ j ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C j b = n + i := by
  obtain ⟨hi,hnm⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨c,hc,hic⟩ := Finset.mem_biUnion.mp hi
  have hcl := (mem_maximal.mp hc).1.1
  have hh : InCone n C i c := by
    rcases (mem_coneSet_iff n C c hcl i).mp hic with he | hh
    · exact False.elim (hnm (he ▸ hc))
    · exact hh
  obtain ⟨j,hj,hij⟩ := InCone_has_reader n C hcl hh
  have hjl : j < C.gates.length := Finset.mem_range.mp (coneSet_subset_range n C c hcl hj)
  obtain ⟨b,hb,he⟩ := List.getElem_of_mem hij
  have hbl : b < 2 := by rw [ao.2.2 _ (by rw [gateAt_eq_getElem C j hjl]; exact List.getElem_mem hjl)] at hb; exact hb
  refine ⟨j, Finset.mem_biUnion.mpr ⟨c,hc,hj⟩, ⟨b,hbl⟩, ?_⟩
  simpa [opnd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] using he

lemma core_input_ports (ao : IsAO2 n C) :
    ((((maximalCores G C).biUnion (coneSet n C)) ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => opnd C p.1 p.2 < n).card ≤
        ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card := by
  exact input_port_count _ _ maximal_subset_union (fun _ hi => cone_union_reader ao hi)

end PEqualNP.Outside.L_meta_2962.Structural
namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma port_budget_identity (U M : Finset ℕ) (hmu : M ⊆ U)
    (hread : ∀ i ∈ U \ M, ∃ j ∈ U, ∃ b : Fin 2, opnd C j b = n + i) :
    U.card + M.card =
      ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card +
      (((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => ¬opnd C p.1 p.2 < n).card -
        (U \ M).card) := by
  classical
  let P := U ×ˢ (Finset.univ : Finset (Fin 2))
  let B := P.filter fun p => opnd C p.1 p.2 < n
  let I := P.filter fun p => ¬opnd C p.1 p.2 < n
  have hsub : U \ M ⊆ I.image (fun p => opnd C p.1 p.2 - n) := by
    intro i hi
    obtain ⟨j,hj,b,hb⟩ := hread i hi
    exact Finset.mem_image.mpr ⟨(j,b), by simp [I,P,hj,hb], by simp [hb]⟩
  have hcard : (U \ M).card ≤ I.card := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hsum : B.card + I.card = 2 * U.card := by
    rw [show B.card + I.card = P.card from
      Finset.card_filter_add_card_filter_not (s := P) (fun p => opnd C p.1 p.2 < n)]
    simp [P, Nat.mul_comm]
  have hdiff := Finset.card_sdiff_add_card_eq_card hmu
  change U.card + M.card = B.card + (I.card - (U \ M).card)
  omega

lemma core_port_budget_identity (ao : IsAO2 n C) :
    let U := (maximalCores G C).biUnion (coneSet n C)
    let M := maximalCores G C
    U.card + M.card =
      ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card +
      (((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => ¬opnd C p.1 p.2 < n).card -
        (U \ M).card) := by
  exact port_budget_identity _ _ maximal_subset_union (fun _ hi => cone_union_reader ao hi)

end PEqualNP.Outside.L_meta_2962.Structural
