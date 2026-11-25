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

namespace PEqualNP.Outside.L_meta_2962.Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this


lemma wire_input {n : Nat} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  change (run C.gates (List.ofFn x)).getD i.val false = _
  rw [run_getD _ _ _ (by simpa using i.isLt)]
  simp

lemma wire_gate {n : Nat} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool)
    (j : Nat) (hj : j < C.gates.length) :
    wval C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) :=
  cval_gate n C (List.ofFn x) (by simp) ao.2.1 j hj

lemma wire_all_true {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · exact wire_input C (fun _ => true) ⟨w, hn⟩
    · have hj : w-n < C.gates.length := by omega
      have wi : n + (w-n) = w := by omega
      rw [← wi, wire_gate C ao _ _ hj]
      have mem : gateAt C (w-n) ∈ C.gates := by
        rw [gateAt_eq C _ hj]
        exact List.getElem_mem _
      obtain ⟨a, b, ins⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
      have av : wval C (fun _ : Fin n => true) a = true := by
        have h := ao.2.1 (w-n) hj a (by simp [ins])
        exact ih a (by omega) (by omega)
      have bv : wval C (fun _ : Fin n => true) b = true := by
        have h := ao.2.1 (w-n) hj b (by simp [ins])
        exact ih b (by omega) (by omega)
      rcases ao.1 _ mem with op | op <;> simp [ins, op, av, bv, GateOp.eval]

lemma graph_unit_false {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) : graphFun G ∅ (fun i => decide (i = a)) = false := by
  simp [graphFun]

lemma below_wire_gate {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (w : Nat) (hw : w < n + C.gates.length)
    (below : ∀ x, wval C x w = true → graphFun G ∅ x = true) :
    IsImpOperand G C w := by
  have hn : n ≤ w := by
    by_contra h
    have wn : w < n := by omega
    let a : Fin n := ⟨w, wn⟩
    have yes : wval C (fun i => decide (i = a)) w = true := by
      simpa using wire_input C (fun i => decide (i = a)) a
    have bad := below _ yes
    rw [graph_unit_false] at bad
    contradiction
  refine ⟨hn, ?_, fun _ => true, ?_⟩
  · intro x hx
    apply below x
    simpa only [gateVal, wval, Nat.add_sub_of_le hn] using hx
  · simpa only [gateVal, wval, Nat.add_sub_of_le hn] using wire_all_true C ao w hw

lemma opnd_member {n : Nat} (C : Circuit) (ao : IsAO2 n C) (j : Nat)
    (hj : j < C.gates.length) (b : Fin 2) : opnd C j b ∈ (gateAt C j).inputs := by
  have mem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C _ hj]
    exact List.getElem_mem _
  have len := ao.2.2 _ mem
  unfold opnd
  rw [List.getD_eq_getElem _ _ (by simpa only [len] using b.isLt)]
  exact List.getElem_mem _

lemma core_is_and {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (core : IsCore G C j) :
    (gateAt C j).op = GateOp.and := by
  have mem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C _ core.1]
    exact List.getElem_mem _
  rcases ao.1 _ mem with hand | hor
  · exact hand
  · exfalso
    apply core.2.2.1
    have operand (b : Fin 2) : IsImpOperand G C (opnd C j b) := by
      have member := opnd_member C ao j core.1 b
      have bound := ao.2.1 j core.1 _ member
      have hj := core.1
      apply below_wire_gate G C ao _ (by omega)
      intro x hx
      apply core.2.1.1 x
      change wval C x (n+j) = true
      rw [wire_gate C ao x j core.1, hor]
      simp only [GateOp.eval, List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨opnd C j b, member, hx⟩, rfl⟩
    exact ⟨operand 0, operand 1⟩

lemma core_has_nonimplicant_operand {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C) (j : Nat)
    (core : IsCore G C j) : ∃ b : Fin 2,
      ¬ (∀ x, wval C x (opnd C j b) = true → graphFun G ∅ x = true) := by
  by_contra all
  push_neg at all
  apply core.2.2.1
  have operand (b : Fin 2) : IsImpOperand G C (opnd C j b) := by
    have bound := ao.2.1 j core.1 _ (opnd_member C ao j core.1 b)
    have hj := core.1
    exact below_wire_gate G C ao _ (by omega) (all b)
  exact ⟨operand 0, operand 1⟩

end PEqualNP.Outside.L_meta_2962.Semantic
namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2962.Semantic
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma essential_gate_input_occurrence (ao : IsAO2 n C) (v : Fin n)
    (x y : Fin n → Bool) (heq : ∀ t, t ≠ v → x t = y t)
    (j : ℕ) (hj : j < C.gates.length)
    (hdiff : gateVal n C j x ≠ gateVal n C j y) :
    ∃ i ∈ coneSet n C j, ∃ b : Fin 2, opnd C i b = v.val := by
  classical
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hex : ∃ w ∈ (gateAt C j).inputs, wval C x w ≠ wval C y w := by
      by_contra hn
      apply hdiff
      change wval C x (n+j) = wval C y (n+j)
      rw [wire_gate C ao x j hj, wire_gate C ao y j hj]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_contra hd
      exact hn ⟨w,hw,hd⟩
    obtain ⟨w,hw,hd⟩ := hex
    have hback := ao.2.1 j hj w hw
    by_cases hinput : w < n
    · let t : Fin n := ⟨w,hinput⟩
      have tv : t = v := by
        by_contra htv
        apply hd
        change wval C x t.val = wval C y t.val
        rw [wire_input, wire_input]
        exact heq t htv
      obtain ⟨b,hb,hbval⟩ := List.getElem_of_mem hw
      have hbl : b < 2 := by rw [ao.2.2 _ (by rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj)] at hb; exact hb
      refine ⟨j, by simp [coneSet], ⟨b,hbl⟩, ?_⟩
      have hv : w = v.val := congrArg Fin.val tv
      simpa [opnd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, hv] using hbval
    · have hn : n ≤ w := by omega
      have hk : w-n < j := by omega
      have hkl : w-n < C.gates.length := by omega
      have he : n + (w-n) = w := by omega
      have hd' : gateVal n C (w-n) x ≠ gateVal n C (w-n) y := by
        change wval C x (n+(w-n)) ≠ wval C y (n+(w-n))
        simpa only [he] using hd
      obtain ⟨i,hi,b,hb⟩ := ih (w-n) hk hkl hd'
      have hcone : InCone n C (w-n) j :=
        (InCone_iff n C (w-n) j hj).mpr ⟨w,hw,hn,hback,Or.inl rfl⟩
      exact ⟨i,coneSet_mono hkl hj (Or.inr hcone) hi,b,hb⟩

lemma accepted_edge_endpoint_port (ao : IsAO2 n C) {j : ℕ}
    (hj : j ∈ maximalCores G C) (u v : Fin n)
    (hv : gateVal n C j (pairInput u v) = true) :
    ∃ i ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C i b = u.val := by
  have hc := (mem_maximal.mp hj).1
  have hs : gateVal n C j (fun t => decide (t=v)) = false := by
    cases he : gateVal n C j (fun t => decide (t=v)) with
    | false => rfl
    | true => have hf := hc.2.1.1 _ he; rw [graph_unit_false] at hf; contradiction
  have hd : gateVal n C j (pairInput u v) ≠ gateVal n C j (fun t => decide (t=v)) := by
    rw [hv,hs]; decide
  obtain ⟨i,hi,b,hb⟩ := essential_gate_input_occurrence ao u (pairInput u v)
    (fun t => decide (t=v)) (by intro t ht; simp [pairInput,ht]) j hc.1 hd
  exact ⟨i,Finset.mem_biUnion.mpr ⟨j,hj,hi⟩,b,hb⟩

end PEqualNP.Outside.L_meta_2962.Structural
namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma gamma_endpoint_port (ao : IsAO2 n C) {e : Sym2 (Fin n)}
    (he : e ∈ (maximalCores G C).biUnion (gammaE G C)) (u : Fin n) (hu : u ∈ e) :
    ∃ i ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C i b = u.val := by
  obtain ⟨j,hj,hje⟩ := Finset.mem_biUnion.mp he
  obtain ⟨_,a,b,rfl,hv⟩ := Finset.mem_filter.mp hje
  simp only [Sym2.mem_iff] at hu
  rcases hu with hu | hu
  · subst u
    exact accepted_edge_endpoint_port ao hj a b hv
  · subst u
    apply accepted_edge_endpoint_port ao hj b a
    have heq : pairInput b a = pairInput a b := by funext t; simp [pairInput, or_comm]
    simpa only [heq] using hv

lemma supported_vertices_bound (ao : IsAO2 n C) (S : Finset (Fin n))
    (hs : ∀ u ∈ S, ∃ e ∈ (maximalCores G C).biUnion (gammaE G C), u ∈ e) :
    S.card ≤ ((maximalCores G C).biUnion (coneSet n C)).card +
      (maximalCores G C).card := by
  classical
  let U := (maximalCores G C).biUnion (coneSet n C)
  let P := (U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n
  have hsub : S.image Fin.val ⊆ P.image (fun p => opnd C p.1 p.2) := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,hue⟩ := hs u hu
    obtain ⟨i,hi,b,hb⟩ := gamma_endpoint_port ao he u hue
    exact Finset.mem_image.mpr ⟨(i,b), by simp [P,U,hi,hb], hb⟩
  have hS : (S.image Fin.val).card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hp : (P.image (fun p => opnd C p.1 p.2)).card ≤ P.card := Finset.card_image_le
  have h := Finset.card_le_card hsub
  have bound := core_input_ports (G := G) ao
  change P.card ≤ U.card + (maximalCores G C).card at bound
  rw [hS] at h
  exact (h.trans hp).trans bound

end PEqualNP.Outside.L_meta_2962.Structural


namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} (G : SimpleGraph (Fin n))

def CoversDeleted (D : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S

theorem cover_union (D : Finset (Sym2 (Fin n))) (S R : Finset (Fin n))
    (hS : CoversDeleted G D S)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : G.IsVertexCover ((S ∪ R : Finset (Fin n)) : Set (Fin n)) := by
  intro u v huv
  by_cases he : s(u, v) ∈ D
  · rcases hS u v huv he with hu | hv
    · exact Or.inl (Finset.mem_union_left R hu)
    · exact Or.inr (Finset.mem_union_left R hv)
  · have hdel : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨huv, he⟩
    rcases hR hdel with hu | hv
    · exact Or.inl (Finset.mem_union_right S hu)
    · exact Or.inr (Finset.mem_union_right S hv)

theorem cover_extension_bound (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : CoversDeleted G D S) : T.card ≤ S.card + R.card := by
  exact (hT.2 (S ∪ R) (cover_union G D S R hS hR)).trans
    (Finset.card_union_le S R)

theorem core_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (budget : ℕ) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : CoversDeleted G D S) (hbudget : D.card + S.card ≤ budget) :
    D.card + T.card ≤ budget + R.card := by
  have h := cover_extension_bound G D T R S hT hR hS
  omega

theorem relative_cover_union (D : Finset (Sym2 (Fin n))) (S R : Finset (Fin n))
    (hS : ∀ u v, G.Adj u v → s(u, v) ∈ D →
      u ∉ R → v ∉ R → u ∈ S ∨ v ∈ S)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : G.IsVertexCover ((S ∪ R : Finset (Fin n)) : Set (Fin n)) := by
  intro u v huv
  by_cases hu : u ∈ R
  · exact Or.inl (Finset.mem_union_right S hu)
  by_cases hv : v ∈ R
  · exact Or.inr (Finset.mem_union_right S hv)
  have he : s(u, v) ∈ D := by
    by_contra he
    have hdel : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨huv, he⟩
    exact (hR hdel).elim hu hv
  rcases hS u v huv he hu hv with h | h
  · exact Or.inl (Finset.mem_union_left R h)
  · exact Or.inr (Finset.mem_union_left R h)

theorem relative_core_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (budget : ℕ) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : ∀ u v, G.Adj u v → s(u, v) ∈ D →
      u ∉ R → v ∉ R → u ∈ S ∨ v ∈ S)
    (hbudget : D.card + S.card ≤ budget) : D.card + T.card ≤ budget + R.card := by
  have h := (hT.2 (S ∪ R) (relative_cover_union G D S R hS hR)).trans
    (Finset.card_union_le S R)
  omega

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial

namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} (G : SimpleGraph (Fin n))

theorem star_cover (D : Finset (Sym2 (Fin n))) (S L : Finset (Fin n))
    (f : Fin n → Fin n) (hD : D = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) : CoversDeleted G D S := by
  intro u v _ huv
  rw [hD] at huv
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp huv
  rcases Sym2.eq_iff.mp heq with h | h
  · exact Or.inl (h.1 ▸ hf w hw)
  · exact Or.inr (h.1 ▸ hf w hw)

theorem star_vertices_incident (D : Finset (Sym2 (Fin n))) (S L : Finset (Fin n))
    (f : Fin n → Fin n) (hD : D = L.image (fun v => s(f v, v)))
    (hS : S ⊆ L.image f) :
    ∀ v ∈ S ∪ L, ∃ e ∈ D, v ∈ e := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp (hS h)
    refine ⟨s(f w, w), ?_, ?_⟩
    · rw [hD]
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · rw [← heq]
      exact Sym2.mem_mk_left _ _
  · refine ⟨s(f v, v), ?_, Sym2.mem_mk_right _ _⟩
    rw [hD]
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

theorem star_forest_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (S L T R : Finset (Fin n)) (f : Fin n → Fin n) (budget : ℕ)
    (hD : D = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) (hdisj : Disjoint S L)
    (hvertices : (S ∪ L).card ≤ budget)
    (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : D.card + T.card ≤ budget + R.card := by
  have hcard : D.card ≤ L.card := by
    rw [hD]
    exact Finset.card_image_le
  have hsum := Finset.card_union_of_disjoint hdisj
  apply core_budget_sufficient G D T R S budget hT hR (star_cover G D S L f hD hf)
  omega

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial

namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core

theorem star_forest_core_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (S L T R : Finset (Fin n)) (f : Fin n → Fin n)
    (hD : (maximalCores G C).biUnion (gammaE G C) = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) (hS : S ⊆ L.image f) (hdisj : Disjoint S L)
    (hT : IsMinCover G T)
    (hR : IsMinCover
      (G.deleteEdges (((maximalCores G C).biUnion (gammaE G C)) : Set (Sym2 (Fin n)))) R) :
    ((maximalCores G C).biUnion (gammaE G C)).card + T.card ≤
      ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card + R.card := by
  have vertices := PEqualNP.Outside.L_meta_2962.Structural.supported_vertices_bound
    (G := G) (C := C) ao (S ∪ L)
    (star_vertices_incident _ S L f hD hS)
  exact star_forest_budget_sufficient G _ S L T R f _ hD hf hdisj vertices hT hR.1

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial
