import PEqualNP.Defs

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

namespace PEqualNP.Outside.L_meta_2962.Vectors
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def uvec (L : List ℕ) (u : ℕ) : List ℕ :=
  L.map fun j => if j = u then 1 else 0

lemma mem_insertNew_of_mem {A : List (List ℕ)} {v w : List ℕ} (h : w ∈ A) :
    w ∈ insertNew A v := by
  unfold insertNew
  split_ifs
  · exact h
  · exact List.mem_append_left _ h

lemma mem_insertNew_self (A : List (List ℕ)) (v : List ℕ) :
    v ∈ insertNew A v := by
  unfold insertNew
  split_ifs with h
  · exact h
  · exact List.mem_append_right _ (List.mem_singleton_self _)

lemma mem_foldl_insertNew_of_mem_acc {B A : List (List ℕ)} {w : List ℕ} (h : w ∈ A) :
    w ∈ B.foldl insertNew A := by
  induction B generalizing A with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (mem_insertNew_of_mem h)

lemma mem_foldl_insertNew_of_mem_list {B A : List (List ℕ)} {w : List ℕ} (h : w ∈ B) :
    w ∈ B.foldl insertNew A := by
  induction B generalizing A with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hxs
    · exact mem_foldl_insertNew_of_mem_acc (mem_insertNew_self A w)
    · exact ih hxs

lemma mem_foldl_orStep_of_mem_acc {ins : List (List (List ℕ))} {acc : List (List ℕ)}
    {w : List ℕ} (h : w ∈ acc) :
    w ∈ ins.foldl (fun a X => X.foldl insertNew a) acc := by
  induction ins generalizing acc with
  | nil => exact h
  | cons X Xs ih =>
    simp only [List.foldl_cons]
    exact ih (mem_foldl_insertNew_of_mem_acc h)

lemma mem_foldl_orStep {ins : List (List (List ℕ))} {acc : List (List ℕ)}
    {A : List (List ℕ)} {w : List ℕ} (hA : A ∈ ins) (hw : w ∈ A) :
    w ∈ ins.foldl (fun a X => X.foldl insertNew a) acc := by
  induction ins generalizing acc with
  | nil => cases hA
  | cons X Xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hA with rfl | hXs
    · exact mem_foldl_orStep_of_mem_acc (mem_foldl_insertNew_of_mem_list hw)
    · exact ih hXs

lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {u v : List ℕ} (hu : u ∈ A) (hv : v ∈ B) :
    capAdd k u v ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem_list
  rw [List.mem_flatMap]
  refine ⟨u, hu, ?_⟩
  rw [List.mem_map]
  exact ⟨v, hv, rfl⟩

lemma capAdd_zero_uvec (L : List ℕ) (u : ℕ) :
    capAdd 1 (L.map fun _ => 0) (uvec L u) = uvec L u := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [capAdd, uvec, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> rfl

lemma mem_uvec_le_one (L : List ℕ) (u : ℕ) :
    ∀ c ∈ uvec L u, c ≤ 1 := by
  intro c hc
  simp only [uvec, List.mem_map] at hc
  rcases hc with ⟨j, _, rfl⟩
  split_ifs <;> omega

lemma mem_capAdd_uvec_le_one (L : List ℕ) (u v : ℕ) (huv : u ≠ v) :
    ∀ c ∈ capAdd 1 (uvec L u) (uvec L v), c ≤ 1 := by
  induction L with
  | nil =>
    intro c hc
    simp [capAdd, uvec] at hc
  | cons a t ih =>
    intro c hc
    simp only [capAdd, uvec, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with rfl | hct
    · split_ifs with h1 h2
      · exact False.elim (huv (h1.symm.trans h2))
      · decide
      · decide
      · decide
    · exact ih c hct

lemma foldl_append_length {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_append_getD_lt {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [f init g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (init ++ [f init g]) hi']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_take_getD {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) (d : α) :
    ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init).getD i d =
      (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, List.foldl_append]
  have hlen : ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init).length = init.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  symm
  exact foldl_append_getD_lt f (gs.drop j) _ i d (by omega)

lemma foldl_append_getD_gate {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD (init.length + j) d =
      f ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set pref := (gs.take j).foldl (fun acc g => acc ++ [f acc g]) init
  have hlen : pref.length = init.length + j := by
    simp only [pref, foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : init.length + j < (pref ++ [f pref gs[j]]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [foldl_append_getD_lt f (gs.drop (j + 1)) (pref ++ [f pref gs[j]]) (init.length + j) d hlt]
  rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_append_length _ C.gates x

lemma wires_getD_lt (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  unfold Circuit.wires
  exact foldl_append_getD_lt _ C.gates x w false hw

lemma wires_getD_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  unfold Circuit.wires
  have h := foldl_append_getD_gate
    (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x j hj false
  rw [hx] at h
  rw [h, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hrb j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have ht := foldl_append_take_getD
    (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates x j i (Nat.le_of_lt hj) (by omega) false
  exact ht

lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (L : List ℕ) (k w : ℕ) (hw : w < n) :
    (readVectors C n L k).getD w [] = leafVectors L k w := by
  unfold readVectors
  have hw' : w < ((List.range n).map (leafVectors L k)).length := by
    simp [hw]
  rw [foldl_append_getD_lt _ C.gates _ w [] hw']
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
  rfl

lemma readVectors_getD_gate (n : ℕ) (C : Circuit) (L : List ℕ) (k : ℕ)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (readVectors C n L k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n L k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [L.map fun _ => 0]
      | _ => [] := by
  unfold readVectors
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep k) [L.map fun _ => 0]
    | _ => []
  let init := (List.range n).map (leafVectors L k)
  have hinit : init.length = n := by simp [init]
  have h := foldl_append_getD_gate step C.gates init j hj []
  rw [hinit] at h
  change (C.gates.foldl (fun R g => R ++ [step R g]) init).getD (n + j) [] = _
  rw [h]
  dsimp only [step]
  rw [gateAt_eq_getElem C j hj]
  have hmap : C.gates[j].inputs.map (fun i => ((C.gates.take j).foldl (fun R g => R ++ [step R g]) init).getD i []) =
      C.gates[j].inputs.map (fun i => (C.gates.foldl (fun R g => R ++ [step R g]) init).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < n + j := by
      have := hrb j hj i
      rw [gateAt_eq_getElem C j hj] at this
      exact this hi
    exact foldl_append_take_getD step C.gates init j i (Nat.le_of_lt hj) (by omega) []
  rw [hmap]
  rfl


end PEqualNP.Outside.L_meta_2962.Vectors



namespace PEqualNP.Outside.L_meta_2962.ActiveNested
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2962.Semantic PEqualNP.Outside.L_meta_2962.Vectors

lemma active_pair_vector {n : Nat} (C : Circuit) (ao : IsAO2 n C) (P : Nat → Prop)
    (a b : Fin n)
    (closed : ∀ w, P w → wval C (pairInput a b) w = true → w < n ∨ ∃ j < C.gates.length,
      w = n+j ∧ (gateAt C j).op = GateOp.or ∧ ∀ t ∈ (gateAt C j).inputs, P t)
    : ∀ w, P w → wval C (pairInput a b) w = true →
      ∃ u : Fin n, (u = a ∨ u = b) ∧
        wval C (fun i => decide (i = u)) w = true ∧
        uvec [a.val,b.val] u.val ∈ (readVectors C n [a.val,b.val] 1).getD w [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    rcases closed w hw hv with leaf | ⟨j,hj,rfl,op,children⟩
    · let u : Fin n := ⟨w,leaf⟩
      have endpoints : u = a ∨ u = b := by
        rw [wire_input C _ u] at hv
        exact of_decide_eq_true hv
      refine ⟨u,endpoints,?_,?_⟩
      · simpa using wire_input C (fun i => decide (i = u)) u
      · rw [readVectors_getD_lt C n [a.val,b.val] 1 w leaf]
        have mem : w ∈ [a.val,b.val] := by
          rcases endpoints with h | h <;> simp [←h,u]
        simp [leafVectors,mem,uvec,u]
    · rw [wire_gate C ao _ j hj,op] at hv
      simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at hv
      obtain ⟨_,⟨t,member,rfl⟩,value⟩ := hv
      obtain ⟨u,endpoints,unit,vec⟩ := ih t (ao.2.1 j hj t member) (children t member) value
      refine ⟨u,endpoints,?_,?_⟩
      · rw [wire_gate C ao _ j hj,op]
        simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
        exact ⟨true,⟨t,member,unit⟩,rfl⟩
      · rw [readVectors_getD_gate n C [a.val,b.val] 1 ao.2.1 j hj]
        dsimp only
        rw [op]
        exact mem_foldl_orStep (List.mem_map.mpr ⟨t,member,rfl⟩) vec

lemma no_active_nested_read_once {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.and) (below : BelowF G C j)
    (a b : Fin n)
    (nonested : ∀ i, InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput a b) ≠ true)
    (accepted : gateVal n C j (pairInput a b) = true) :
    readsAtMost (atGate n C j) n [a.val,b.val] 1 = true := by
  let P : Nat → Prop := fun w => w < n ∨ ∃ i, w = n+i ∧ InCone n C i j
  have closed : ∀ w, P w → wval C (pairInput a b) w = true → w < n ∨ ∃ i < C.gates.length,
      w = n+i ∧ (gateAt C i).op = GateOp.or ∧ ∀ t ∈ (gateAt C i).inputs, P t := by
    intro w hw active
    rcases hw with leaf | ⟨i,rfl,cone⟩
    · exact Or.inl leaf
    · right
      have hi := Structural.InCone_lt_len n C cone
      have mem : gateAt C i ∈ C.gates := by
        rw [Semantic.gateAt_eq C i hi]
        exact List.getElem_mem _
      refine ⟨i,hi,rfl,(ao.1 _ mem).resolve_left (fun hand => nonested i cone hand active),?_⟩
      intro t member
      by_cases ht : t < n
      · exact Or.inl ht
      · right
        have tn : n ≤ t := by omega
        have tc : InCone n C (t-n) i :=
          Structural.InCone_of_mem_inputs n C hi ao.2.1 (by simpa [Nat.add_sub_of_le tn] using member)
        exact ⟨t-n,by omega,Structural.InCone_trans n C tc cone⟩
  have gateMem : gateAt C j ∈ C.gates := by
    rw [Semantic.gateAt_eq C j hj]
    exact List.getElem_mem _
  obtain ⟨l,r,ins⟩ := List.length_eq_two.mp (ao.2.2 _ gateMem)
  have children (t : Nat) (member : t ∈ (gateAt C j).inputs) : P t := by
    by_cases ht : t < n
    · exact Or.inl ht
    · right
      have tn : n ≤ t := by omega
      exact ⟨t-n,by omega,Structural.InCone_of_mem_inputs n C hj ao.2.1
        (by simpa [Nat.add_sub_of_le tn] using member)⟩
  change wval C (pairInput a b) (n+j) = true at accepted
  rw [wire_gate C ao _ j hj,op,ins] at accepted
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    id_eq,Bool.and_true,Bool.and_eq_true] at accepted
  obtain ⟨u,_,lu,lv⟩ := active_pair_vector C ao P a b closed l (children l (by simp [ins])) accepted.1
  obtain ⟨v,_,ru,rv⟩ := active_pair_vector C ao P a b closed r (children r (by simp [ins])) accepted.2
  have distinct : u.val ≠ v.val := by
    intro same
    have uv : u = v := Fin.ext same
    subst v
    have yes : gateVal n C j (fun i => decide (i = u)) = true := by
      change wval C _ (n+j) = true
      rw [wire_gate C ao _ j hj,op,ins]
      simp [GateOp.eval,lu,ru]
    have bad := below _ yes
    rw [graph_unit_false] at bad
    contradiction
  have vec : capAdd 1 (uvec [a.val,b.val] u.val) (uvec [a.val,b.val] v.val) ∈
      (readVectors C n [a.val,b.val] 1).getD (n+j) [] := by
    rw [readVectors_getD_gate n C [a.val,b.val] 1 ao.2.1 j hj]
    dsimp only
    rw [op,ins]
    simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil]
    apply mem_andStep _ rv
    rw [←capAdd_zero_uvec [a.val,b.val] u.val]
    exact mem_andStep (List.mem_singleton_self _) lv
  change ((readVectors C n [a.val,b.val] 1).getD (n+j) []).any _ = true
  rw [List.any_eq_true]
  refine ⟨_,vec,?_⟩
  rw [List.all_eq_true]
  intro c hc
  exact decide_eq_true (mem_capAdd_uvec_le_one [a.val,b.val] u.val v.val distinct c hc)

lemma active_nested_and {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.and) (below : BelowF G C j)
    (a b : Fin n) (accepted : gateVal n C j (pairInput a b) = true)
    (twice : ReadTwiceAt n C j a b) :
    ∃ i, InCone n C i j ∧ (gateAt C i).op = GateOp.and ∧
      gateVal n C i (pairInput a b) = true := by
  by_contra absent
  push_neg at absent
  have once := no_active_nested_read_once G C ao j hj op below a b absent accepted
  exact Bool.noConfusion (twice.symm.trans once)

lemma core_has_active_nested_and {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (core : IsCore G C j) :
    ∃ (a b : Fin n) (i : Nat), G.Adj a b ∧ gateVal n C j (pairInput a b) = true ∧
      ReadTwiceAt n C j a b ∧ InCone n C i j ∧ (gateAt C i).op = GateOp.and ∧
      gateVal n C i (pairInput a b) = true := by
  obtain ⟨a,b,edge,accepted,twice⟩ := core.2.2.2
  obtain ⟨i,cone,op,value⟩ := active_nested_and G C ao j core.1
    (core_is_and G C ao j core) core.2.1.1 a b accepted twice
  exact ⟨a,b,i,edge,accepted,twice,cone,op,value⟩

end PEqualNP.Outside.L_meta_2962.ActiveNested
