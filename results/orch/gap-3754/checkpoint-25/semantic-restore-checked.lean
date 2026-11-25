import PEqualNP.Defs
-- Wire evaluation helpers are adapted from L_meta_5779 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.Ledger
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm


lemma gate_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) : ∃ a b,(gateAt C j).inputs=[a,b] := by
  have hm : gateAt C j∈C.gates := by rw [gateAt_eq_getElem C j hj];exact List.getElem_mem hj
  exact List.length_eq_two.mp (hAO.2.2 _ hm)

lemma wire_all_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w,w<n+C.gates.length → wireVal n C w (fun _ => true)=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hinput : w<n
    · rw [wireVal_input n C _ w hinput]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      obtain ⟨a,b,hab⟩ := gate_two n C hAO k hk
      have ha : a<n+k := hAO.2.1 k hk a (by simp [hab])
      have hb : b<n+k := hAO.2.1 k hk b (by simp [hab])
      have hva := ih a ha (by omega)
      have hvb := ih b hb (by omega)
      have hm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rw [wireVal_gate n C _ k hk hAO.2.1,hab]
      rcases hAO.1 _ hm with hop | hop <;> simp [hop,GateOp.eval,hva,hvb]

lemma operand_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (b : Fin 2) : opnd C j b<n+j := by
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  have hb : opnd C j b∈(gateAt C j).inputs := by
    fin_cases b <;> simp [opnd,hac]
  exact hAO.2.1 j hj _ hb

lemma below_wire_implicant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w<n+C.gates.length)
    (hbelow : ∀ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true → graphFun G ∅ x=true) :
    PEqualNP.Core.IsImpWire G C w := by
  refine ⟨hbelow,fun _ => true,?_⟩
  exact wire_all_true n C hAO w hw

lemma fixed_or_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j)
    (hop : (gateAt C j).op=GateOp.or) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  by_contra hn
  apply hfixed
  refine ⟨j,hcone.1,b,hcone,hop,hn,?_⟩
  exact below_wire_implicant G C hAO _ ((operand_bound n C hAO j hcone.1 b).trans (Nat.add_lt_add_left hcone.1 n)) hbelow

lemma and_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hop : (gateAt C j).op=GateOp.and) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  intro x hx
  apply hbelow x
  change wireVal n C (n+j) x=true at hx
  rw [wireVal_gate n C x j hj hAO.2.1,hop] at hx
  simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hx
  apply hx
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  fin_cases b <;> simp [opnd,hac]

lemma fixed_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  have hm : gateAt C j∈C.gates := by
    rw [gateAt_eq_getElem C j hcone.1];exact List.getElem_mem hcone.1
  rcases hAO.1 _ hm with hop | hop
  · exact and_reader_closed G C hAO j hcone.1 hop b hbelow
  · exact fixed_or_reader_closed G C hAO hfixed j hcone hop b hbelow

lemma dirty_operand_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j) (b : Fin 2) :
    ∃ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x (opnd C j b)=true ∧ graphFun G ∅ x=false := by
  classical
  by_contra hn
  apply hdirty
  apply fixed_reader_closed G C hAO hfixed j hcone b
  intro x hx
  cases hf : graphFun G ∅ x with
  | false => exact False.elim (hn ⟨x,hx,hf⟩)
  | true => rfl
lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi


lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j<C.gates.length)
    (h : InCone n C i j) : i<j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hw,hnw,hwj,hi⟩ := (inCone_iff n C i j hj).mp h
    rcases hi with hi | hi
    · omega
    · have hh := ih (w-n) (by omega) (by omega) hi
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) (i j k : ℕ) (hk : k<C.gates.length)
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w,hw,hnw,hwk,hj⟩ := (inCone_iff n C j k hk).mp hjk
    apply (inCone_iff n C i k hk).mpr
    refine ⟨w,hw,hnw,hwk,Or.inr ?_⟩
    rcases hj with rfl | hj
    · exact hij
    · exact ih (w-n) (by omega) (by omega) hj

lemma output_cone_ancestor (n : ℕ) (C : Circuit) (i j : ℕ)
    (hcone : PEqualNP.Core.InOutputCone n C j) (hij : InCone n C i j) :
    PEqualNP.Core.InOutputCone n C i := by
  have hi := (inCone_lt n C i j hcone.1 hij).trans hcone.1
  refine ⟨hi,Or.inr ?_⟩
  rcases hcone.2 with heq | ⟨hle,hjc⟩
  · refine ⟨by omega,?_⟩
    simpa only [heq,Nat.add_sub_cancel_left] using hij
  · refine ⟨hle,?_⟩
    have hout : C.output-n<C.gates.length := by
      by_contra hbad
      have hz : (cones n C).getD (C.output-n) []=[] := by
        apply List.getD_eq_default
        have hlen : (cones n C).length=C.gates.length := by
          simpa [cones] using foldl_coneStep_length n C.gates []
        omega
      change j∈(cones n C).getD (C.output-n) [] at hjc
      rw [hz] at hjc
      simp at hjc
    exact inCone_trans n C i j (C.output-n) hout hij hjc

lemma mem_inputs_opnd (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (w : ℕ) (hw : w∈(gateAt C j).inputs) :
    ∃ b : Fin 2,opnd C j b=w := by
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  simp [hac] at hw
  rcases hw with rfl | rfl
  · exact ⟨0,by simp [opnd,hac]⟩
  · exact ⟨1,by simp [opnd,hac]⟩

lemma fixed_reader_closed_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j)
    (w : ℕ) (hw : w∈(gateAt C j).inputs)
    (hbelow : ∀ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  obtain ⟨b,hb⟩ := mem_inputs_opnd n C hAO j hcone.1 w hw
  apply fixed_reader_closed G C hAO hfixed j hcone b
  simpa only [hb] using hbelow

lemma fixed_cone_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C) :
    ∀ j,PEqualNP.Core.InOutputCone n C j → ∀i,InCone n C i j → BelowF G C i → BelowF G C j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hcone i hanc hib
    obtain ⟨w,hw,hnw,hwj,hi⟩ := (inCone_iff n C i j hcone.1).mp hanc
    have hwcone : InCone n C (w-n) j :=
      (inCone_iff n C (w-n) j hcone.1).mpr ⟨w,hw,hnw,hwj,Or.inl rfl⟩
    have hclean : BelowF G C (w-n) := by
      rcases hi with rfl | hi
      · exact hib
      · exact ih (w-n) (by omega) (output_cone_ancestor n C (w-n) j hcone hwcone) i hi hib
    apply fixed_reader_closed_mem G C hAO hfixed j hcone w hw
    intro x hx
    apply hclean x
    have he : n+(w-n)=w := by omega
    simpa only [gateVal,PEqualNP.ReadTwo.wval,he] using hx

lemma earliest_dirty_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (i : ℕ) (hi : InCone n C i j) : (gateAt C i).op≠GateOp.and := by
  intro hand
  exact hdirty (fixed_cone_closed G C hAO hfixed j hcone i hi
    (hearlier i (inCone_lt n C i j hcone.1 hi) hand))

lemma earliest_dirty_ancestor_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (i : ℕ) (hi : InCone n C i j) : (gateAt C i).op=GateOp.or := by
  have hil := (inCone_lt n C i j hcone.1 hi).trans hcone.1
  have him : gateAt C i∈C.gates := by rw [gateAt_eq_getElem C i hil];exact List.getElem_mem hil
  rcases hAO.1 _ him with hand | hor
  · exact (earliest_dirty_no_and_ancestor G C hAO hfixed j hcone hdirty hearlier i hi hand).elim
  · exact hor


lemma gate_eval_monotone (g : Gate) (hg : g.op=GateOp.and ∨ g.op=GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀i∈g.inputs,x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
    intro h i hi
    exact hxy i hi (h i hi)
  · rw [hg]
    simp only [GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i hi h⟩

lemma wire_monotone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀i,x i=true → y i=true) :
    ∀w,w<n+C.gates.length → wireVal n C w x=true → wireVal n C w y=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hinput : w<n
    · rw [wireVal_input n C x w hinput] at hx
      rw [wireVal_input n C y w hinput]
      exact hxy _ hx
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      have hm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rw [wireVal_gate n C x k hk hAO.2.1] at hx
      rw [wireVal_gate n C y k hk hAO.2.1]
      apply gate_eval_monotone (gateAt C k) (hAO.1 _ hm)
        (fun u => wireVal n C u x) (fun u => wireVal n C u y) _ hx
      intro u hu huv
      have hub := hAO.2.1 k hk u hu
      exact ih u hub (by omega) huv

lemma wire_or_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hop : (gateAt C j).op=GateOp.or)
    (w : ℕ) (hw : w∈(gateAt C j).inputs) (x : Fin n → Bool)
    (hx : wireVal n C w x=true) : wireVal n C (n+j) x=true := by
  rw [wireVal_gate n C x j hj hAO.2.1,hop]
  simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
  exact ⟨w,hw,hx⟩

def singletonInput {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i=v)

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => wireVal n C w (singletonInput v)=true

lemma or_cone_singleton_witness (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀j,j<C.gates.length → (gateAt C j).op=GateOp.or →
      (∀i,InCone n C i j → (gateAt C i).op=GateOp.or) →
      ∀x : Fin n → Bool,wireVal n C (n+j) x=true →
        ∃v : Fin n,x v=true ∧ wireVal n C (n+j) (singletonInput v)=true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hop hanc x hx
    rw [wireVal_gate n C x j hj hAO.2.1,hop] at hx
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx
    obtain ⟨w,hw,hwx⟩ := hx
    have hwj := hAO.2.1 j hj w hw
    by_cases hinput : w<n
    · refine ⟨⟨w,hinput⟩,?_,?_⟩
      · simpa only [wireVal_input n C x w hinput] using hwx
      · apply wire_or_true n C hAO j hj hop w hw
        rw [wireVal_input n C _ w hinput]
        simp [singletonInput]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hkj : k<j := by omega
      have hk : k<C.gates.length := by omega
      have hcone : InCone n C k j :=
        (inCone_iff n C k j hj).mpr ⟨n+k,hw,by omega,hwj,Or.inl (by omega)⟩
      obtain ⟨v,hv,hvg⟩ := ih k hkj hk (hanc k hcone)
        (fun i hi => hanc i (inCone_trans n C i k j hj hi hcone)) x hwx
      exact ⟨v,hv,wire_or_true n C hAO j hj hop (n+k) hw _ hvg⟩

lemma earliest_dirty_operand_singleton_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (b : Fin 2) (x : Fin n → Bool)
    (hx : wireVal n C (opnd C j b) x=true) :
    ∃v : Fin n,x v=true ∧ wireVal n C (opnd C j b) (singletonInput v)=true := by
  let w := opnd C j b
  have hwj : w<n+j := operand_bound n C hAO j hcone.1 b
  change wireVal n C w x=true at hx
  by_cases hinput : w<n
  · refine ⟨⟨w,hinput⟩,?_,?_⟩
    · simpa only [wireVal_input n C x w hinput] using hx
    · change wireVal n C w (singletonInput ⟨w,hinput⟩)=true
      rw [wireVal_input n C _ w hinput]
      simp [singletonInput]
  · obtain ⟨k,hweq⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by have hj:=hcone.1;omega
    have hwmem : w∈(gateAt C j).inputs := by
      obtain ⟨a,c,hac⟩ := gate_two n C hAO j hcone.1
      fin_cases b <;> simp [w,opnd,hac]
    have hkj : InCone n C k j :=
      (inCone_iff n C k j hcone.1).mpr ⟨w,hwmem,by omega,hwj,Or.inl (by omega)⟩
    have hkOR := earliest_dirty_ancestor_or G C hAO hfixed j hcone hdirty hearlier k hkj
    have hall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or := by
      intro i hi
      exact earliest_dirty_ancestor_or G C hAO hfixed j hcone hdirty hearlier i
        (inCone_trans n C i k j hcone.1 hi hkj)
    change wireVal n C w x=true at hx
    rw [hweq] at hx
    have hh := or_cone_singleton_witness n C hAO k hk hkOR hall x hx
    simpa only [←hweq] using hh

lemma earliest_dirty_operand_exact_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C j b) x=
      decide (∃v∈singletonSupport n C (opnd C j b),x v=true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    obtain ⟨v,hv,hvs⟩ := earliest_dirty_operand_singleton_witness G C hAO hfixed j hcone hdirty hearlier b x hx
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvs⟩,hv⟩
  · rintro ⟨v,hv,hvx⟩
    have hb := (Finset.mem_filter.mp hv).2
    apply wire_monotone n C hAO (singletonInput v) x _ (opnd C j b)
      ((operand_bound n C hAO j hcone.1 b).trans (Nat.add_lt_add_left hcone.1 n)) hb
    intro i hi
    have he : i=v := by simpa [singletonInput] using hi
    simpa only [he] using hvx

end PEqualNP.Outside.L_meta_3754.Ledger

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- This relation describes the three aliases before contraction changes any wire indices.
def AliasSem (n : ℕ) (C P : Circuit) (j p B g : ℕ) (v : Fin n) : Prop :=
  ∀ (x : Fin n → Bool) k, k<C.gates.length →
    wireVal n P (n+k) x =
      if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun w => wireVal n P w x)

lemma aliases_le {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hp : p<n+j)
    (hsem : AliasSem n C P j p B g v)
    (hjBelow : ∀ x, wireVal n C p x=true → gateVal n C j x=true)
    (hBBelow : ∀ x, x v=true → gateVal n C B x=true)
    (hgBelow : ∀ x, x v=true → gateVal n C g x=true) :
    ∀ (x : Fin n → Bool) w, w<n+C.gates.length → wireVal n P w x=true → wireVal n C w x=true := by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnow
    by_cases hraw : w<n
    · simpa only [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw] using hnow
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    rw [hsem x k hk] at hnow
    by_cases hkg : k=g ∨ k=B
    · rw [if_pos hkg] at hnow
      rcases hkg with rfl | rfl
      · exact hgBelow x hnow
      · exact hBBelow x hnow
    rw [if_neg hkg] at hnow
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl] at hnow
      exact hjBelow x (ih p hp (by omega) hnow)
    rw [if_neg hkj] at hnow
    rw [Ledger.wireVal_gate n C x k hk hC.2.1]
    have hm : gateAt C k∈C.gates := by
      rw [Ledger.gateAt_eq_getElem C k hk]
      exact List.getElem_mem hk
    apply Ledger.gate_eval_monotone (gateAt C k) (hC.1 _ hm) _ _ ?_ hnow
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)

lemma aliases_agree_except_private {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hp : p<n+j) (hpB : p≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (x : Fin n → Bool) (hxv : x v=false)
    (hjEq : gateVal n C j x=wireVal n C p x) (hgZero : gateVal n C g x=false) :
    ∀ w,w<n+C.gates.length → w≠n+B → wireVal n P w x=wireVal n C w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwB
    by_cases hraw : w<n
    · rw [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw]
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have hkB : k≠B := by omega
    rw [hsem x k hk]
    by_cases hkg : k=g
    · subst k
      rw [if_pos (Or.inl rfl),hxv]
      exact hgZero.symm
    rw [if_neg (by simp [hkg,hkB])]
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl,ih p hp (by omega) hpB]
      exact hjEq.symm
    rw [if_neg hkj,Ledger.wireVal_gate n C x k hk hC.2.1]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)
      (fun h => hkg (hprivate k hk (h ▸ hu)))

lemma aliases_agree_before_g {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hg : g<C.gates.length) (hp : p<n+j) (hpB : p≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (x : Fin n → Bool) (hxv : x v=false)
    (hjEq : gateVal n C j x=wireVal n C p x) :
    ∀ w,w<n+g → w≠n+B → wireVal n P w x=wireVal n C w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwB
    by_cases hraw : w<n
    · rw [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw]
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have hkB : k≠B := by omega
    have hkg : k≠g := by omega
    rw [hsem x k hk,if_neg (by simp [hkg,hkB])]
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl,ih p hp (by omega) hpB]
      exact hjEq.symm
    rw [if_neg hkj,Ledger.wireVal_gate n C x k hk hC.2.1]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)
      (fun h => hkg (hprivate k hk (h ▸ hu)))

end PEqualNP.Outside.L_meta_3754.PatchSemantics


namespace PEqualNP.Outside.L_meta_3754.Loss

lemma and_false {a b : Bool} (h : (a && b) = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

lemma or_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

lemma loss_propagates_label
    (n N j B g : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (old now : ℕ → Bool) (label : ℕ → Prop)
    (hback : ∀ k < N, a k < n+k ∧ b k < n+k)
    (hraw : ∀ w < n, old w = now w)
    (hstart : label (n+j))
    (hB : now (n+B) = true) (hg : now (n+g) = true)
    (hgate : ∀ k < N, k ≠ j → k ≠ B → k ≠ g →
      old (n+k) = (if isAnd k then old (a k) && old (b k) else old (a k) || old (b k)) ∧
      now (n+k) = (if isAnd k then now (a k) && now (b k) else now (a k) || now (b k)))
    (hor : ∀ k < N, isAnd k = false → label (a k) ∨ label (b k) → label (n+k))
    (hand : ∀ k < N, k ≠ j → k ≠ B → k ≠ g → isAnd k = true →
      (label (a k) → old (b k) = false) ∧ (label (b k) → old (a k) = false)) :
    ∀ w < n+N, old w = true → now w = false → label w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ho hn
    by_cases hwi : w < n
    · have h := hraw w hwi
      rw [ho,hn] at h
      cases h
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < N := by omega
    by_cases hkj : k = j
    · simpa [hkj] using hstart
    by_cases hkB : k = B
    · subst k; rw [hB] at hn; cases hn
    by_cases hkg : k = g
    · subst k; rw [hg] at hn; cases hn
    obtain ⟨ha,hb⟩ := hback k hk
    obtain ⟨hgo,hgn⟩ := hgate k hk hkj hkB hkg
    cases hop : isAnd k
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∨ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∧ now (b k) = false := or_false (by simpa using hn)
      apply hor k hk hop
      rcases hv with hv | hv
      · exact Or.inl (ih (a k) ha (by omega) hv hn'.1)
      · exact Or.inr (ih (b k) hb (by omega) hv hn'.2)
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∧ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∨ now (b k) = false := and_false (by simpa using hn)
      obtain ⟨hga,hgb⟩ := hand k hk hkj hkB hkg hop
      exfalso
      rcases hn' with hn' | hn'
      · have h := hga (ih (a k) ha (by omega) hv.1 hn')
        rw [hv.2] at h
        cases h
      · have h := hgb (ih (b k) hb (by omega) hv.2 hn')
        rw [hv.1] at h
        cases h

lemma loss_from_three_labels
    (n N j B g : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (old now : ℕ → Bool) (label : ℕ → Prop)
    (hback : ∀ k < N, a k < n+k ∧ b k < n+k)
    (hraw : ∀ w < n, old w = now w)
    (hstart : label (n+j))
    (hB : label (n+B)) (hg : label (n+g))
    (hgate : ∀ k < N, k ≠ j → k ≠ B → k ≠ g →
      old (n+k) = (if isAnd k then old (a k) && old (b k) else old (a k) || old (b k)) ∧
      now (n+k) = (if isAnd k then now (a k) && now (b k) else now (a k) || now (b k)))
    (hor : ∀ k < N, isAnd k = false → label (a k) ∨ label (b k) → label (n+k))
    (hand : ∀ k < N, k ≠ j → k ≠ B → k ≠ g → isAnd k = true →
      (label (a k) → old (b k) = false) ∧ (label (b k) → old (a k) = false)) :
    ∀ w < n+N, old w = true → now w = false → label w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ho hn
    by_cases hwi : w < n
    · have h := hraw w hwi
      rw [ho,hn] at h
      cases h
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < N := by omega
    by_cases hkj : k = j
    · simpa [hkj] using hstart
    by_cases hkB : k = B
    · simpa [hkB] using hB
    by_cases hkg : k = g
    · simpa [hkg] using hg
    obtain ⟨ha,hb⟩ := hback k hk
    obtain ⟨hgo,hgn⟩ := hgate k hk hkj hkB hkg
    cases hop : isAnd k
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∨ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∧ now (b k) = false := or_false (by simpa using hn)
      apply hor k hk hop
      rcases hv with hv | hv
      · exact Or.inl (ih (a k) ha (by omega) hv hn'.1)
      · exact Or.inr (ih (b k) hb (by omega) hv hn'.2)
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∧ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∨ now (b k) = false := and_false (by simpa using hn)
      obtain ⟨hga,hgb⟩ := hand k hk hkj hkB hkg hop
      exfalso
      rcases hn' with hn' | hn'
      · have h := hga (ih (a k) ha (by omega) hv.1 hn')
        rw [hv.2] at h
        cases h
      · have h := hgb (ih (b k) hb (by omega) hv.2 hn')
        rw [hv.1] at h
        cases h

end PEqualNP.Outside.L_meta_3754.Loss

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Classical in
lemma gate_bin {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k<C.gates.length)
    (f : ℕ → Bool) :
    (gateAt C k).op.eval ((gateAt C k).inputs.map f) =
      if decide ((gateAt C k).op=GateOp.and) then f (opnd C k 0) && f (opnd C k 1)
      else f (opnd C k 0) || f (opnd C k 1) := by
  obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hC k hk
  have hm : gateAt C k∈C.gates := by
    rw [Ledger.gateAt_eq_getElem C k hk]
    exact List.getElem_mem hk
  rcases hC.1 _ hm with hop | hop <;> simp [hab,hop,opnd,GateOp.eval]

lemma alias_middle_preserved {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length)
    (hsem : AliasSem n C P j p B g v)
    (label : ℕ → Prop) (hstart : label (n+j)) (houtLabel : ¬label C.output)
    (hlabelOR : ∀ k<C.gates.length,(gateAt C k).op=GateOp.or →
      label (opnd C k 0) ∨ label (opnd C k 1) → label (n+k))
    (x : Fin n → Bool) (hxv : x v=true)
    (hguard : ∀ k<C.gates.length,k≠j → k≠B → k≠g → (gateAt C k).op=GateOp.and →
      (label (opnd C k 0) → wireVal n C (opnd C k 1) x=false) ∧
      (label (opnd C k 1) → wireVal n C (opnd C k 0) x=false)) :
    wireVal n C C.output x=true → wireVal n P C.output x=true := by
  classical
  intro hold
  cases hnow : wireVal n P C.output x
  · apply False.elim
    apply houtLabel
    apply Loss.loss_propagates_label n C.gates.length j B g (fun k=>opnd C k 0)
      (fun k=>opnd C k 1) (fun k=>decide ((gateAt C k).op=GateOp.and))
      (fun w=>wireVal n C w x) (fun w=>wireVal n P w x) label ?_ ?_ hstart ?_ ?_ ?_ ?_ ?_
      C.output hout hold hnow
    · intro k hk
      exact ⟨Ledger.operand_bound n C hC k hk 0,Ledger.operand_bound n C hC k hk 1⟩
    · intro w hw
      rw [Ledger.wireVal_input n C x w hw,Ledger.wireVal_input n P x w hw]
    · rw [hsem x B hB,if_pos (Or.inr rfl),hxv]
    · rw [hsem x g hg,if_pos (Or.inl rfl),hxv]
    · intro k hk hkj hkB hkg
      constructor
      · rw [Ledger.wireVal_gate n C x k hk hC.2.1]
        exact gate_bin C hC k hk _
      · rw [hsem x k hk,if_neg (by simp [hkg,hkB]),if_neg hkj]
        exact gate_bin C hC k hk _
    · intro k hk hnotand hlab
      have hm : gateAt C k∈C.gates := by
        rw [Ledger.gateAt_eq_getElem C k hk]
        exact List.getElem_mem hk
      rcases hC.1 _ hm with hand | hor
      · simp [hand] at hnotand
      · exact hlabelOR k hk hor hlab
    · intro k hk hkj hkB hkg hand
      exact hguard k hk hkj hkB hkg (of_decide_eq_true hand)
  · rfl

lemma alias_guarded_preserved {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length)
    (hsem : AliasSem n C P j p B g v)
    (label : ℕ → Prop) (hstart : label (n+j)) (houtLabel : ¬label C.output)
    (hlabelOR : ∀ k<C.gates.length,(gateAt C k).op=GateOp.or →
      label (opnd C k 0) ∨ label (opnd C k 1) → label (n+k))
    (hBLabel : label (n+B)) (hgLabel : label (n+g)) (x : Fin n → Bool)
    (hguard : ∀ k<C.gates.length,k≠j → k≠B → k≠g → (gateAt C k).op=GateOp.and →
      (label (opnd C k 0) → wireVal n C (opnd C k 1) x=false) ∧
      (label (opnd C k 1) → wireVal n C (opnd C k 0) x=false)) :
    wireVal n C C.output x=true → wireVal n P C.output x=true := by
  classical
  intro hold
  cases hnow : wireVal n P C.output x
  · apply False.elim
    apply houtLabel
    apply Loss.loss_from_three_labels n C.gates.length j B g (fun k=>opnd C k 0)
      (fun k=>opnd C k 1) (fun k=>decide ((gateAt C k).op=GateOp.and))
      (fun w=>wireVal n C w x) (fun w=>wireVal n P w x) label ?_ ?_ hstart hBLabel hgLabel ?_ ?_ ?_
      C.output hout hold hnow
    · intro k hk
      exact ⟨Ledger.operand_bound n C hC k hk 0,Ledger.operand_bound n C hC k hk 1⟩
    · intro w hw
      rw [Ledger.wireVal_input n C x w hw,Ledger.wireVal_input n P x w hw]
    · intro k hk hkj hkB hkg
      constructor
      · rw [Ledger.wireVal_gate n C x k hk hC.2.1]
        exact gate_bin C hC k hk _
      · rw [hsem x k hk,if_neg (by simp [hkg,hkB]),if_neg hkj]
        exact gate_bin C hC k hk _
    · intro k hk hnotand hlab
      have hm : gateAt C k∈C.gates := by
        rw [Ledger.gateAt_eq_getElem C k hk]
        exact List.getElem_mem hk
      rcases hC.1 _ hm with hand | hor
      · simp [hand] at hnotand
      · exact hlabelOR k hk hor hlab
    · intro k hk hkj hkB hkg hand
      exact hguard k hk hkj hkB hkg (of_decide_eq_true hand)
  · rfl

end PEqualNP.Outside.L_meta_3754.PatchSemantics

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma graph_from_edge_values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y,(∀ i,x i=true → y i=true) → f x=true → f y=true)
    (hsafe : ∀ x,f x=true → graphFun G ∅ x=true)
    (hedge : ∀ a b,G.Adj a b → f (pairInput a b)=true) : f=graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsafe x
  · intro hx
    simp [graphFun] at hx
    obtain ⟨a,b,hab,ha,hb⟩ := hx
    apply hmono (pairInput a b) x ?_ (hedge a b hab)
    intro i hi
    simp only [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption

lemma three_alias_restoration {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsAO2 n C) (hP : IsAO2 n P)
    (hcomp : circuitFun n C=graphFun G ∅) (hlen : P.gates.length=C.gates.length)
    (j p B g aW : ℕ) (v m : Fin n) (hg : g<C.gates.length)
    (hp : p<n+j) (hpB : p≠n+B) (haW : aW<n+g) (haWB : aW≠n+B)
    (hout : C.output<n+C.gates.length) (houtB : C.output≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (hjval : ∀ x,gateVal n C j x=(x v || wireVal n C p x))
    (hgv : ∀ x,x v=true → gateVal n C g x=true)
    (hBv : ∀ x,x v=true → gateVal n C B x=true)
    (hgA : ∀ x,gateVal n C g x=true → wireVal n C aW x=true)
    (hsafeA : ∀ x,x m=true → wireVal n C aW x=true → graphFun G ∅ x=true)
    (hlow : ∀ a b,G.Adj a b → pairInput a b v=false → pairInput a b m=false →
      gateVal n C g (pairInput a b)=true → wireVal n P C.output (pairInput a b)=true)
    (hmiddle : ∀ a b,G.Adj a b → pairInput a b v=true → pairInput a b m=false →
      wireVal n P C.output (pairInput a b)=true)
    (hpair : wireVal n P C.output (pairInput v m)=true) :
    ∀ x,(wireVal n P C.output x || (x m && wireVal n P aW x))=graphFun G ∅ x := by
  have haFull : aW<n+C.gates.length := by omega
  have hjBelow : ∀ x,wireVal n C p x=true → gateVal n C j x=true := by
    intro x hx
    rw [hjval x,hx]
    simp
  have hdecrease := aliases_le C P hC j p B g v hp hsem hjBelow hBv hgv
  have hkeepA (x : Fin n → Bool) (hv : x v=false) : wireVal n P aW x=wireVal n C aW x := by
    apply aliases_agree_before_g C P hC j p B g v hg hp hpB hsem hprivate x hv ?_ aW haW haWB
    rw [hjval x,hv]
    simp
  have hmono (w : ℕ) (hw : w<n+C.gates.length) :=
    fun x y hxy => Ledger.wire_monotone n P hP x y hxy w (by simpa [hlen] using hw)
  let Fnew := fun x : Fin n → Bool => wireVal n P C.output x || (x m && wireVal n P aW x)
  have hF : Fnew=graphFun G ∅ := by
    apply graph_from_edge_values G Fnew
    · intro x y hxy hx
      change (wireVal n P C.output x || (x m && wireVal n P aW x))=true at hx
      change (wireVal n P C.output y || (y m && wireVal n P aW y))=true
      simp only [Bool.or_eq_true,Bool.and_eq_true] at hx ⊢
      exact hx.elim (fun h=>Or.inl (hmono C.output hout x y hxy h))
        (fun h=>Or.inr ⟨hxy m h.1,hmono aW haFull x y hxy h.2⟩)
    · intro x hx
      change (wireVal n P C.output x || (x m && wireVal n P aW x))=true at hx
      simp only [Bool.or_eq_true,Bool.and_eq_true] at hx
      rcases hx with hx | ⟨hm,ha⟩
      · have hc := hdecrease x C.output hout hx
        change circuitFun n C x=true at hc
        rwa [hcomp] at hc
      · exact hsafeA x hm (hdecrease x aW haFull ha)
    · intro a b hab
      change (wireVal n P C.output (pairInput a b) ||
        (pairInput a b m && wireVal n P aW (pairInput a b)))=true
      simp only [Bool.or_eq_true,Bool.and_eq_true]
      cases hv : pairInput a b v
      · cases hgd : gateVal n C g (pairInput a b)
        · left
          have he := aliases_agree_except_private C P hC j p B g v hp hpB hsem hprivate
            (pairInput a b) hv (by rw [hjval,hv];simp) hgd C.output hout houtB
          rw [he]
          change circuitFun n C (pairInput a b)=true
          rw [hcomp]
          have he : ∃ u w,G.Adj u w ∧ pairInput a b u=true ∧ pairInput a b w=true :=
            ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
          simpa [graphFun] using he
        · cases hm : pairInput a b m
          · exact Or.inl (hlow a b hab hv hm hgd)
          · exact Or.inr ⟨rfl,by rw [hkeepA _ hv];exact hgA _ hgd⟩
      · cases hm : pairInput a b m
        · exact Or.inl (hmiddle a b hab hv hm)
        · left
          apply hmono C.output hout (pairInput v m) (pairInput a b) ?_ hpair
          intro i hi
          simp only [pairInput,decide_eq_true_eq] at hi
          rcases hi with rfl | rfl <;> assumption
  exact fun x=>congrFun hF x

end PEqualNP.Outside.L_meta_3754.PatchSemantics
