
namespace PEqualNP.Outside.L_meta_2962.Nested
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2962.Semantic PEqualNP.Outside.L_meta_2962.Vectors

lemma pure_pair_vector {n : Nat} (C : Circuit) (ao : IsAO2 n C) (P : Nat → Prop)
    (closed : ∀ w, P w → w < n ∨ ∃ j < C.gates.length,
      w = n+j ∧ (gateAt C j).op = GateOp.or ∧ ∀ t ∈ (gateAt C j).inputs, P t)
    (a b : Fin n) : ∀ w, P w → wval C (pairInput a b) w = true →
      ∃ u : Fin n, (u = a ∨ u = b) ∧
        wval C (fun i => decide (i = u)) w = true ∧
        uvec [a.val,b.val] u.val ∈ (readVectors C n [a.val,b.val] 1).getD w [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    rcases closed w hw with leaf | ⟨j,hj,rfl,op,children⟩
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

lemma no_nested_read_once {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.and) (below : BelowF G C j)
    (nonested : ∀ i, InCone n C i j → (gateAt C i).op ≠ GateOp.and)
    (a b : Fin n) (accepted : gateVal n C j (pairInput a b) = true) :
    readsAtMost (atGate n C j) n [a.val,b.val] 1 = true := by
  let P : Nat → Prop := fun w => w < n ∨ ∃ i, w = n+i ∧ InCone n C i j
  have closed : ∀ w, P w → w < n ∨ ∃ i < C.gates.length,
      w = n+i ∧ (gateAt C i).op = GateOp.or ∧ ∀ t ∈ (gateAt C i).inputs, P t := by
    intro w hw
    rcases hw with leaf | ⟨i,rfl,cone⟩
    · exact Or.inl leaf
    · right
      have hi := Structural.InCone_lt_len n C cone
      have mem : gateAt C i ∈ C.gates := by
        rw [Semantic.gateAt_eq C i hi]
        exact List.getElem_mem _
      refine ⟨i,hi,rfl,(ao.1 _ mem).resolve_left (nonested i cone),?_⟩
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
  obtain ⟨u,_,lu,lv⟩ := pure_pair_vector C ao P closed a b l (children l (by simp [ins])) accepted.1
  obtain ⟨v,_,ru,rv⟩ := pure_pair_vector C ao P closed a b r (children r (by simp [ins])) accepted.2
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

lemma core_has_nested_and {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (j : Nat) (core : IsCore G C j) :
    ∃ i, InCone n C i j ∧ (gateAt C i).op = GateOp.and := by
  by_contra absent
  push_neg at absent
  obtain ⟨a,b,_,accepted,twice⟩ := core.2.2.2
  have once := no_nested_read_once G C ao j core.1 (core_is_and G C ao j core)
    core.2.1.1 absent a b accepted
  exact Bool.noConfusion (twice.symm.trans once)

end PEqualNP.Outside.L_meta_2962.Nested
