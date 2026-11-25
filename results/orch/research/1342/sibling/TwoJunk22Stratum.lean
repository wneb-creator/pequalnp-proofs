import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1342.TwoJunkWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A checked near witness: size22, not the posted size21 conclusion.
def twoJunk22 : Circuit :=
  ⟨[⟨GateOp.or, [0, 8]⟩,
    ⟨GateOp.or, [4, 9]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.and, [16, 17]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [3, 18]⟩,
    ⟨GateOp.and, [19, 20]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.and, [1, 22]⟩,
    ⟨GateOp.or, [2, 14]⟩,
    ⟨GateOp.and, [5, 24]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [26, 4]⟩,
    ⟨GateOp.and, [10, 27]⟩,
    ⟨GateOp.or, [15, 21]⟩,
    ⟨GateOp.or, [29, 23]⟩,
    ⟨GateOp.or, [30, 25]⟩,
    ⟨GateOp.or, [31, 28]⟩], 32⟩

theorem twoJunk22_mono : Monotone2 twoJunk22 := by
  simp [Monotone2, twoJunk22]

theorem twoJunk22_size : twoJunk22.size = 22 := rfl

theorem twoJunk22_ao2 : PEqualNP.TopForm.IsAO2 11 twoJunk22 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem twoJunk22_exact : ∀ x : Fin 11 → Bool,
  twoJunk22.eval (List.ofFn x) = true ↔
  ∃ u v : Fin 11, (u.val, v.val) ∈
    ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true := by
  intro x
  have identity (a b c d : Prop) :
      ((b ∨ a) ∧ (d ∨ c)) ∧ (a ∨ c) ↔ (a ∧ c ∨ a ∧ d ∨ b ∧ c) := by
    tauto
  have second (a b c d e : Prop) :
      (a ∨ b) ∧ (c ∨ ((b ∨ d) ∧ (a ∨ e))) ↔
        (a ∧ c ∨ b ∧ c ∨ a ∧ b ∨ a ∧ d ∨ b ∧ e) := by
    tauto
  simp [twoJunk22, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, Fin.exists_fin_succ]
  rw [identity, second]
  simp only [and_or_left]
  apply Iff.of_eq
  ac_rfl

def tail19 : Circuit := ⟨twoJunk22.gates.drop 3, twoJunk22.output⟩

theorem tail19_mono : Monotone2 tail19 := by
  simp [Monotone2, tail19, twoJunk22]

theorem tail19_size : tail19.size = 19 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem tail19_exact : ∀ x : Fin 11 → Bool,
  tail19.eval (List.ofFn x ++
    [x 0 || x 8, x 4 || x 9, (x 0 || x 8) && (x 4 || x 9)]) = true ↔
  ∃ u v : Fin 11, (u.val, v.val) ∈
    ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true := by
  intro x
  have eq : tail19.eval (List.ofFn x ++
      [x 0 || x 8, x 4 || x 9, (x 0 || x 8) && (x 4 || x 9)]) =
      twoJunk22.eval (List.ofFn x) := by
    simp [tail19, twoJunk22, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]
  rw [eq]
  exact twoJunk22_exact x

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def edges : List (ℕ × ℕ) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

abbrev graph : SimpleGraph (Fin 11) := edgeGraph 11 edges

theorem graph_spec (x : Fin 11 → Bool) :
    graphFun graph ∅ x = true ↔
      ∃ u v : Fin 11, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨u,v,⟨_,h | h⟩,hu,hv⟩
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩
  · rintro ⟨u,v,h,hu,hv⟩
    refine ⟨u,v,⟨?_,Or.inl h⟩,hu,hv⟩
    intro eq
    subst v
    fin_cases u <;> simp [edges] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem clean_tops (j : ℕ) (hj : j ∈ [4,10,12,14,17]) (x : Fin 11 → Bool)
    (hv : gateVal 11 twoJunk22 j x = true) :
    twoJunk22.eval (List.ofFn x) = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp_all [gateVal, twoJunk22, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

theorem dirty_two : IsDirtyAnd 11 graph twoJunk22 2 := by
  refine ⟨rfl, by decide, pairInput (0 : Fin 11) 4, ?_, ?_⟩ <;> decide

theorem dirty_seven : IsDirtyAnd 11 graph twoJunk22 7 := by
  refine ⟨rfl, by decide, pairInput (9 : Fin 11) 10, ?_, ?_⟩ <;> decide

theorem twoJunk22_junk : junk graph twoJunk22 = {2,7} := by
  ext j
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hj,hdirty⟩
    have inds : j = 2 ∨ j = 4 ∨ j = 7 ∨ j = 10 ∨ j = 12 ∨ j = 14 ∨ j = 17 := by
      have hop := hdirty.1
      change j < 22 at hj
      interval_cases j <;> simp_all [twoJunk22, gateAt]
    rcases inds with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · obtain ⟨_,x,hx,hn⟩ := hdirty.2
      have hout := clean_tops 4 (by simp) x hx
      have hg := (graph_spec x).2 ((twoJunk22_exact x).1 hout)
      simp_all
    · exact Or.inr rfl
    · obtain ⟨_,x,hx,hn⟩ := hdirty.2
      have hout := clean_tops 10 (by simp) x hx
      have hg := (graph_spec x).2 ((twoJunk22_exact x).1 hout)
      simp_all
    · obtain ⟨_,x,hx,hn⟩ := hdirty.2
      have hout := clean_tops 12 (by simp) x hx
      have hg := (graph_spec x).2 ((twoJunk22_exact x).1 hout)
      simp_all
    · obtain ⟨_,x,hx,hn⟩ := hdirty.2
      have hout := clean_tops 14 (by simp) x hx
      have hg := (graph_spec x).2 ((twoJunk22_exact x).1 hout)
      simp_all
    · obtain ⟨_,x,hx,hn⟩ := hdirty.2
      have hout := clean_tops 17 (by simp) x hx
      have hg := (graph_spec x).2 ((twoJunk22_exact x).1 hout)
      simp_all
  · rintro (rfl | rfl)
    · exact ⟨by decide, dirty_two⟩
    · exact ⟨by decide, dirty_seven⟩

theorem twoJunk22_junk_card : (junk graph twoJunk22).card = 2 := by
  rw [twoJunk22_junk]
  decide

end PEqualNP.Outside.L_meta_1342.TwoJunkWitness
