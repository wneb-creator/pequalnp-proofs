import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.ReachBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n+k) g ↔ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n+k ∧ OrReaches n C i g)) := by
  rw [orReaches_iff]
  simp only [hk,true_and]

lemma reach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n+k) k := (reach_iff n C k k hk).mpr (Or.inl rfl)

lemma reach_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → n+g ≤ w ∧ w < n+C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    obtain ⟨hk,h⟩ := (orReaches_iff n C k g).mp hr
    refine ⟨?_,by omega⟩
    rcases h with rfl | ⟨_,u,_,hu,hr⟩
    · omega
    · have hh := (ih u hu hr).1
      omega

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

lemma orIn_input (n : ℕ) (C : Circuit) (u : Fin n) : orIn n C u.val = {u} := by
  ext v
  rw [mem_orIn,Finset.mem_singleton]
  constructor
  · rintro (h | ⟨j,_,hr,_,_⟩)
    · exact Fin.ext h
    · have h := hr.1
      have hu := u.isLt
      omega
  · intro h
    subst v
    exact Or.inl rfl

lemma gateAt_append_old (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
  simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]

lemma gateAt_append_new (gs : List Gate) (g : Gate) : gateAt ⟨gs++[g],0⟩ gs.length = g := by
  simp [gateAt,List.getD_eq_getElem?_getD]

lemma reaches_append_old (n : ℕ) (gs : List Gate) (g : Gate) (w j : ℕ)
    (hw : w < n+gs.length) :
    OrReaches n ⟨gs++[g],0⟩ w j ↔ OrReaches n ⟨gs,0⟩ w j := by
  by_cases hn : n ≤ w
  · have hk : w-n < gs.length := by omega
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
    unfold OrReaches orSets
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,orStep]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : w-n < (gs.foldl (orStep n) []).length)]
  · simp only [OrReaches,hn,false_and]

lemma orIn_append_old (n : ℕ) (gs : List Gate) (g : Gate) (w : ℕ)
    (hw : w < n+gs.length) :
    orIn n ⟨gs++[g],0⟩ w = orIn n ⟨gs,0⟩ w := by
  ext v
  rw [mem_orIn,mem_orIn]
  constructor
  · rintro (h | ⟨j,hj,hr,hop,hin⟩)
    · exact Or.inl h
    · have hj' : j < gs.length := by
        have h := (reach_bound n ⟨gs++[g],0⟩ j w hr).1
        omega
      rw [gateAt_append_old gs g j hj'] at hop hin
      exact Or.inr ⟨j,hj',(reaches_append_old n gs g w j hw).mp hr,hop,hin⟩
  · rintro (h | ⟨j,hj,hr,hop,hin⟩)
    · exact Or.inl h
    · rw [← gateAt_append_old gs g j hj] at hop hin
      exact Or.inr ⟨j,by simpa using Nat.lt_succ_of_lt hj,(reaches_append_old n gs g w j hw).mpr hr,hop,hin⟩

lemma orIn_and (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : orIn n C (n+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_orIn n C (n+j) v).mp hv with h | ⟨k,hk,hr,hko,_⟩
  · have hv := v.isLt
    omega
  · rcases (reach_iff n C j k hj).mp hr with h | ⟨hjo,_⟩
    · subst k
      rw [hop] at hko
      cases hko
    · rw [hop] at hjo
      cases hjo

lemma orIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, mem_orIn, mem_orIn, mem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (reach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, reach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (reach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, reach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (reach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma orIn_append_and (n : ℕ) (gs : List Gate) (u v : ℕ) :
    orIn n ⟨gs++[⟨GateOp.and,[u,v]⟩],0⟩ (n+gs.length) = ∅ := by
  apply orIn_and n _ gs.length (by simp)
  rw [gateAt_append_new]

lemma orIn_append_or (n : ℕ) (gs : List Gate) (u v : ℕ)
    (hu : u < n+gs.length) (hv : v < n+gs.length) :
    orIn n ⟨gs++[⟨GateOp.or,[u,v]⟩],0⟩ (n+gs.length) =
      orIn n ⟨gs,0⟩ u ∪ orIn n ⟨gs,0⟩ v := by
  rw [orIn_or n _ gs.length u v (by simp) (by rw [gateAt_append_new])
    (by rw [gateAt_append_new]) hu hv]
  rw [orIn_append_old n gs _ u hu,orIn_append_old n gs _ v hv]

def binary (b : Bool) (u v : ℕ) : Gate := ⟨if b then GateOp.and else GateOp.or,[u,v]⟩

lemma orIn_append_binary (n : ℕ) (gs : List Gate) (b : Bool) (u v : ℕ)
    (hu : u < n+gs.length) (hv : v < n+gs.length) :
    orIn n ⟨gs++[binary b u v],0⟩ (n+gs.length) =
      if b then ∅ else orIn n ⟨gs,0⟩ u ∪ orIn n ⟨gs,0⟩ v := by
  cases b
  · exact orIn_append_or n gs u v hu hv
  · exact orIn_append_and n gs u v

end PEqualNP.Outside.L_meta_4970_aux.ReachBridge
