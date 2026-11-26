import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5290_583
    (firstBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 13 ≤ C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (tight : ∀ (u v : Fin 9), 10 * min u.val v.val + max u.val v.val ∈
        ([1,2,6,16,17,18,24,26,34,46,67] : List ℕ) →
      ∀ C : Circuit, FanInTwo C → C.size = 13 → PEqualNP.NotBracket.notCount C = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → (x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} ∨ ∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x6 < x7 ∧ x2 = {x6, x7} ∧ (10 : ℕ) * ↑x6 + ↑x7 ∈ [(1 : ℕ), (2 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (34 : ℕ), (46 : ℕ), (47 : ℕ), (48 : ℕ), (56 : ℕ), (57 : ℕ), (67 : ℕ), (78 : ℕ)]) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) → False := by
  classical
  intro C s fan small hasNot inGood agrees
  let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let fire := fun (x : Fin 9 → Bool) => decide (∃ i ∈ s, x i = true)
  have correct (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4, fire x]) = f x := agrees x
  let paid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  have accounting (E : Circuit) : E.gates.countP paid + PEqualNP.NotBracket.notCount E = E.size := by
    unfold PEqualNP.NotBracket.notCount Circuit.size
    induction E.gates with
    | nil => rfl
    | cons h gs ih =>
      dsimp only [paid] at ih
      cases h with | mk op ins => cases op <;> simp [paid,List.filter_cons] <;> omega
  let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  by_cases degenerate : s.card ≤ 1 ∨ s = {0,4}
  · -- the second extra input copies an existing wire or is constantly false: rewire it away
    let A (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
    obtain ⟨pin, pinValue⟩ : ∃ pin : ℕ, ∀ (x : Fin 9 → Bool) (t : List Bool), t.length ≤ C.size →
        (A x ++ t).getD pin false = fire x := by
      by_cases dup : s = {0,4}
      · subst s
        refine ⟨9, ?_⟩
        intro x t _
        rw [List.getD_append _ _ _ _ (by simp [A])]
        unfold A fire
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [Bool.or_eq_true]
      · have one : s.card ≤ 1 := by
          rcases degenerate with h | h
          · exact h
          · exact absurd h dup
        by_cases empty : s = ∅
        · subst s
          refine ⟨10 + C.size, ?_⟩
          intro x t ht
          rw [List.getD_eq_default _ _ (by simp [A]; omega)]
          simp [fire]
        · obtain ⟨i,mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
          have single : s = {i} := by
            ext j
            simpa only [Finset.mem_singleton] using
              (show j ∈ s ↔ j = i from ⟨fun hj => Finset.card_le_one_iff.mp one hj mem,
                fun e => e ▸ mem⟩)
          subst s
          refine ⟨i.val, ?_⟩
          intro x t _
          have h : i.val < (List.ofFn x).length := by simp
          rw [List.getD_append _ _ _ _ (by simp [A]; omega)]
          unfold A fire
          rw [List.getD_append _ _ _ _ h]
          simp only [Finset.mem_singleton, exists_eq_left, decide_eq_true_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some, List.getElem_ofFn]
          change x i = decide (x i = true)
          cases x i <;> rfl
    let dest (i : ℕ) := if i < 10 then i else if i = 10 then pin else i-1
    let shift (g : Gate) : Gate := ⟨g.op, g.inputs.map dest⟩
    have align (x : Fin 9 → Bool) (t : List Bool) (ht : t.length ≤ C.size) (i : ℕ) :
        ((A x ++ [fire x]) ++ t).getD i false = (A x ++ t).getD (dest i) false := by
      have len : (A x).length = 10 := by simp [A]
      by_cases low : i < 10
      · simp only [dest, low, if_true]
        have h : i < (A x).length := by omega
        have hbig : i < (A x ++ [fire x]).length := by simp [len]; omega
        rw [List.getD_append (A x ++ [fire x]) t false i hbig, List.getD_append (A x) [fire x] false i h, List.getD_append (A x) t false i h]
      · by_cases eq : i = 10
        · subst i
          simp only [dest, lt_irrefl, if_false, if_true]
          rw [pinValue x t ht, List.getD_append _ _ _ _ (by simp [len]),
            List.getD_append_right _ _ _ _ (by omega),len]
          rfl
        · simp only [dest,low,eq,if_false]
          rw [List.getD_append_right _ _ _ _ (by simp [len]; omega),
            List.getD_append_right _ _ _ _ (by omega)]
          congr 1
    have simulate (x : Fin 9 → Bool) (gs : List Gate) (t : List Bool)
        (budget : t.length + gs.length ≤ C.size) :
        ∃ u, u.length ≤ C.size ∧ gs.foldl step ((A x ++ [fire x]) ++ t) = (A x ++ [fire x]) ++ u ∧
          (gs.map shift).foldl step (A x ++ t) = A x ++ u := by
      induction gs generalizing t with
      | nil => exact ⟨t,by simpa using budget,rfl,rfl⟩
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun i => ((A x ++ [fire x]) ++ t).getD i false)
        have same : (shift g).op.eval ((shift g).inputs.map (fun i => (A x ++ t).getD i false)) = v := by
          unfold shift v
          rw [List.map_map]
          apply congrArg
          apply List.map_congr_left
          intro i _
          exact (align x t (by simp at budget; omega) i).symm
        obtain ⟨u,hu,h1,h2⟩ := ih (t ++ [v]) (by simp at budget ⊢; omega)
        refine ⟨u,hu,?_,?_⟩
        · simpa only [List.foldl_cons,step,v,List.append_assoc] using h1
        · simpa only [List.map_cons,List.foldl_cons,step,same,List.append_assoc] using h2
    let D : Circuit := ⟨C.gates.map shift, dest C.output⟩
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      simpa [shift] using fan q hq
    have honestD (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = f x := by
      obtain ⟨u,hu,h1,h2⟩ := simulate x C.gates [] (by change 0 + C.gates.length ≤ C.gates.length; omega)
      simp only [List.append_nil] at h1 h2
      change ((C.gates.map shift).foldl step (A x)).getD (dest C.output) false = _
      rw [h2,← align x u hu C.output,← h1]
      change C.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [fire x]) = _
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using correct x
    have lb := firstBound D fanD honestD
    change 13 ≤ (C.gates.map shift).countP paid at lb
    rw [List.countP_map] at lb
    have keep : (C.gates.countP (paid ∘ shift)) = C.gates.countP paid := rfl
    have balance := accounting C
    omega
  obtain ⟨u,v,lt,ss,code⟩ : ∃ u v : Fin 9, u < v ∧ s = {u,v} ∧ 10*u.val+v.val ∈
      ([1,2,5,6,7,8,16,17,18,24,25,26,34,46,47,48,56,57,67,78] : List ℕ) := by
    rcases inGood with h | h | h
    · exact absurd (Or.inl h) degenerate
    · exact absurd (Or.inr h) degenerate
    · exact h
  have arity : s.card ≤ 2 := by rw [ss]; exact Finset.card_le_two
  let g : Gate := ⟨.or,s.toList.map Fin.val⟩
  let D : Circuit := ⟨g :: C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact ⟨by simp [g], by simpa [g] using arity⟩
    · exact fan a h
  have addGate (x : Fin 9 → Bool) :
      step (List.ofFn x ++ [x 0 || x 4]) g = List.ofFn x ++ [x 0 || x 4, fire x] := by
    let w := List.ofFn x ++ [x 0 || x 4]
    have read (i : Fin 9) : w.getD i.val false = x i := by
      change (List.ofFn x ++ [_]).getD i.val false = _
      rw [List.getD_append (List.ofFn x) _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
    have one : ((s.toList.map Fin.val).map (fun i => w.getD i false)).any id = fire x := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.map_map,Function.comp_def,read,List.any_map,id_eq,Function.id_comp,
        List.any_eq_true,Finset.mem_toList,fire,decide_eq_true_eq]
    change w ++ [((s.toList.map Fin.val).map (fun i => w.getD i false)).any id] = _
    rw [one]
    simp [w,List.append_assoc]
  have honest (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = f x := by
    change (C.gates.foldl step (step (List.ofFn x ++ [x 0 || x 4]) g)).getD _ false = _
    rw [addGate]
    exact correct x
  have lb := firstBound D legal honest
  change 13 ≤ (g :: C.gates).countP paid at lb
  have pg : paid g = true := rfl
  rw [List.countP_cons,pg,if_pos rfl] at lb
  have balance := accounting C
  have exactly : PEqualNP.NotBracket.notCount C = 1 := by omega
  have length : C.size = 13 := by omega
  let reps : List ℕ := [1,2,6,16,17,18,24,26,34,46,67]
  let rho : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let num := fun (a b : Fin 9) => 10 * min a.val b.val + max a.val b.val
  have narrow : ∀ u v : Fin 9, u<v → 10*u.val+v.val ∈
      ([1,2,5,6,7,8,16,17,18,24,25,26,34,46,47,48,56,57,67,78] : List ℕ) →
      num u v ∈ reps ∨ num (rho u) (rho v) ∈ reps := by
    dsimp only [num,reps,rho]
    decide +kernel
  have pairEval (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [x 0 || x 4, x u || x v]) = f x := by
    have flag : fire x = (x u || x v) := by
      apply Bool.eq_iff_iff.mpr
      simp [fire,ss,Bool.or_eq_true]
    simpa only [flag] using correct x
  rcases narrow u v lt code with yes | reflected
  · obtain ⟨x,h⟩ := tight u v yes C fan length exactly
    exact h (pairEval x)
  let shift := fun (i : ℕ) => if h : i<9 then (rho ⟨i,h⟩).val else i
  let move := fun (g : Gate) => Gate.mk g.op (g.inputs.map shift)
  let E : Circuit := ⟨C.gates.map move,shift C.output⟩
  have reads (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
      (List.ofFn (fun k => x (rho k)) ++ tail).getD i false = (List.ofFn x ++ tail).getD (shift i) false := by
    by_cases h : i<9
    · simp only [shift,dif_pos h]
      have j := (rho ⟨i,h⟩).isLt
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j)]
      simp only [List.getElem_ofFn]
    · simp only [shift,dif_neg h]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega),
        List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega)]
      simp only [List.length_ofFn]
  have forward (x : Fin 9 → Bool) (gs : List Gate) (t : List Bool) : ∃ T,
      gs.foldl step (List.ofFn (fun k => x (rho k))++t) = List.ofFn (fun k => x (rho k))++T ∧
      (gs.map move).foldl step (List.ofFn x++t) = List.ofFn x++T := by
    induction gs generalizing t with
    | nil => exact ⟨t,rfl,rfl⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => x (rho k))++t).getD i false)
      have eq : (move g).op.eval ((move g).inputs.map fun i => (List.ofFn x++t).getD i false) = bit := by
        dsimp only [move,bit]
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i _
        exact (reads x t i).symm
      obtain ⟨T,hl,hr⟩ := ih (t++[bit])
      refine ⟨T,?_,?_⟩
      · simpa only [List.foldl_cons,step,bit,List.append_assoc] using hl
      · simpa only [List.map_cons,List.foldl_cons,step,eq,List.append_assoc] using hr
  have legalE : FanInTwo E := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [move] using fan a ha
  have lenE : E.size = 13 := by
    change (C.gates.map move).length = 13
    rw [List.length_map]
    exact length
  have negE : PEqualNP.NotBracket.notCount E = 1 := by
    have eq : E.gates.countP paid = C.gates.countP paid := by
      change (C.gates.map move).countP paid = _
      rw [List.countP_map]
      rfl
    have b := accounting E
    omega
  have fixed : ∀ x : Fin 9 → Bool, f (fun i => x (rho i)) = f x := by
    dsimp only [f,rho]
    decide +kernel
  obtain ⟨x,wrong⟩ := tight (rho u) (rho v) reflected E legalE lenE negE
  let t := [x 0 || x 4, x (rho u) || x (rho v)]
  have h := pairEval (fun i => x (rho i))
  have old : C.eval (List.ofFn (fun k => x (rho k))++t) = f x := h.trans (fixed x)
  obtain ⟨T,hl,hr⟩ := forward x C.gates t
  apply wrong
  change ((C.gates.map move).foldl step (List.ofFn x++t)).getD (shift C.output) false = f x
  change (C.gates.foldl step _).getD C.output false = f x at old
  rw [hr,← reads x T C.output,←hl]
  exact old
