import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 5500000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_8174_204
    (live : ∀ (n : ℕ) (C : Circuit) (T : List (ℕ × ℕ)),
      (∀ j < C.size, (∃ e ∈ T, n+j = e.1 ∨ n+j = e.2) ∨
        ∃ i < C.size, j < i ∧ n+j ∈ (gateAt C i).inputs) →
      ∀ j < C.size, ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
        w = n+j ∨ n ≤ w ∧ EdgeOwnership.InCone n C j (w-n))
    (search : ∃ (k : ℕ) (op : Fin k → Bool) (a b : Fin k → ℕ)
        (s : ℕ → ℕ) (T : List (ℕ × ℕ)),
      6 ≤ k ∧ k + 2*T.length = 22 ∧ 3 ≤ ((List.finRange k).filter op).length ∧
      (∀ i : Fin 11, s i.val = ([2147418115,663661903884,34144976944,728266375360,
        21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,
        1065151898146] : List ℕ).getD i.val 0) ∧
      (∀ j, a j ≤ b j ∧ b j < 11+j.val ∧
        s (11+j.val) = (if op j then s (a j) &&& s (b j) else s (a j) ||| s (b j)) ∧
        (∃ p : Fin 16, (s (11+j.val)).testBit p.val = true) ∧
        (∃ q : Fin 24, (s (11+j.val)).testBit (16+q.val) = true) ∧
        ((∃ e ∈ T, 11+j.val = e.1 ∨ 11+j.val = e.2) ∨
          ∃ i : Fin k, j < i ∧ (11+j.val = a i ∨ 11+j.val = b i))) ∧
      (∀ e ∈ T, e.1 < 11+k ∧ e.2 < 11+k) ∧
      (T.map (fun e => s e.1 &&& s e.2)).foldr (· ||| ·) 0 = 65535) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   have x6 : ℕ → Bool := fun (x6 : ℕ) => x2.any fun (x7 : ℕ × ℕ) => x5 x6 x7.1 && x5 x6 x7.2;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * (x2.length + (List.filter (fun (x7 : ℕ) => !x6 x7) x3).length) ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x7 ∈ x2, x7.1 < (11 : ℕ) + x1.size ∧ x7.2 < (11 : ℕ) + x1.size ∧ ((11 : ℕ) ≤ x7.1 ∨ (11 : ℕ) ≤ x7.2)) ∧ (∀ x7 < x1.size, (x3.any fun (x9 : ℕ) => x5 x9 ((11 : ℕ) + x7)) = Bool.true ∧ (x4.any fun (x9 : ℕ) => x5 x9 ((11 : ℕ) + x7)) = Bool.true) ∧ (∀ x7 < x1.size, PEqualNP.ReadTwo.isAnd x1 x7 → ∃ x10 ∈ x2, ∃ x11 ∈ [x10.1, x10.2], x11 = (11 : ℕ) + x7 ∨ (11 : ℕ) ≤ x11 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x7 (x11 - (11 : ℕ))) ∧ ∀ x7 ∈ x4, x6 x7 = Bool.false := by
  obtain ⟨k,op,a,b,s,T,floor,budget,ands,initial,gates,valid,joined⟩ := search
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let N : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let rows := P ++ N
  let row (r : ℕ) := fun i : Fin 11 => r.testBit i.val
  let cols : List ℕ := [2147418115,663661903884,34144976944,728266375360,
    21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  have firstBits : ∀ (r : Fin 40) (i : Fin 11),
      row (rows.getD r.val 0) i = (cols.getD i.val 0).testBit r.val := by decide +kernel
  have posBits : ∀ p : Fin 16, rows.getD p.val 0 ∈ P := by decide
  have negBits : ∀ q : Fin 24, rows.getD (16+q.val) 0 ∈ N := by decide
  have findP : ∀ r ∈ P, ∃ p : Fin 40, rows.getD p.val 0 = r ∧ (65535 : ℕ).testBit p.val = true := by decide +kernel
  have findN : ∀ r ∈ N, ∃ p : Fin 40, rows.getD p.val 0 = r ∧ (65535 : ℕ).testBit p.val = false := by decide +kernel
  let g (i : Fin k) : Gate := ⟨if op i then .and else .or, [a i,b i]⟩
  let C : Circuit := ⟨List.ofFn g,0⟩
  have size : C.size = k := List.length_ofFn
  have atGate (i : Fin k) : gateAt C i.val = g i := by
    change (List.ofFn g).getD i.val _ = g i
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
  have model : TopForm.IsAO2 11 C := by
    refine ⟨?_,?_,?_⟩
    · intro h hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      cases e : op i <;> simp [g,e]
    · intro j hj w hw
      have h : j < k := by simpa [C] using hj
      let i : Fin k := ⟨j,h⟩
      change w ∈ (gateAt C i.val).inputs at hw
      rw [atGate] at hw
      have ab := (gates i).1
      have ub : b i < 11+j := (gates i).2.1
      rcases (show w = a i ∨ w = b i by simpa [g] using hw) with rfl | rfl <;> omega
    · intro h hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      rfl
  have numAnd : ReadTwo.nAnd C = ((List.finRange k).filter op).length := by
    change ((List.ofFn g).filter _).length = _
    rw [List.ofFn_eq_map, List.filter_map]
    simp only [List.length_map]
    congr 1
    apply List.filter_congr
    intro i _
    cases e : op i <;> simp [g,e]
  have replay (r : Fin 40) (w : ℕ) (hw : w < 11+k) :
      BlindGate.wireValue C 11 (row (rows.getD r.val 0)) w = (s w).testBit r.val := by
    let bit (i : ℕ) := (s i).testBit r.val
    let xs := List.ofFn (row (rows.getD r.val 0))
    let step := fun (l : List Bool) (h : Gate) => l ++ [h.op.eval (h.inputs.map (fun i => l.getD i false))]
    have replayAux (gs : List Gate) (l : List Bool)
        (base : ∀ u < l.length, l.getD u false = bit u)
        (rule : ∀ i (hi : i < gs.length), (∀ u ∈ (gs[i]).inputs, u < l.length+i) ∧
          (gs[i]).op.eval ((gs[i]).inputs.map bit) = bit (l.length+i)) :
        ∀ u < l.length+gs.length, (gs.foldl step l).getD u false = bit u := by
      induction gs generalizing l with
      | nil => simpa using base
      | cons h hs ih =>
        have h0 := rule 0 (by simp)
        have next : h.op.eval (h.inputs.map (fun i => l.getD i false)) = bit l.length := by
          have eqs : h.inputs.map (fun i => l.getD i false) = h.inputs.map bit := by
            apply List.map_congr_left
            intro i hi
            apply base
            simpa using h0.1 i hi
          rw [eqs]
          simpa using h0.2
        have len : (step l h).length = l.length+1 := by simp [step]
        apply fun u hu => ih (step l h) ?_ ?_ u (by simp_all only [List.length_cons]; omega)
        · intro i hi
          by_cases small : i < l.length
          · exact (List.getD_append _ _ _ _ small).trans (base i small)
          · have eq : i = l.length := by omega
            subst i
            simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_right] using next
        · intro i hi
          have h := rule (i+1) (by simp; omega)
          change (∀ u ∈ hs[i].inputs, u < l.length+(i+1)) ∧ hs[i].op.eval _ = bit (l.length+(i+1)) at h
          simpa [len,Nat.add_assoc,Nat.add_comm 1] using h
    apply replayAux C.gates xs ?_ ?_ w (by simpa [xs,C] using hw)
    · intro i hi
      have ii : i < 11 := by simpa [xs] using hi
      let z : Fin 11 := ⟨i,ii⟩
      change xs.getD z.val false = _
      rw [List.getD_eq_getElem _ _ hi]
      exact (List.getElem_ofFn ..).trans ((firstBits r z).trans (congrArg (fun n : ℕ => n.testBit r.val) (initial z).symm))
    · intro i hi
      let j : Fin k := ⟨i,by simpa [C] using hi⟩
      have ge : C.gates[i] = g j := List.getElem_ofFn ..
      rw [ge]
      obtain ⟨ab,ub,eq,_⟩ := gates j
      change b j < 11+i at ub
      constructor
      · intro u hu
        rcases (show u = a j ∨ u = b j by simpa [g] using hu) with rfl | rfl <;> simp [xs] <;> omega
      · change _ = (s (xs.length+i)).testBit r.val
        rw [show xs.length+i=11+j.val by simp [xs,j],eq]
        cases e : op j
        · simp only [g,e,Bool.false_eq_true,ite_false,Nat.testBit_or,List.map_cons,List.map_nil]
          change (bit (a j) || (bit (b j) || false)) = _
          simp only [Bool.or_false,bit]
        · simp only [g,e,ite_true,Nat.testBit_and,List.map_cons,List.map_nil]
          change (bit (a j) && (bit (b j) && true)) = _
          simp only [Bool.and_true,bit]
  let val (r w : ℕ) := BlindGate.wireValue C 11 (row r) w
  let keep (e : ℕ × ℕ) := decide (11 ≤ e.1 ∨ 11 ≤ e.2)
  let U := T.filter keep
  let hit (L : List (ℕ × ℕ)) (r : ℕ) := L.any (fun e => val r e.1 && val r e.2)
  have bits (r : ℕ) (L : List (ℕ × ℕ)) :
      ((L.map (fun (e : ℕ × ℕ) => s e.1 &&& s e.2)).foldr (· ||| ·) 0).testBit r =
        L.any (fun e => (s e.1).testBit r && (s e.2).testBit r) := by
    induction L with
    | nil => simp
    | cons e es ih => simp [Nat.testBit_and,Nat.testBit_or,ih]
  have full (p : Fin 40) : hit T (rows.getD p.val 0) = (65535 : ℕ).testBit p.val := by
    rw [← joined,bits]
    apply Bool.eq_iff_iff.mpr
    simp only [hit,List.any_eq_true]
    apply exists_congr
    intro e
    apply and_congr_right
    intro he
    rw [show val (rows.getD p.val 0) e.1 = _ from replay p _ (valid e he).1,
        show val (rows.getD p.val 0) e.2 = _ from replay p _ (valid e he).2]
  have paths := live 11 C T (by
    intro j hj
    let t : Fin k := ⟨j,by omega⟩
    rcases (gates t).2.2.2.2.2 with old | ⟨i,lt,uses⟩
    · exact Or.inl old
    · refine Or.inr ⟨i.val,by rw [size]; exact i.isLt,lt,?_⟩
      rw [atGate]
      simpa [g] using uses)
  have kept {j : ℕ} (hj : j<C.size) :
      ∃ e ∈ U, ∃ w ∈ [e.1,e.2], w=11+j ∨ 11≤w ∧ EdgeOwnership.InCone 11 C j (w-11) := by
    obtain ⟨e,he,w,hw,h⟩ := paths j hj
    have big : 11 ≤ w := by rcases h with h | h <;> omega
    have stays : keep e = true := by
      apply decide_eq_true
      rcases (show w=e.1 ∨ w=e.2 by simpa using hw) with rfl | rfl <;> omega
    exact ⟨e,List.mem_filter.mpr ⟨he,stays⟩,w,hw,h⟩
  have positive : 0 < C.size := by
    omega
  have nonempty : U ≠ [] := by
    obtain ⟨e,he,_⟩ := kept positive
    intro eq; rw [eq] at he; exact List.not_mem_nil he
  have reject : ∀ r ∈ N, hit U r = false := by
    intro r hr
    obtain ⟨p,hp,hn⟩ := findN r hr
    have h := (full p).trans hn
    rw [hp] at h
    apply Bool.eq_false_iff.mpr
    intro on
    obtain ⟨e,he,v⟩ := List.any_eq_true.mp on
    have on' : hit T r = true := List.any_eq_true.mpr ⟨e,(List.mem_filter.mp he).1,v⟩
    exact Bool.false_ne_true (h.symm.trans on')
  have raw (p : Fin 40) (w : ℕ) (hw : w < 11) :
      val (rows.getD p.val 0) w = (rows.getD p.val 0).testBit w := by
    let i : Fin 11 := ⟨w,hw⟩
    exact (replay p _ (by omega)).trans ((congrArg (fun n : ℕ => n.testBit p.val) (initial i)).trans (firstBits p i).symm)
  have smallPairs : ∀ (a b : Fin 11),
      (∀ r ∈ N, (r.testBit a.val && r.testBit b.val) = false) →
      (P.filter (fun r => r.testBit a.val && r.testBit b.val)).length ≤ 1 := by decide +kernel
  let missing := P.filter fun r => !(hit U r)
  have miss_le : missing.length ≤ (T.filter (fun e => !(keep e))).length := by
    let lost := T.filter (fun e => !(keep e))
    have covers : ∀ r ∈ missing, ∃ e ∈ lost, (val r e.1 && val r e.2) = true := by
      intro r hr
      obtain ⟨hp,hu⟩ := List.mem_filter.mp hr
      obtain ⟨p,ep,on⟩ := findP r hp
      have yes := (full p).trans on
      rw [ep] at yes
      obtain ⟨e,he,hv⟩ := List.any_eq_true.mp yes
      refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,hv⟩
      cases hh : keep e
      · rfl
      · have h : hit U r = true := List.any_eq_true.mpr ⟨e,List.mem_filter.mpr ⟨he,hh⟩,hv⟩
        simp [h] at hu
    have capacity (e : ℕ × ℕ) (he : e ∈ lost) :
        (P.filter (fun r => val r e.1 && val r e.2)).length ≤ 1 := by
      obtain ⟨he',hh⟩ := List.mem_filter.mp he
      have hl : e.1 < 11 ∧ e.2 < 11 := by simpa [keep,not_or] using hh
      let a : Fin 11 := ⟨e.1,hl.1⟩
      let b : Fin 11 := ⟨e.2,hl.2⟩
      have same (r : ℕ) (p : Fin 40) (hp : rows.getD p.val 0 = r) :
          (val r e.1 && val r e.2) = (r.testBit a.val && r.testBit b.val) := by
        subst r; rw [raw p _ hl.1,raw p _ hl.2]
      have eqs : P.filter (fun r => val r e.1 && val r e.2) =
          P.filter (fun r => r.testBit a.val && r.testBit b.val) := by
        apply List.filter_congr; intro r hr; obtain ⟨p,hp,_⟩ := findP r hr; exact same r p hp
      rw [eqs]
      apply smallPairs
      intro r hr
      obtain ⟨p,hp,off⟩ := findN r hr
      have h := (full p).trans off
      rw [hp] at h
      rw [← same r p hp]
      apply Bool.eq_false_iff.mpr
      intro hv
      exact Bool.false_ne_true (h.symm.trans (List.any_eq_true.mpr ⟨e,he',hv⟩))
    let bag := lost.flatMap (fun e => P.filter (fun r => val r e.1 && val r e.2))
    have subset : missing.toFinset ⊆ bag.toFinset := by
      intro r hr
      have hm := List.mem_toFinset.mp hr
      obtain ⟨e,he,hv⟩ := covers r hm
      exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨e,he,List.mem_filter.mpr ⟨(List.mem_filter.mp hm).1,hv⟩⟩)
    have nodup : P.Nodup := by decide
    have small (L : List (ℕ × ℕ)) (h : ∀ e ∈ L, e ∈ lost) :
        (L.flatMap (fun e => P.filter (fun r => val r e.1 && val r e.2))).length ≤ L.length := by
      induction L with
      | nil => simp
      | cons e es ih =>
        have h1 := capacity e (h e (by simp))
        have h2 := ih (by intro t ht; exact h t (List.mem_cons_of_mem _ ht))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        omega
    calc
      missing.length = missing.toFinset.card := (List.toFinset_card_of_nodup (nodup.filter _)).symm
      _ ≤ bag.toFinset.card := Finset.card_le_card subset
      _ ≤ bag.length := List.toFinset_card_le _
      _ ≤ lost.length := small lost (fun _ h => h)
  refine ⟨C,U,model,nonempty,?_,numAnd.ge.trans' ands,?_,?_,fun j hj _ => kept hj,reject⟩
  · change C.size + 2*(U.length+missing.length) ≤ 22
    have sum := List.length_eq_length_filter_add (l := T) keep
    dsimp only [U]
    omega
  · intro e he
    obtain ⟨ht,hk⟩ := List.mem_filter.mp he
    obtain ⟨a,b⟩ := valid e ht
    exact ⟨by omega,by omega,of_decide_eq_true hk⟩
  · intro j hj
    let i : Fin k := ⟨j,by omega⟩
    obtain ⟨p,hp⟩ := (gates i).2.2.2.1
    obtain ⟨q,hq⟩ := (gates i).2.2.2.2.1
    constructor <;> apply List.any_eq_true.mpr
    · exact ⟨_,posBits p,(replay ⟨p.val,by omega⟩ (11+j) (by omega)).trans hp⟩
    · exact ⟨_,negBits q,(replay ⟨16+q.val,by omega⟩ (11+j) (by omega)).trans hq⟩
