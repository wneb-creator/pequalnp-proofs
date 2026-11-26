import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_8297_683
    (andRoot : let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (D : Circuit) (a : ℕ), FanInTwo D → D.size ≤ 18 →
        (D.size < 18 ∨ ∃ g ∈ D.gates, g.op = .not) →
        10 ≤ a → a < D.output → D.output + 1 = 10 + D.size →
        ¬ ∀ x : Fin 10 → Bool,
          ((D.wires (List.ofFn x)).getD a false && D.eval (List.ofFn x)) = f x)
    (orRoot : let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (D : Circuit) (a : ℕ), FanInTwo D → D.size ≤ 18 →
        (D.size < 18 ∨ ∃ g ∈ D.gates, g.op = .not) →
        10 ≤ a → a < D.output → D.output + 1 = 10 + D.size →
        ¬ ∀ x : Fin 10 → Bool,
          ((D.wires (List.ofFn x)).getD a false || D.eval (List.ofFn x)) = f x)
    (notRoot : let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 → 10 ≤ D.output →
        (∃ g ∈ D.gates, g.op = .not) → D.output + 1 = 10 + D.size →
        ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = !(f x)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.size + x3.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [!x2.eval (List.ofFn x7)]) = x1 x7 := by
  dsimp only
  intro A B hA hB hbudget hcompute
  let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let calcGate (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have sizeEq (C : Circuit) : C.size = C.gates.length := rfl
  have wiresEq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl calcGate x := rfl
  have evalEq (C : Circuit) (x : List Bool) : C.eval x = (C.wires x).getD C.output false := rfl
  let G : Circuit := ⟨A.gates ++ ⟨.not,[A.output]⟩ :: B.gates, B.output⟩
  have gFan : FanInTwo G := by
    intro g hg
    rcases List.mem_append.mp hg with ha | hb
    · exact hA g ha
    · rcases List.mem_cons.mp hb with rfl | hg
      · simp
      · obtain ⟨hop,hcap⟩ := hB g hg
        exact ⟨by rcases hop with h | h; exact Or.inl h; exact Or.inr (Or.inl h),hcap⟩
  have gSize : G.size ≤ 19 := by
    change A.gates.length + B.gates.length ≤ 18 at hbudget
    simp [G,sizeEq]
    omega
  have gNot : ∃ g ∈ G.gates, g.op = .not :=
    ⟨⟨.not,[A.output]⟩,List.mem_append_right _ (by simp),rfl⟩
  have gCompute (x : Fin 10 → Bool) : G.eval (List.ofFn x) = f x := by
    simpa only [G,List.foldl_append,List.foldl_cons,calcGate,notEval,List.map_cons,List.map_nil,
      List.headD_cons,evalEq,wiresEq] using hcompute x

  have foldExt (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, gs.foldl calcGate w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t,ht,hl⟩ := ih (calcGate w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      rw [List.foldl_cons,ht]; simp [calcGate]
  have foldLength (gs : List Gate) (w : List Bool) :
      (gs.foldl calcGate w).length = w.length + gs.length := by
    obtain ⟨t,ht,hl⟩ := foldExt gs w
    rw [ht]; simp [hl]
  have foldRead (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl calcGate w).getD i false = w.getD i false := by
    obtain ⟨t,ht,_⟩ := foldExt gs w
    rw [ht,List.getD_append _ _ _ _ hi]
  let bit (D : Circuit) (a : ℕ) (x : Fin 10 → Bool) := (D.wires (List.ofFn x)).getD a false
  have raw (D : Circuit) (a : ℕ) (ha : a < 10) (x : Fin 10 → Bool) :
      bit D a x = x ⟨a,ha⟩ := by
    change (D.gates.foldl calcGate (List.ofFn x)).getD a false = _
    rw [foldRead _ _ _ (by simpa using ha), List.getD_eq_getElem _ _ (by simpa using ha)]
    rw [List.getElem_ofFn]
  have invalid (D : Circuit) (a : ℕ) (ha : 10+D.size ≤ a) (x : Fin 10 → Bool) :
      bit D a x = false := by
    change (D.gates.foldl calcGate (List.ofFn x)).getD a false = false
    apply List.getD_eq_default
    simpa [foldLength,sizeEq] using ha
  let cut (D : Circuit) (n a : ℕ) : Circuit := ⟨D.gates.take n,a⟩
  have cutSize (D : Circuit) (n a : ℕ) (h : n ≤ D.size) : (cut D n a).size = n := by
    simpa [cut,sizeEq] using Nat.min_eq_left h
  have cutFan (D : Circuit) (n a : ℕ) (h : FanInTwo D) : FanInTwo (cut D n a) := by
    intro g hg
    exact h g (List.mem_of_mem_take hg)
  have cutRead (D : Circuit) (n a i : ℕ) (nle : n ≤ D.size) (hi : i < 10+n)
      (x : Fin 10 → Bool) : bit (cut D n a) i x = bit D i x := by
    change ((D.gates.take n).foldl calcGate (List.ofFn x)).getD i false =
      (D.gates.foldl calcGate (List.ofFn x)).getD i false
    conv_rhs => rw [← List.take_append_drop n D.gates]
    rw [List.foldl_append,foldRead (D.gates.drop n) _ i]
    have nn : n ≤ D.gates.length := nle
    simpa [foldLength,List.length_take,Nat.min_eq_left nn] using hi
  have gateRead (D : Circuit) (j : ℕ) (hj : j < D.gates.length) (x : Fin 10 → Bool) :
      bit D (10+j) x =
        D.gates[j].op.eval (D.gates[j].inputs.map fun i =>
          if i < 10+j then bit D i x else false) := by
    have split : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j+1) := by simp
    let W := (D.gates.take j).foldl calcGate (List.ofFn x)
    have wl : W.length = 10+j := by
      simp [W,foldLength,Nat.min_eq_left (Nat.le_of_lt hj)]
    have eq (i : ℕ) : W.getD i false = if i < 10+j then bit D i x else false := by
      split
      · exact cutRead D j 0 i (Nat.le_of_lt hj) (by assumption) x
      · apply List.getD_eq_default
        omega
    change (D.gates.foldl calcGate (List.ofFn x)).getD (10+j) false = _
    conv_lhs => rw [split]
    rw [List.foldl_append,List.foldl_cons]
    change ((D.gates.drop (j+1)).foldl calcGate (calcGate W D.gates[j])).getD (10+j) false = _
    rw [foldRead _ _ _ (by simp [calcGate,wl])]
    simp only [calcGate]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [wl,Nat.sub_self,List.getD_cons_zero]
    congr 1
    exact List.map_congr_left fun i _ => eq i

  have zFalse : f (fun _ => false) = false := rfl
  have oTrue : f (fun _ => true) = true := rfl
  have singletonFalse : ∀ i : Fin 10, f (fun j => decide (j=i)) = false := by decide +kernel
  have absentTrue : ∀ i : Fin 10, f (fun j => decide (j≠i)) = true := by decide +kernel
  have noFalse (h : ∀ x, false = f x) : False := by
    have k := h (fun _ => true)
    rw [oTrue] at k
    contradiction
  have noTrue (h : ∀ x, true = f x) : False := by
    have k := h (fun _ => false)
    rw [zFalse] at k
    contradiction
  have increasing (D : Circuit) (hd : FanInTwo D)
      (none : ¬ ∃ g ∈ D.gates, g.op = .not) :
      ∀ k, bit D k (fun _ => false) = true → bit D k (fun _ => true) = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro ht
      by_cases kr : k < 10
      · rw [raw D k kr] at ht
        contradiction
      by_cases ki : 10+D.size ≤ k
      · rw [invalid D k ki] at ht
        contradiction
      let j := k-10
      have red : 10+j = k := by omega
      have jr : j < D.gates.length := by change j < D.size; omega
      have legal := (hd D.gates[j] (List.getElem_mem jr)).1
      have move (a : ℕ) :
          (if a < 10+j then bit D a (fun _ => false) else false) = true →
          (if a < 10+j then bit D a (fun _ => true) else false) = true := by
        by_cases ar : a < 10+j
        · simpa only [ite_eq_left ar] using (ih a (by omega))
        · simp [ar]
      rw [← red,gateRead D j jr] at ht ⊢
      rcases legal with op | op | op
      · simp only [op,andEval,List.all_map,Function.comp_apply,id_eq,List.all_eq_true] at ht ⊢
        exact fun a ha => move a (ht a ha)
      · simp only [op,orEval,List.any_map,Function.comp_apply,id_eq,List.any_eq_true] at ht ⊢
        obtain ⟨a,ha,hb⟩ := ht
        exact ⟨a,ha,move a hb⟩
      · exact False.elim (none ⟨D.gates[j],List.getElem_mem jr,op⟩)

  have solve (D : Circuit) (hd : FanInTwo D) (sz : D.size ≤ 19)
      (used : D.size < 19 ∨ ∃ g ∈ D.gates, g.op = .not) :
      ∀ r, (∀ x, bit D r x = f x) → False := by
    intro r
    induction r using Nat.strong_induction_on with
    | ind r ih =>
      intro comp
      by_cases rawR : r < 10
      · let i : Fin 10 := ⟨r,rawR⟩
        have q := comp (fun j => decide (j=i))
        rw [raw D r rawR, singletonFalse i] at q
        simp [i] at q
      by_cases invR : 10+D.size ≤ r
      · exact noFalse fun x => (invalid D r invR x).symm.trans (comp x)
      let j := r-10
      have red : 10+j = r := by omega
      have jj : j < D.gates.length := by change j < D.size; omega
      let g := D.gates[j]
      have hg := hd g (List.getElem_mem jj)
      have go : g.op = .and ∨ g.op = .or ∨ g.op = .not := hg.1
      let readAt (a : ℕ) (x : Fin 10 → Bool) := if a < r then bit D a x else false
      have form (x : Fin 10 → Bool) : g.op.eval (g.inputs.map fun i => readAt i x) = f x := by
        have hh := gateRead D j jj x
        rw [red] at hh
        exact hh.symm.trans (comp x)
      have projection (a : ℕ) (hread : ∀ x, readAt a x = f x) : False := by
        by_cases ha : a < r
        · exact ih a ha fun x => by simpa [readAt,ha] using hread x
        · exact noFalse fun x => by simpa [readAt,ha] using hread x
      have validNot (a : ℕ) (hread : ∀ x, (!(readAt a x)) = f x) : False := by
        by_cases ha : a < r
        · by_cases ha10 : a < 10
          · have q := hread (fun _ => false)
            simp [readAt,ha,raw D a ha10,zFalse] at q
          have nle : a+1-10 ≤ D.size := by omega
          let P := cut D (a+1-10) a
          have ps := cutSize D (a+1-10) a nle
          have pd : P.output = a := rfl
          have complement (x : Fin 10 → Bool) : P.eval (List.ofFn x) = !(f x) := by
            change bit P a x = !(f x)
            rw [cutRead D (a+1-10) a a nle (by omega)]
            have q := congrArg Bool.not (hread x)
            simpa only [readAt,ite_eq_left ha,Bool.not_not] using q
          by_cases neg : ∃ t ∈ P.gates, t.op = .not
          · exact notRoot P (cutFan D _ _ hd) (by change (cut D _ _).size ≤ 18; omega)
              (by omega) neg (by change a+1 = 10 + (cut D _ _).size; omega) complement
          · have low : bit P P.output (fun _ => false) = true := by
              change P.eval _ = true
              rw [complement,zFalse]
              rfl
            have high : bit P P.output (fun _ => true) = false := by
              change P.eval _ = false
              rw [complement,oTrue]
              rfl
            have h := increasing P (cutFan D _ _ hd) neg P.output low
            rw [high] at h
            contradiction
        · exact noTrue fun x => by simpa [readAt,ha] using hread x
      have binary (op : GateOp) (hop : g.op = op) (bin : op = .and ∨ op = .or)
          (a b : ℕ) (formula : ∀ x, op.eval [readAt a x,readAt b x] = f x) : False := by
        by_cases ha : a < r
        · by_cases hb : b < r
          · by_cases ha10 : a < 10
            · rcases bin with rfl | rfl
              · let i : Fin 10 := ⟨a,ha10⟩
                have q := formula (fun k => decide (k≠i))
                rw [absentTrue i] at q
                simp [andEval,orEval,notEval,readAt,ha,hb,raw D a ha10,i] at q
              · let i : Fin 10 := ⟨a,ha10⟩
                have q := formula (fun k => decide (k=i))
                simp [andEval,orEval,notEval,readAt,ha,hb,raw D a ha10,singletonFalse i,i] at q
            by_cases hb10 : b < 10
            · rcases bin with rfl | rfl
              · let i : Fin 10 := ⟨b,hb10⟩
                have q := formula (fun k => decide (k≠i))
                rw [absentTrue i] at q
                simp [andEval,orEval,notEval,readAt,ha,hb,raw D b hb10,i] at q
              · let i : Fin 10 := ⟨b,hb10⟩
                have q := formula (fun k => decide (k=i))
                simp [andEval,orEval,notEval,readAt,ha,hb,raw D b hb10,singletonFalse i,i] at q
            by_cases hab : a=b
            · subst b
              apply projection a
              intro x
              have q := formula x
              rcases bin with rfl | rfl <;> simpa [andEval,orEval,notEval] using q
            let lo := min a b
            let hi := max a b
            have hmin : 10 ≤ lo := by dsimp [lo]; omega
            have hmax : hi < r := by dsimp [hi]; omega
            have ord : lo < hi := by dsimp [lo,hi]; omega
            have hl : hi+1-10 ≤ D.size := by omega
            let P := cut D (hi+1-10) hi
            have ps : P.size = hi+1-10 := cutSize D _ _ hl
            have po : P.output = hi := rfl
            have pSmall : P.size ≤ 18 := by omega
            have pLast : P.output+1 = 10+P.size := by omega
            have pNeg : P.size < 18 ∨ ∃ t ∈ P.gates, t.op = .not := by
              by_cases below : P.size < 18
              · exact Or.inl below
              right
              have eqJ : j = 18 := by omega
              have eqD : D.size = 19 := by omega
              have eqL : hi+1-10 = j := by omega
              obtain ⟨t,ht,hnot⟩ := used.resolve_left (by omega)
              have dsplit : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j+1) := by simp
              have nil : D.gates.drop (j+1) = [] := by
                apply List.drop_eq_nil_of_le
                change D.size ≤ j+1
                omega
              rw [dsplit,nil] at ht
              rcases List.mem_append.mp ht with old | last
              · refine ⟨t,?_,hnot⟩
                change t ∈ D.gates.take (hi+1-10)
                simpa [eqL] using old
              · have e : t = g := List.mem_singleton.mp last
                subst t
                rw [hop] at hnot
                rcases bin with e | e <;> rw [e] at hnot <;> contradiction
            have swap (x : Fin 10 → Bool) :
                op.eval [bit D lo x,bit D hi x] = f x := by
              have eq := formula x
              by_cases ab : a ≤ b
              · simpa [lo,hi,Nat.min_eq_left ab,Nat.max_eq_right ab,readAt,ha,hb] using eq
              · have ba : b ≤ a := by omega
                rcases bin with rfl | rfl
                · simpa [lo,hi,Nat.min_eq_right ba,Nat.max_eq_left ba,readAt,ha,hb,
                    andEval,Bool.and_comm] using eq
                · simpa [lo,hi,Nat.min_eq_right ba,Nat.max_eq_left ba,readAt,ha,hb,
                    orEval,Bool.or_comm] using eq
            have lowWire (x) := cutRead D (hi+1-10) hi lo hl (by omega) x
            have highWire (x) := cutRead D (hi+1-10) hi hi hl (by omega) x
            rcases bin with rfl | rfl
            · apply andRoot P lo (cutFan D _ _ hd) pSmall pNeg hmin (by simpa [po] using ord) pLast
              intro x
              change (bit P lo x && bit P hi x) = f x
              rw [show bit P lo x = bit D lo x from lowWire x,
                show bit P hi x = bit D hi x from highWire x]
              simpa [andEval,orEval,notEval] using swap x
            · apply orRoot P lo (cutFan D _ _ hd) pSmall pNeg hmin (by simpa [po] using ord) pLast
              intro x
              change (bit P lo x || bit P hi x) = f x
              rw [show bit P lo x = bit D lo x from lowWire x,
                show bit P hi x = bit D hi x from highWire x]
              simpa [andEval,orEval,notEval] using swap x
          · rcases bin with rfl | rfl
            · exact noFalse fun x => by simpa [andEval,orEval,notEval,readAt,hb] using formula x
            · exact projection a fun x => by simpa [andEval,orEval,notEval,readAt,hb] using formula x
        · rcases bin with rfl | rfl
          · exact noFalse fun x => by simpa [andEval,orEval,notEval,readAt,ha] using formula x
          · exact projection b fun x => by simpa [andEval,orEval,notEval,readAt,ha] using formula x
      have inputCases (l : List ℕ) (len : l.length ≤ 2) :
          l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a,b]) := by
        rcases l with _ | ⟨a,l⟩
        · exact Or.inl rfl
        rcases l with _ | ⟨b,l⟩
        · exact Or.inr (Or.inl ⟨a,rfl⟩)
        rcases l with _ | ⟨c,l⟩
        · exact Or.inr (Or.inr ⟨a,b,rfl⟩)
        simp at len
      rcases inputCases g.inputs hg.2 with no | ⟨a,one⟩ | ⟨a,b,two⟩
      · rcases go with op | op | op
        · exact noTrue fun x => by simpa [op,no,andEval,orEval,notEval] using form x
        · exact noFalse fun x => by simpa [op,no,andEval,orEval,notEval] using form x
        · exact noTrue fun x => by simpa [op,no,andEval,orEval,notEval] using form x
      · rcases go with op | op | op
        · exact projection a fun x => by simpa [op,one,andEval,orEval,notEval] using form x
        · exact projection a fun x => by simpa [op,one,andEval,orEval,notEval] using form x
        · exact validNot a fun x => by simpa [op,one,andEval,orEval,notEval] using form x
      · rcases go with op | op | op
        · exact binary .and op (Or.inl rfl) a b fun x => by simpa [op,two] using form x
        · exact binary .or op (Or.inr rfl) a b fun x => by simpa [op,two] using form x
        · exact validNot a fun x => by simpa [op,two,andEval,orEval,notEval] using form x

  exact solve G gFan gSize (Or.inr gNot) G.output gCompute
