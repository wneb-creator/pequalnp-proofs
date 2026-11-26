import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6500000 in
theorem PEqualNP.Outside.R_meta_3803_731
    (packBit : ∀ (xs : List Bool) (i : ℕ), (xs.foldr Nat.bit 0).testBit i = xs.getD i false)
    (rejection :
      ∀ (C : Circuit) (J : List ℕ), J.length ≤ 2 →
      Monotone2 C → ReadsBack 27 C → C.size ≤ 62 →
      let V := List.finRange 13
      let positive := V.flatMap fun l => (singerLines3 l).sort.map fun p => (true,incidenceInput {p} {l})
      let negative := (V.sublistsLen 4).filterMap fun q =>
        let Q := q.toFinset
        if IsQuadrangle singerLines3 Q then some (false,incidenceInput Q (missLines singerLines3 Q)) else none
      let pack := fun f : Bool × List Bool → Bool => ((positive ++ negative).map f).foldr Nat.bit 0
      let bank := List.ofFn fun i : Fin 27 => pack (fun r => (r.2 ++ [J.any fun i => r.2.getD i false]).getD i.val false)
      let mask := 2^(positive ++ negative).length-1
      let step := fun (b : List ℕ) (g : Gate) =>
        let args := g.inputs.map fun i => b.getD i 0
        b ++ [if g.op.eval [true,false] then args.foldr (fun a z => a ||| z) 0 else args.foldr (fun a z => a &&& z) mask]
      ((C.gates.foldl step bank).getD C.output 0 &&& mask) ≠ pack Prod.fst) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → (63 : ℕ) ≤ x6.size := by
  intro shifts pos neg arc accepts C J listed mono reads fit
  by_contra! small
  let V := List.finRange 13
  let positive := V.flatMap fun l => (singerLines3 l).sort.map fun p => (true,incidenceInput {p} {l})
  let negative := (V.sublistsLen 4).filterMap fun q =>
    let Q := q.toFinset
    if IsQuadrangle singerLines3 Q then some (false,incidenceInput Q (missLines singerLines3 Q)) else none
  let rows := positive ++ negative
  let input := fun (x : List Bool) => x ++ [J.any fun i => x.getD i false]
  let pack := fun f : Bool × List Bool → Bool => (rows.map f).foldr Nat.bit 0
  let bank := List.ofFn fun i : Fin 27 => pack (fun r => (input r.2).getD i.val false)
  let mask := 2^rows.length-1
  let step := fun (b : List ℕ) (g : Gate) =>
    let args := g.inputs.map fun i => b.getD i 0
    b ++ [if g.op.eval [true,false] then args.foldr (fun a z => a ||| z) 0 else args.foldr (fun a z => a &&& z) mask]

  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ shifts := by decide +kernel
  have posSpec (p l : Fin 13) (inc : p ∈ singerLines3 l) :
      C.eval (input (incidenceInput {p} {l})) = true := by
    have yes := fit.1 p l ((incidence p l).1 inc)
    delta incidenceInput
    simpa only [Finset.mem_singleton] using yes
  have negSpec (Q : Finset (Fin 13)) (quad : IsQuadrangle singerLines3 Q) :
      C.eval (input (incidenceInput Q (missLines singerLines3 Q))) = false := by
    have inLine (l : Fin 13) : Q.filter (fun p => p-l ∈ shifts) = Q ∩ singerLines3 l := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_inter,incidence]
    have cap : arc Q := ⟨quad.1,fun l => (inLine l).symm ▸ quad.2 l⟩
    have misses (l : Fin 13) : l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p-l ∉ shifts := by
      change l ∈ Finset.univ.filter (fun k => Disjoint (singerLines3 k) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,incidence]
      exact ⟨fun h p hp hpl => h hpl hp,fun h p hpl hp => h p hp hpl⟩
    delta incidenceInput
    simpa only [input,misses] using fit.2 Q cap
  have width (P L : Finset (Fin 13)) : (input (incidenceInput P L)).length = 27 := by
    delta incidenceInput
    simp [input]
  have observe (r : Bool × List Bool) (hr : r ∈ rows) :
      C.eval (input r.2) = r.1 ∧ (input r.2).length = 27 := by
    change r ∈ positive ++ negative at hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨l,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      exact ⟨posSpec p l ((Finset.mem_sort (· ≤ ·)).mp hp),width _ _⟩
    · obtain ⟨q,_,h⟩ := List.mem_filterMap.mp h
      change (if IsQuadrangle singerLines3 q.toFinset then
        some (false,incidenceInput q.toFinset (missLines singerLines3 q.toFinset)) else none) = some r at h
      by_cases okay : IsQuadrangle singerLines3 q.toFinset
      · rw [ite_eq_left okay] at h
        have eq := Option.some.inj h
        rw [← eq]
        exact ⟨negSpec _ okay,width _ _⟩
      · simp [okay] at h
  have foldOr (b : ℕ) (values : List ℕ) :
      (values.foldr (fun a z => a ||| z) 0).testBit b = (values.map (·.testBit b)).any id := by
    induction values with
    | nil => exact Nat.zero_testBit _
    | cons v vs ih =>
      change (v ||| vs.foldr (fun a z => a ||| z) 0).testBit b = _
      rw [Nat.testBit_or,ih]
      rfl
  have foldAnd (b : ℕ) (values : List ℕ) (hb : mask.testBit b = true) :
      (values.foldr (fun a z => a &&& z) mask).testBit b = (values.map (·.testBit b)).all id := by
    induction values with
    | nil => exact hb
    | cons v vs ih =>
      change (v &&& vs.foldr (fun a z => a &&& z) mask).testBit b = _
      rw [Nat.testBit_and,ih]
      rfl
  let stepB := fun (values : List Bool) (g : Gate) =>
    values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]
  have bitStep (j : ℕ) (hj : mask.testBit j = true) (b : List ℕ) (g : Gate)
      (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
      (step b g).map (·.testBit j) = stepB (b.map (·.testBit j)) g := by
    have args : (g.inputs.map (fun i => b.getD i 0)).map (·.testBit j) =
        g.inputs.map (fun i => (b.map (·.testBit j)).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simpa only [Function.comp_apply,Nat.zero_testBit] using
        (List.getD_map (n := i) b 0 (·.testBit j)).symm
    rcases hop with hand | hor
    · have st : step b g = b ++ [(g.inputs.map (fun i => b.getD i 0)).foldr (fun a z => a &&& z) mask] := by
        change b ++ [if g.op.eval [true,false] then _ else _] = _
        rw [hand]
        rfl
      rw [st,List.map_append,List.map_singleton,foldAnd _ _ hj,args]
      change _ = b.map (·.testBit j) ++ [g.op.eval _]
      rw [hand]
      rfl
    · have st : step b g = b ++ [(g.inputs.map (fun i => b.getD i 0)).foldr (fun a z => a ||| z) 0] := by
        change b ++ [if g.op.eval [true,false] then _ else _] = _
        rw [hor]
        rfl
      rw [st,List.map_append,List.map_singleton,foldOr,args]
      change _ = b.map (·.testBit j) ++ [g.op.eval _]
      rw [hor]
      rfl
  have bitRun (j : ℕ) (hj : mask.testBit j = true) (gs : List Gate) (b : List ℕ)
      (pure : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      (gs.foldl step b).map (·.testBit j) = gs.foldl stepB (b.map (·.testBit j)) := by
    induction gs generalizing b with
    | nil => rfl
    | cons g gs ih =>
      have rem : ∀ t ∈ gs, t.op = GateOp.and ∨ t.op = GateOp.or :=
        fun t ht => pure t (List.mem_cons_of_mem _ ht)
      simp only [List.foldl_cons]
      rw [ih _ rem,bitStep j hj b g (pure g List.mem_cons_self)]
  have oneRow (j : ℕ) (hj : j < rows.length) :
      bank.map (·.testBit j) = input rows[j].2 := by
    change (List.ofFn fun i : Fin 27 => pack (fun r => (input r.2).getD i.val false)).map
      (·.testBit j) = input rows[j].2
    rw [List.map_ofFn]
    have len : (input rows[j].2).length = 27 := (observe _ (List.getElem_mem hj)).2
    apply List.ext_getElem
    · simpa using len.symm
    · intro i ha hb
      have i27 : i < 27 := by simpa using ha
      rw [List.getElem_ofFn]
      change ((rows.map (fun r => (input r.2).getD i false)).foldr Nat.bit 0).testBit j =
        (input rows[j].2)[i]'hb
      rw [packBit]
      have fits : j < (rows.map (fun r => (input r.2).getD i false)).length := by simpa using hj
      rw [List.getD_eq_getElem _ _ fits,List.getElem_map,List.getD_eq_getElem _ _ hb]
  have correct : ((C.gates.foldl step bank).getD C.output 0 &&& mask) = pack Prod.fst := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    change (_ && (2^rows.length-1).testBit j) =
      ((rows.map Prod.fst).foldr Nat.bit 0).testBit j
    rw [Nat.testBit_two_pow_sub_one,packBit]
    by_cases hj : j < rows.length
    · have maskOn : mask.testBit j = true := by
        change (2^rows.length-1).testBit j = true
        rw [Nat.testBit_two_pow_sub_one,decide_eq_true hj]
      rw [decide_eq_true hj,Bool.and_true]
      have get := List.getD_map (n := C.output) (C.gates.foldl step bank) 0 (·.testBit j)
      have start : ((C.gates.foldl step bank).getD C.output 0).testBit j =
          (C.gates.foldl stepB (input rows[j].2)).getD C.output false := by
        simpa only [Nat.zero_testBit,bitRun j maskOn C.gates bank (fun g hg => (mono g hg).1),
          oneRow j hj] using get.symm
      rw [start]
      have hm : j < (rows.map Prod.fst).length := by simpa using hj
      rw [List.getD_eq_getElem _ _ hm,List.getElem_map]
      exact (observe _ (List.getElem_mem hj)).1
    · rw [decide_eq_false hj,Bool.and_false,List.getD_eq_default]
      simpa using Nat.le_of_not_lt hj
  have shortJ : J.length ≤ 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have legal : ReadsBack 27 C := by
    intro j hj w hw
    have gate : gateAt C j = C.gates.get ⟨j,hj⟩ := by
      change C.gates.getD j ⟨.or,[]⟩ = _
      exact List.getD_eq_get _ _ ⟨j,hj⟩
    rw [gate] at hw
    exact reads ⟨j,hj⟩ w hw
  exact (rejection C J shortJ mono legal (by omega)) correct
