import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK

-- Boundary rows and their monotonicity argument are adapted from Martin Benda, PR 22209.
-- The packed-column and read-multiplicity checks combine into a finite circuit search.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_17114_733
    (synth : ∃ C : Circuit, C.size ≤ 15 ∧ 25 ≤ C.output ∧ C.output < 25+C.size ∧
      (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j) ∧ ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) [70689, 5263618, 1046528, 47534084, 28520456, 3158096, 62080, 86679559, 134213632, 134213632, 134213632, 105693240, 126812608, 133172736, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632]).getD C.output 0) = 4095 ∧ (∀ v ∈ ([0,7] : List ℕ), 2 ≤ ((scalarMults C 25 [0,7] v).getD C.output none).getD 2))
    (pack : ∀ (C : Circuit), (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) → ∀ (w : List ℕ) (k : ℕ),
      C.eval (w.map (fun z => z.testBit k)) = ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) w).getD C.output 0).testBit k)
    (lift : ∀ (C : Circuit), (∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 25+j ∧ b < 25+j) → (∀ v ∈ ([0,7] : List ℕ), 2 ≤ ((scalarMults C 25 [0,7] v).getD C.output none).getD 2) → ∀ s : Bool, ∃ r : ℕ → ℕ, r (if s = true then 0 else 7) = 0 ∧ r (if s = true then 7 else 0) ≤ 1 ∧
      (∀ j < 25, j ≠ 0 → j ≠ 7 → r j = 2) ∧ 2 ≤ r C.output ∧
      ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → r (25+j) ≤ r a + r b) ∧ (g.op = .or → r (25+j) ≤ min (r a) (r b))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool) (x3 : List Bool), x3.length = (11 : ℕ) → (x1.eval (List.ofFn x2 ++ x3) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), ¬((1 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (3 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  let E := fun p l : Fin 7 => ¬ (1 ≤ l.val ∧ l.val ≤ 3) ∧ (p = l ∨ p = l + 1 ∨ p = l + 3)
  let P : List ℕ := [129,130,136,2064,2080,2049,4128,4160,4098,8256,8193,8196]
  let Z : List ℕ := [1919,2036,3918,4036,5917,6036,7948,8068,10042,10160,12042,14104,14224,16136,16256]
  let row (m : ℕ) (i : Fin 14) := m.testBit i.val
  have pos : ∀ p l : Fin 7, E p l → ∃ m ∈ P,
      ∀ i : Fin 14, row m i = true → i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := by decide +kernel
  have neg : ∀ a : Fin 7 → Bool, ∃ m ∈ Z,
      (∀ i : Fin 7, a i = true → row m (Fin.castAdd 7 i) = true) ∧
      (∀ j : Fin 7, (∀ i : Fin 7, E i j → a i = false) → row m (Fin.natAdd 7 j) = true) := by decide +kernel
  obtain ⟨C,hs,ho,hou,hg,hw,hcost⟩ := synth
  have hr := lift C hg hcost
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] := by
    intro g hmem
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨ho,a,b,hab,_,_,_⟩ := hg j g (List.getElem?_eq_some_iff.mpr ⟨hj,he⟩)
    exact ⟨ho,a,b,hab⟩
  have stepMono (u v : List Bool) (g : Gate)
      (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b])
      (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
    intro i hi
    by_cases hlt : i < u.length
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h i hi
    · change (u ++ [_]).getD i false = true at hi
      change (v ++ [_]).getD i false = true
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases hz : i-u.length = 0
      · simp only [hz, List.getD_cons_zero] at hi ⊢
        obtain ⟨ho,a,b,hab⟩ := hg
        rcases ho with ho | ho
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].all id) = true at hi
          change ([v.getD a false, v.getD b false].all id) = true
          simp only [List.all_cons, List.all_nil, Bool.and_true, id_eq, Bool.and_eq_true] at hi ⊢
          exact ⟨h a hi.1, h b hi.2⟩
        · rw [ho, hab] at hi ⊢
          change ([u.getD a false, u.getD b false].any id) = true at hi
          change ([v.getD a false, v.getD b false].any id) = true
          simp only [List.any_cons, List.any_nil, Bool.or_false, id_eq, Bool.or_eq_true] at hi ⊢
          exact hi.elim (fun ha => Or.inl (h a ha)) (fun hb => Or.inr (h b hb))
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
  have runMono : ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) →
      ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (run gs u).getD i false = true → (run gs v).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro hg u v hlen h i hi; exact h i hi
    | cons g gs ih =>
      intro hg u v hlen h i hi
      change (run gs (step u g)).getD i false = true at hi
      change (run gs (step v g)).getD i false = true
      exact ih (fun k hk => hg k (by simp [hk])) _ _
        (by simp [step, hlen]) (stepMono u v g (hg g (by simp)) hlen h) i hi
  have mono (u v : List Bool) (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) : C.eval u = true → C.eval v = true :=
    runMono C.gates hG u v hlen h C.output
  let cols : List ℕ := [70689, 5263618, 1046528, 47534084, 28520456, 3158096, 62080, 86679559, 134213632, 134213632, 134213632, 105693240, 126812608, 133172736, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632]
  have hp (m : ℕ) (hm : m ∈ P) : C.eval (List.ofFn (row m) ++ List.replicate 11 false) = true := by
    have rows : ∀ m ∈ P, ∃ k : Fin 27, cols.map (fun z => z.testBit k.val) = List.ofFn (row m) ++ List.replicate 11 false ∧ (4095 : ℕ).testBit k.val = true := by decide +kernel
    obtain ⟨k,hk,hout⟩ := rows m hm
    rw [← hk,pack C hG cols k.val]
    change ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) [70689, 5263618, 1046528, 47534084, 28520456, 3158096, 62080, 86679559, 134213632, 134213632, 134213632, 105693240, 126812608, 133172736, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632]).getD C.output 0).testBit k.val = true
    rw [hw,hout]
  have hn (m : ℕ) (hm : m ∈ Z) : C.eval (List.ofFn (row m) ++ List.replicate 11 true) = false := by
    have rows : ∀ m ∈ Z, ∃ k : Fin 27, cols.map (fun z => z.testBit k.val) = List.ofFn (row m) ++ List.replicate 11 true ∧ (4095 : ℕ).testBit k.val = false := by decide +kernel
    obtain ⟨k,hk,hout⟩ := rows m hm
    rw [← hk,pack C hG cols k.val]
    change ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) [70689, 5263618, 1046528, 47534084, 28520456, 3158096, 62080, 86679559, 134213632, 134213632, 134213632, 105693240, 126812608, 133172736, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632, 134213632]).getD C.output 0).testBit k.val = false
    rw [hw,hout]
  have cmp (x y : Fin 14 → Bool) (a b : List Bool)
      (hxy : ∀ i, x i = true → y i = true)
      (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (List.ofFn x ++ a).getD i false = true → (List.ofFn y ++ b).getD i false = true := by
    intro i hv
    by_cases hi : i < 14
    · have read (z : Fin 14 → Bool) : (List.ofFn z).getD i false = z ⟨i,hi⟩ := by
        have hz : i < (List.ofFn z).length := by simpa using hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz, List.getElem_ofFn]
        rfl
      rw [List.getD_append _ _ _ _ (by simpa using hi), read x] at hv
      rw [List.getD_append _ _ _ _ (by simpa using hi), read y]
      exact hxy _ hv
    · have hx : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt hi
      have hy : (List.ofFn y).length ≤ i := by simpa using Nat.le_of_not_lt hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hx, List.getElem?_append_right hy,
        List.length_ofFn] at hv ⊢
      simp only [List.getD_eq_getElem?_getD] at hab
      exact hab _ hv
  refine ⟨C,hs,ho,hou,hg,?_,hr⟩
  intro x a ha
  suffices h : C.eval (List.ofFn x ++ a) = true ↔ ∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true by
    simpa only [E, and_assoc] using h
  constructor
  · intro hv
    by_contra he
    obtain ⟨m,hm,hmp,hml⟩ := neg (fun i => x (Fin.castAdd 7 i))
    have sub : ∀ i, x i = true → row m i = true := by
      intro i hi
      by_cases hl : i.val < 7
      · let p : Fin 7 := ⟨i.val,hl⟩
        have eq : Fin.castAdd 7 p = i := Fin.ext rfl
        rw [← eq] at hi ⊢
        exact hmp p hi
      · let l : Fin 7 := ⟨i.val - 7, by omega⟩
        have eq : Fin.natAdd 7 l = i := Fin.ext (by simp [l]; omega)
        rw [← eq] at hi ⊢
        apply hml l
        intro p hepl
        cases hx : x (Fin.castAdd 7 p)
        · rfl
        · exact False.elim (he ⟨p,l,hepl,hx,hi⟩)
    have tail : ∀ i, a.getD i false = true → (List.replicate 11 true).getD i false = true := by
      intro i h
      by_cases hi : i < 11
      · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        simp only [hi, ite_true, Option.getD_some]
      · rw [List.getD_eq_default _ _ (by omega)] at h
        exact Bool.noConfusion h
    have hy := mono _ _ (by simp [ha]) (cmp x (row m) a (List.replicate 11 true) sub tail) hv
    exact Bool.noConfusion ((hn m hm).symm.trans hy)
  · rintro ⟨p,l,he,hxp,hxl⟩
    obtain ⟨m,hm,hm'⟩ := pos p l he
    have sub : ∀ i, row m i = true → x i = true := by
      intro i hi
      rcases hm' i hi with rfl | rfl
      · exact hxp
      · exact hxl
    have tail : ∀ i, (List.replicate 11 false).getD i false = true → a.getD i false = true := by
      intro i h
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
      by_cases hi : i < 11 <;> simp only [hi, ite_true, ite_false, Option.getD_some, Option.getD_none,
        Bool.false_eq_true] at h
    exact mono _ _ (by simp [ha]) (cmp (row m) x (List.replicate 11 false) a sub tail) (hp m hm)
