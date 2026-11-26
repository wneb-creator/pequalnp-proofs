import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5687_481
    (compile : ∀ C : Circuit, Monotone2 C → C.size ≤ 18 →
      ∃ (p : List (Bool × ℕ × ℕ)) (o : ℕ), p.length ≤ 18 ∧ o < 13 + p.length ∧
        (∀ j g, p[j]? = some g → g.2.1 < 13+j ∧ g.2.2 < 13+j) ∧
        ∀ x : List Bool, x.length = 11 →
          ((p.foldl (fun (w : List Bool) t =>
            let a := w.getD t.2.1 false
            let b := w.getD t.2.2 false
            w ++ [if t.1 = true then a && b else a || b]) (false :: true :: x)).getD o false) = C.eval x)
    (exclude : let cols : List ℕ := [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048]
      ∀ a b : Fin 11, ∀ (p : List (Bool × ℕ × ℕ)) (o : ℕ), p.length ≤ 18 → o < 13 + p.length →
        (∀ j g, p[j]? = some g → g.2.1 < 13+j ∧ g.2.2 < 13+j) →
          let w := 0 :: 1073741823 :: (cols ++ [cols.getD a.val 0 ||| cols.getD b.val 0])
          let z := p.foldl (fun (w : List ℕ) t =>
            let a := w.getD t.2.1 0
            let b := w.getD t.2.2 0
            w ++ [if t.1 = true then a &&& b else a ||| b]) w
          z.getD o 0 &&& 1073741823 ≠ 32767) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).any id]) ≠ x6.2 := by
  intro C s hm hs hlen
  by_contra fail
  let r : List ℕ := [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
  let cols : List ℕ := [579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048]
  let row (i : ℕ) := List.ofFn (fun j : Fin 10 => (r.getD i 0).testBit j.val)
  have rows : ∀ i : Fin 30, row i.val = cols.map (fun w => w.testBit i.val) := by decide +kernel
  have covered : ∀ i : Fin 30, (r.getD i.val 0, (32767 : ℕ).testBit i.val) ∈
      ([((3 : ℕ),true),(6,true),(12,true),(24,true),(17,true),(33,true),(66,true),(132,true),(264,true),(528,true),(160,true),(640,true),(576,true),(320,true),(288,true),(50,false),(69,false),(104,false),(116,false),(138,false),(201,false),(208,false),(276,false),(385,false),(402,false),(521,false),(548,false),(554,false),(770,false),(773,false)] : List (ℕ × Bool)) := by decide +kernel
  let norm (j : ℕ) : Fin 11 := if h : j < 10 then ⟨j, by omega⟩ else 10
  have sz (i : ℕ) : (row i).length = 10 := List.length_ofFn
  have rd (i j : ℕ) : (row i).getD (norm j).val false = (row i).getD j false := by
    by_cases h : j < 10
    · simp [norm,h]
    · have h₁ : (row i).length ≤ (norm j).val := by simp [sz,norm,h]
      have h₂ : (row i).length ≤ j := by rw [sz]; omega
      rw [List.getD_eq_default _ _ h₁, List.getD_eq_default _ _ h₂]
  obtain ⟨a,b,extra⟩ : ∃ a b : Fin 11, ∀ i,
      ((row i).getD a.val false || (row i).getD b.val false) = (s.map (fun j => (row i).getD j false)).any id := by
    rcases s with _ | ⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
    · refine ⟨10,10,fun i => ?_⟩
      have h : (row i).length ≤ 10 := by rw [sz]
      simp only [List.map_nil, List.any_nil]
      rw [show (10 : Fin 11).val = 10 from rfl, List.getD_eq_default _ _ h]
      rfl
    · refine ⟨norm a,10,fun i => ?_⟩
      have h : (row i).length ≤ 10 := by rw [sz]
      rw [rd i a, show (10 : Fin 11).val = 10 from rfl, List.getD_eq_default _ _ h]
      simp only [Bool.or_false, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
    · exact ⟨norm a,norm b,fun i => by simp only [rd, List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]⟩
    · simp at hlen
  obtain ⟨p,o,hp,ho,hord,sim⟩ := compile C hm hs
  let w := 0 :: 1073741823 :: (cols ++ [cols.getD a.val 0 ||| cols.getD b.val 0])
  let ns := fun (w : List ℕ) (t : Bool × ℕ × ℕ) =>
    let a := w.getD t.2.1 0
    let b := w.getD t.2.2 0
    w ++ [if t.1 = true then a &&& b else a ||| b]
  let bs := fun (w : List Bool) (t : Bool × ℕ × ℕ) =>
    let a := w.getD t.2.1 false
    let b := w.getD t.2.2 false
    w ++ [if t.1 = true then a && b else a || b]
  have bit (i : ℕ) (xs : List ℕ) (j : ℕ) :
      (xs.map (fun z => z.testBit i)).getD j false = (xs.getD j 0).testBit i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases xs[j]? <;> simp
  have fold (i : ℕ) (q : List (Bool × ℕ × ℕ)) (xs : List ℕ) :
      (q.foldl ns xs).map (fun z => z.testBit i) = q.foldl bs (xs.map fun z => z.testBit i) := by
    induction q generalizing xs with
    | nil => rfl
    | cons t q ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      have ht : (ns xs t).map (fun z => z.testBit i) = bs (xs.map fun z => z.testBit i) t := by
        simp only [ns,bs,List.map_append,List.map_cons,List.map_nil,bit]
        cases h : t.1 <;> simp [h, Nat.testBit_and, Nat.testBit_or]
      rw [ht]
  apply exclude a b p o hp ho hord
  change (p.foldl ns w).getD o 0 &&& 1073741823 = 32767
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 30
  · let k : Fin 30 := ⟨i,hi⟩
    have hone : (1073741823 : ℕ).testBit i = true := (by decide +kernel : ∀ j : Fin 30, (1073741823 : ℕ).testBit j.val = true) k
    have extlen : (row i ++ [(s.map (fun j => (row i).getD j false)).any id]).length = 11 := by simp [sz]
    have input : w.map (fun z => z.testBit i) = false :: true :: (row i ++ [(s.map (fun j => (row i).getD j false)).any id]) := by
      change _ = _
      simp only [w,List.map_cons,List.map_append,List.map_nil,Nat.zero_testBit,hone,Nat.testBit_or]
      rw [← bit i cols a.val, ← bit i cols b.val, ← rows k, extra i]
    have exact_row : C.eval (row i ++ [(s.map (fun j => (row i).getD j false)).any id]) = (32767 : ℕ).testBit i := by
      by_contra bad
      exact fail ⟨(r.getD i 0,(32767 : ℕ).testBit i), covered k, bad⟩
    rw [Nat.testBit_and, hone, Bool.and_true, ← bit i (p.foldl ns w) o, fold, input]
    exact (sim _ extlen).trans exact_row
  · have hpow : 2 ^ 30 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hmask : (1073741823 : ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1073741823 < 2 ^ 30) hpow)
    have htarget : (32767 : ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 32767 < 2 ^ 30) hpow)
    rw [Nat.testBit_and,hmask,htarget,Bool.and_false]
