import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

-- Quotient wire values by equality on the 29 tests and order the operands.
-- The formula child excludes expansions below 17 literal occurrences.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3616_317
  (formula : ∃ P : Nat → Nat → Prop, (∀ x ∈ ([176460377,270729347,101974798,15276076,353501232,1778752,31244416,434112256,503379968,360410534,0,536870911] : List Nat), P x 1) ∧
    (∀ a b i j, P a i → P b j → P (a &&& b) (i+j) ∧ P (a ||| b) (i+j)) ∧
    (∀ k, P 65535 k → 17≤k))
  (search : ∀ gs : List (Bool × Nat × Nat), gs.length≤14 → (∀ g ∈ gs, g.2.1<g.2.2) →
    let xs := gs.foldl (fun (xs : List (Nat × Nat)) (g : Bool × Nat × Nat) =>
        let a := xs.getD g.2.1 (0,1)
        let b := xs.getD g.2.2 (0,1)
        xs ++ [(if g.1 then a.1 &&& b.1 else a.1 ||| b.1, a.2+b.2)]) (([176460377,270729347,101974798,15276076,353501232,1778752,31244416,434112256,503379968,360410534,0,536870911] : List Nat).map (fun a => (a,(1 : Nat))))
    (xs.map Prod.fst).Nodup → ∀ k, 17≤k → (65535,k)∉xs) :
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (∀ (x7 : Fin x1), (x3 x7).1 < (10 : ℕ) + ↑x7 ∧ (x4 x7).1 < (10 : ℕ) + ↑x7) →     x5.1 < (10 : ℕ) + x1 →       x5.2 = Bool.false →         x1 ≤ (14 : ℕ) →           (have x11 : ℕ × Bool → Prop := fun (x11 : ℕ × Bool) => x11.2 = Bool.true → x11.1 = (0 : ℕ) ∨ x11.1 = (9 : ℕ);             x11 x5 ∧ ∀ (x12 : Fin x1), x11 (x3 x12) ∧ x11 (x4 x12)) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin (9 : ℕ)), x6 x12 ↑x13 = x12 x13) →               (∀ (x13 : Fin (9 : ℕ) → Bool), x6 x13 (9 : ℕ) = Bool.false) →                 (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin x1),                     have x16 : ℕ × Bool → Bool := fun (x16 : ℕ × Bool) => x6 x14 x16.1 ^^ x16.2;                     x6 x14 ((10 : ℕ) + ↑x15) = if x2 x15 = Bool.true then x16 (x3 x15) && x16 (x4 x15) else x16 (x3 x15) || x16 (x4 x15)) →                   (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (133 : ℕ), (138 : ℕ), (160 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (265 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (385 : ℕ), (402 : ℕ)],                       have x17 : Fin (9 : ℕ) → Bool := fun (x17 : Fin (9 : ℕ)) => x15.testBit ↑x17;                       (x6 x17 x5.1 ^^ x5.2) = Decidable.decide (x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ)])) →                     False := by
  intro n op left right out value earlier rangeOut outPol size signs inputs zero trace agree
  let rows : List Nat := [3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321,42,50,69,104,116,138,200,201,208,261,276,385,402]
  let positives : List Nat := [3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321]
  let pack (rs : List Nat) (f : Nat → Bool) : Nat := rs.foldr (fun r k => Nat.bit (f r) k) 0
  let x (r : Nat) (i : Fin 9) := r.testBit i.val
  let signal (p : Nat × Bool) (r : Nat) := value (x r) p.1 ^^ p.2
  let word (p : Nat × Bool) := pack rows (signal p)
  let symbols : List Nat := [176460377,270729347,101974798,15276076,353501232,1778752,31244416,434112256,503379968,360410534,0,536870911]
  let init := symbols.map (fun a => (a,(1 : Nat)))
  let add := (fun (xs : List (Nat × Nat)) (g : Bool × Nat × Nat) =>
        let a := xs.getD g.2.1 (0,1)
        let b := xs.getD g.2.2 (0,1)
        xs ++ [(if g.1 then a.1 &&& b.1 else a.1 ||| b.1, a.2+b.2)])
  let run (gs : List (Bool × Nat × Nat)) := gs.foldl add init
  let combineWords (o : Bool) (a b : Nat) := if o then a &&& b else a ||| b
  have combine (rs : List Nat) (f g : Nat → Bool) (o : Bool) :
      pack rs (fun r => if o then f r && g r else f r || g r) = combineWords o (pack rs f) (pack rs g) := by
    induction rs with
    | nil => cases o <;> simp [pack,combineWords]
    | cons r rs ih =>
      cases o <;> simp only [pack,combineWords,List.foldr_cons,Bool.false_eq_true,ite_false,ite_true,
        Nat.lor_bit,Nat.land_bit] at ih ⊢ <;> rw [ih]
  have packEq (rs : List Nat) (f g : Nat → Bool) (h : ∀ r ∈ rs, f r=g r) : pack rs f=pack rs g := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      change Nat.bit (f r) (pack rs f) = Nat.bit (g r) (pack rs g)
      rw [h r List.mem_cons_self,ih (fun t ht => h _ (List.mem_cons_of_mem _ ht))]
  have inputNat (p : Nat × Bool) (hp : p.1<10) (hs : p.2=true → p.1=0 ∨ p.1=9) :
      word p ∈ symbols := by
    obtain ⟨k,b⟩ := p
    simp only at hp hs
    cases b with
    | false =>
      by_cases h : k<9
      · let i : Fin 9 := ⟨k,h⟩
        have eq : word (k,false) = pack rows (fun r => r.testBit i.val) := by
          apply packEq
          intro r _
          simpa [signal,x] using inputs (x r) i
        rw [eq]
        exact (show ∀ j : Fin 9, pack rows (fun r => r.testBit j.val) ∈ symbols by decide +kernel) i
      · have e : k=9 := by omega
        subst k
        have eq : word (9,false)=pack rows (fun _ => false) := by
          apply packEq; intro r _; simp [signal,zero]
        rw [eq]; decide +kernel
    | true =>
      rcases hs rfl with rfl|rfl
      · have eq : word (0,true)=pack rows (fun r => !r.testBit 0) := by
          apply packEq; intro r _
          have e := inputs (x r) 0
          simp [signal,x] at e ⊢
          exact e
        rw [eq]; decide +kernel
      · have eq : word (9,true)=pack rows (fun _ => true) := by
          apply packEq; intro r _; simp [signal,zero]
        rw [eq]; decide +kernel
  have gateWord (j : Fin n) :
      word (10+j.val,false) = combineWords (op j) (word (left j)) (word (right j)) := by
    refine (packEq rows _ _ ?_).trans (combine rows (signal (left j)) (signal (right j)) (op j))
    intro r _
    simpa [signal] using trace (x r) j
  have get (vs : List (Nat × Nat)) {a : Nat × Nat} (ha : a∈vs) :
      ∃ i, vs.getD i (0,1)=a := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem ha
    exact ⟨i,by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq⟩
  have sim (m : Nat) (hm : m≤n) :
      ∃ gs : List (Bool × Nat × Nat), gs.length≤m ∧ (∀ g ∈ gs, g.2.1<g.2.2) ∧
        ((run gs).map Prod.fst).Nodup ∧ ∀ p : Nat × Bool, p.1<10+m →
          (p.2=true → p.1=0 ∨ p.1=9) → word p ∈ (run gs).map Prod.fst := by
    induction m with
    | zero =>
      refine ⟨[],by decide,by simp,by decide +kernel,?_⟩
      intro p hp hs
      have h := inputNat p hp hs
      exact List.mem_map.mpr ⟨(word p,1),List.mem_map.mpr ⟨word p,h,rfl⟩,rfl⟩
    | succ m ih =>
      obtain ⟨gs,sz,ord,uniq,seen⟩ := ih (by omega)
      let j : Fin n := ⟨m,by omega⟩
      let vs := run gs
      let y := word (10+m,false)
      have extend (ts : List (Nat × Nat)) (inc : vs ⊆ ts) (hy : y∈ts.map Prod.fst) :
          ∀ p : Nat × Bool, p.1<10+(m+1) → (p.2=true → p.1=0 ∨ p.1=9) → word p∈ts.map Prod.fst := by
        intro p hp hs
        by_cases h : p.1<10+m
        · obtain ⟨z,hz,eq⟩ := List.mem_map.mp (seen p h hs)
          exact List.mem_map.mpr ⟨z,inc hz,eq⟩
        · have e : p.1=10+m := by omega
          have b : p.2=false := by
            cases hb : p.2 with
            | false => rfl
            | true => rcases hs hb with h|h <;> omega
          have eq : p=(10+m,false) := Prod.ext e b
          exact eq ▸ hy
      by_cases existsY : y∈vs.map Prod.fst
      · exact ⟨gs,by omega,ord,uniq,extend vs (fun _ h => h) existsY⟩
      · obtain ⟨a,ha,ea⟩ := List.mem_map.mp (seen (left j) (earlier j).1 (signs.2 j).1)
        obtain ⟨b,hb,eb⟩ := List.mem_map.mp (seen (right j) (earlier j).2 (signs.2 j).2)
        obtain ⟨i,hi⟩ := get vs ha
        obtain ⟨k,hk⟩ := get vs hb
        have eq : y=combineWords (op j) a.1 b.1 := by simpa only [ea,eb] using gateWord j
        have ne : i≠k := by
          rintro rfl
          have ab := hi.symm.trans hk
          have same : y=a.1 := by rw [eq,←ab]; cases op j <;> simp [combineWords]
          exact existsY (same ▸ List.mem_map.mpr ⟨a,ha,rfl⟩)
        let g : Bool × Nat × Nat := (op j,min i k,max i k)
        let res : Nat × Nat := (y,a.2+b.2)
        have update : run (gs++[g])=vs++[res] := by
          change (gs++[g]).foldl add init = _
          rw [List.foldl_append]
          change add vs g = _
          by_cases ik : i≤k
          · simp only [add,g,min_eq_left ik,max_eq_right ik,hi,hk,res,eq,combineWords]
          · have ki : k ≤ i := by omega
            simp only [add,g,min_eq_right ki,max_eq_left ki,hi,hk,res,eq,combineWords]
            cases op j <;> simp [Nat.and_comm,Nat.or_comm,Nat.add_comm]
        refine ⟨gs++[g],by simp; omega,?_,?_,?_⟩
        · intro t ht
          rcases List.mem_append.mp ht with h|h
          · exact ord _ h
          · obtain rfl := List.mem_singleton.mp h
            change min i k < max i k
            omega
        · rw [update,List.map_append]
          apply List.nodup_append.mpr
          refine ⟨uniq,by simp,?_⟩
          intro z hz b hb e
          have be : b=y := by simpa [res] using hb
          exact existsY ((e.trans be) ▸ hz)
        · rw [update]
          exact extend _ (fun _ h => List.mem_append_left _ h) (List.mem_map.mpr ⟨res,by simp,rfl⟩)
  obtain ⟨gs,sz,ord,uniq,seen⟩ := sim n le_rfl
  have output := seen out rangeOut signs.1
  have eqOut : word out = 65535 := by
    have incl : ∀ r ∈ rows, r ∈ ([3,6,12,13,17,24,33,42,50,66,69,104,116,132,133,138,160,200,201,208,261,264,265,276,288,320,321,385,402] : List Nat) := by decide +kernel
    have eq := packEq rows (signal out) (fun r => decide (r∈positives)) (fun r hr => agree _ (incl _ hr))
    exact eq.trans (by decide +kernel)
  rw [eqOut] at output
  obtain ⟨⟨z,k⟩,member,eq⟩ := List.mem_map.mp output
  change z=65535 at eq
  subst z
  obtain ⟨P,base,closed,bound⟩ := formula
  have all (ls : List (Bool × Nat × Nat)) (vs : List (Nat × Nat)) (hold : ∀ a ∈ vs,P a.1 a.2) :
      ∀ a ∈ ls.foldl add vs,P a.1 a.2 := by
    induction ls generalizing vs with
    | nil => exact hold
    | cons g ls ih =>
      apply ih
      intro t ht
      rcases List.mem_append.mp ht with h|h
      · exact hold t h
      · have good (i : Nat) : P (vs.getD i (0,1)).1 (vs.getD i (0,1)).2 := by
          by_cases h : i<vs.length
          · simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some] using hold _ (List.getElem_mem h)
          · simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : vs.length ≤ i),Option.getD_none] using base 0 (by decide)
        obtain rfl := List.mem_singleton.mp h
        have both := closed _ _ _ _ (good g.2.1) (good g.2.2)
        cases e : g.1
        · simpa only [e,Bool.false_eq_true,ite_false] using both.2
        · simpa only [e,ite_true] using both.1
  have hk := all gs init (by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact base b hb) (65535,k) member
  exact search gs (by omega) ord uniq k (bound k hk) member
