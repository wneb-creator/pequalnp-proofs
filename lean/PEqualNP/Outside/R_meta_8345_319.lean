import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8345_319
    (trim : ∀ (base : List ℕ),
    let f := fun (s : List ℕ) (g : Gate) =>
      let a := s.getD (g.inputs.getD 0 0) 0
      let b := s.getD (g.inputs.getD 1 0) 0
      s++[if g.op.eval [false,true]=true then a ||| b else a &&& b]
    let v (C : Circuit) (w : ℕ) := (C.gates.foldl f base).getD w 0
    let prod := fun (C : Circuit) (e : ℕ×ℕ) => v C e.1 &&& v C e.2
    let bounds := fun (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) => ∀ e∈T, e.1<n+C.size ∧ e.2<n+C.size
    let live := fun (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) =>
      ∀ j<C.size, ReadTwo.isAnd C j → ∃ e∈T, ∃ w∈[e.1,e.2],
        w=n+j ∨ n≤w ∧ EdgeOwnership.InCone n C j (w-n)
    ∀ (C : Circuit) (T : List (ℕ×ℕ)), IsAO2 base.length C → bounds base.length C T →
      ¬live base.length C T → ∃ (D : Circuit) (L : List (ℕ×ℕ)), IsAO2 base.length D ∧
      bounds base.length D L ∧ D.size+1=C.size ∧ ReadTwo.nAnd C≤ReadTwo.nAnd D+1 ∧
      L.length=T.length ∧ L.map (prod D)=T.map (prod C) ∧
      ∀ j<D.size, ∃ k<C.size, v D (base.length+j)=v C (base.length+k))
    (lift : ∀ (n : ℕ) (C : Circuit) (a b : ℕ) (T : List (ℕ×ℕ)),
    let D : Circuit := ⟨C.gates++[⟨.and,[a,a]⟩],C.output⟩
    let live := fun (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) =>
      ∀ j<C.size, ReadTwo.isAnd C j → ∃ e∈T, ∃ w∈[e.1,e.2],
        w=n+j ∨ n≤w ∧ EdgeOwnership.InCone n C j (w-n)
    IsAO2 n C → a<n+C.size → live n C ((a,b)::T) → live n D ((n+C.size,b)::T))
    (cheap : let base : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
    let f := fun (s : List ℕ) (g : Gate) =>
      let a := s.getD (g.inputs.getD 0 0) 0
      let b := s.getD (g.inputs.getD 1 0) 0
      s++[if g.op.eval [false,true]=true then a ||| b else a &&& b]
    let v (C : Circuit) (w : ℕ) := (C.gates.foldl f base).getD w 0
    let prod := fun (C : Circuit) (e : ℕ×ℕ) => v C e.1 &&& v C e.2
    let dirty := fun (z : ℕ) => (∃ i : Fin 16,z.testBit i.val = true) ∧ ∃ i : Fin 24,z.testBit (16+i.val)=true
    ∃ (C : Circuit) (T : List (ℕ×ℕ)), IsAO2 11 C ∧ T≠[] ∧
      C.size+(3-ReadTwo.nAnd C)+2*T.length≤22 ∧
      (∀ e∈T, e.1<11+C.size ∧ e.2<11+C.size) ∧
      (∀ j<C.size, dirty (v C (11+j))) ∧
      (T.map (prod C)).foldl (fun (y z : ℕ) => y ||| z) 0=65535)
    : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ :=     List.foldl       (fun (x3 : List ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) =>         have x5 : ℕ := x3.getD (x4.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x6 : ℕ := x3.getD (x4.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x3 ++ [if x4.op.eval [Bool.false, Bool.true] = Bool.true then x5 ||| x6 else x5 &&& x6])       [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] x1.gates;   have x4 : ℕ → ℕ := fun (x4 : ℕ) => x3.getD x4 (0 : ℕ);   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x5 ∈ x2, x5.1 < (11 : ℕ) + x1.size ∧ x5.2 < (11 : ℕ) + x1.size) ∧ (∀ x5 < x1.size, (∃ (x7 : Fin (16 : ℕ)), (x4 ((11 : ℕ) + x5)).testBit ↑x7 = Bool.true) ∧ ∃ (x7 : Fin (24 : ℕ)), (x4 ((11 : ℕ) + x5)).testBit ((16 : ℕ) + ↑x7) = Bool.true) ∧ (∀ x5 < x1.size, PEqualNP.ReadTwo.isAnd x1 x5 → ∃ x8 ∈ x2, ∃ x9 ∈ [x8.1, x8.2], x9 = (11 : ℕ) + x5 ∨ (11 : ℕ) ≤ x9 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x5 (x9 - (11 : ℕ))) ∧ List.foldl (fun (x5 : ℕ) (x6 : ℕ × ℕ) => x5 ||| x4 x6.1 &&& x4 x6.2) (0 : ℕ) x2 = (65535 : ℕ)) := by
  classical
  let base : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let f := fun (s : List ℕ) (g : Gate) =>
      let a := s.getD (g.inputs.getD 0 0) 0
      let b := s.getD (g.inputs.getD 1 0) 0
      s++[if g.op.eval [false,true]=true then a ||| b else a &&& b]
  let v (C : Circuit) (w : ℕ) := (C.gates.foldl f base).getD w 0
  let prod := fun (C : Circuit) (e : ℕ×ℕ) => v C e.1 &&& v C e.2
  let bounds := fun (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) => ∀ e∈T, e.1<n+C.size ∧ e.2<n+C.size
  let live := fun (n : ℕ) (C : Circuit) (T : List (ℕ×ℕ)) =>
      ∀ j<C.size, ReadTwo.isAnd C j → ∃ e∈T, ∃ w∈[e.1,e.2],
        w=n+j ∨ n≤w ∧ EdgeOwnership.InCone n C j (w-n)
  let dirty := fun (z : ℕ) => (∃ i : Fin 16,z.testBit i.val = true) ∧ ∃ i : Fin 24,z.testBit (16+i.val)=true
  let ok (C : Circuit) (T : List (ℕ×ℕ)) :=
    IsAO2 11 C ∧ T ≠ [] ∧ C.size+(3-ReadTwo.nAnd C)+2*T.length≤22 ∧
    bounds 11 C T ∧ (∀ j<C.size, dirty (v C (11+j))) ∧ (T.map (prod C)).foldl (fun (y z : ℕ) => y ||| z) 0=65535
  obtain ⟨C,T,hw⟩ := cheap
  change ok C T at hw
  have cut (s : ℕ) (A : Circuit) (L : List (ℕ×ℕ)) (eqs : A.size=s) (H : ok A L) :
      ∃ (B : Circuit) (U : List (ℕ×ℕ)), ok B U ∧ live 11 B U := by
    induction s generalizing A L with
    | zero =>
      refine ⟨A,L,H,?_⟩
      intro j hj
      omega
    | succ s ih =>
      by_cases liveA : live 11 A L
      · exact ⟨A,L,H,liveA⟩
      · obtain ⟨model,ne,price,bd,good,sig⟩ := H
        obtain ⟨B,U,modelB,ubd,sm,count,len,pairs,keep⟩ := trim base A L model bd liveA
        have sizeB : B.size=s := by omega
        apply ih B U sizeB
        refine ⟨modelB,?_,?_,ubd,?_,?_⟩
        · intro e
          have := List.length_eq_zero_iff.mpr e
          exact ne (List.length_eq_zero_iff.mp (by omega))
        · omega
        · intro j hj
          obtain ⟨k,hk,eq⟩ := keep j hj
          change v B (11+j)=v A (11+k) at eq
          rw [eq]
          exact good k hk
        · change (U.map (prod B)).foldl (fun (y z : ℕ) => y ||| z) 0 = _
          change U.map (prod B)=L.map (prod A) at pairs
          rw [pairs]; exact sig
  obtain ⟨B,U,okB,liveB⟩ := cut C.size C T rfl hw
  have lenFold (gs : List Gate) (s : List ℕ) : (gs.foldl f s).length=s.length+gs.length := by
    induction gs generalizing s with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [f]
      omega
  have rawGood : ∀ i : Fin 11, dirty (base.getD i.val 0) := by decide +kernel
  have raw (A : Circuit) (i : Fin 11) : v A i.val=base.getD i.val 0 := by
    have pre (gs : List Gate) (s : List ℕ) : ∃ z, gs.foldl f s=s++z := by
      induction gs generalizing s with
      | nil => exact ⟨[],by simp⟩
      | cons g gs ih =>
        obtain ⟨z,hz⟩ := ih (f s g)
        rw [List.foldl_cons,hz]
        dsimp only [f]
        rw [List.append_assoc]
        exact ⟨_,rfl⟩
    obtain ⟨z,h⟩ := pre A.gates base
    simp only [v,h,List.getD_eq_getElem?_getD,List.getElem?_append_left (show i.val<base.length from i.isLt)]
  have pad (k : ℕ) (A : Circuit) (L : List (ℕ×ℕ)) (hk : 3-ReadTwo.nAnd A=k) (H : ok A L) (used : live 11 A L) :
      ∃ (D : Circuit) (M : List (ℕ×ℕ)), ok D M ∧ live 11 D M ∧ 3≤ReadTwo.nAnd D := by
    induction k generalizing A L with
    | zero => exact ⟨A,L,H,used,by omega⟩
    | succ k ih =>
      obtain ⟨model,ne,price,bd,good,sig⟩ := H
      cases L with
      | nil => exact False.elim (ne rfl)
      | cons e rest =>
        let a := e.1
        let b := e.2
        let g : Gate := ⟨.and,[a,a]⟩
        let D : Circuit := ⟨A.gates++[g],A.output⟩
        let w := 11+A.size
        let M := (w,b)::rest
        have ab := bd e (List.mem_cons_self ..)
        have ha : a<w := ab.1
        have hb : b<w := ab.2
        have sz : D.size=A.size+1 := by
          change (A.gates++[g]).length=A.gates.length+1
          simp
        have ands : ReadTwo.nAnd D=ReadTwo.nAnd A+1 := by
          delta ReadTwo.nAnd
          simp [D,g,List.filter_append]
        have ed : v D w = v A a := by
          let s := A.gates.foldl f base
          have len : s.length=w := lenFold A.gates base
          change ((A.gates++[g]).foldl f base).getD w 0 = s.getD a 0
          rw [List.foldl_append]
          change (s++[s.getD a 0 &&& s.getD a 0]).getD w 0 = _
          rw [←len]
          simp
        have keep {i : ℕ} (h : i<w) : v D i=v A i := by
          let s := A.gates.foldl f base
          have len : s.length=w := lenFold A.gates base
          change ((A.gates++[g]).foldl f base).getD i 0 = s.getD i 0
          rw [List.foldl_append]
          change (s++[_]).getD i 0=_
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (show i<s.length by omega)]
        have modelD : IsAO2 11 D := by
          refine ⟨?_,?_,?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact model.1 q h
            · obtain rfl : q=g := List.mem_singleton.mp h
              exact Or.inl rfl
          · intro j hj i hi
            by_cases early : j<A.gates.length
            · have atj : gateAt D j=gateAt A j := by
                delta gateAt
                simp [D,List.getD_eq_getElem?_getD,List.getElem?_append_left early]
              rw [atj] at hi
              exact model.2.1 j early i hi
            · change j<D.size at hj
              have last : j=A.gates.length := by change ¬j<A.size at early; change j=A.size; omega
              subst j
              have atj : gateAt D A.gates.length=g := by delta gateAt; simp [D]
              rw [atj] at hi
              have hi' : i=a := by simpa [g] using hi
              rw [hi']
              exact ha
          · intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact model.2.2 q h
            · obtain rfl : q=g := List.mem_singleton.mp h
              rfl
        have liveD : live 11 D M := lift 11 A a b rest model ha used
        apply ih D M (by omega) _ liveD
        refine ⟨modelD,by simp [M],?_,?_,?_,?_⟩
        · have eql : M.length=(e::rest).length := rfl
          omega
        · intro z hz
          rcases List.mem_cons.mp hz with h | h
          · subst z
            exact ⟨by change 11+A.size < 11+D.size; omega,by change b < 11+D.size; dsimp [w] at hb; omega⟩
          · obtain ⟨l,r⟩ := bd z (List.mem_cons_of_mem _ h)
            exact ⟨by omega,by omega⟩
        · intro j hj
          by_cases early : j<A.size
          · rw [keep (show 11+j<w by dsimp [w]; omega)]
            exact good j early
          · have hj' : j=A.size := by omega
            subst j
            change dirty (v D w)
            rw [ed]
            by_cases inp : a<11
            · exact (raw A ⟨a,inp⟩) ▸ rawGood ⟨a,inp⟩
            · have ae : a=11+(a-11) := by omega
              have bnd : a-11<A.size := by dsimp [w] at ha; omega
              simpa only [←ae] using good (a-11) bnd
        · have terms : rest.map (prod D)=rest.map (prod A) := by
            apply List.map_congr_left
            intro z hz
            have hit := bd z (List.mem_cons_of_mem _ hz)
            simp only [prod,keep hit.1,keep hit.2]
          change ((prod D (w,b))::rest.map (prod D)).foldl (fun (y z : ℕ) => y ||| z) 0 = _
          change ((prod A e)::rest.map (prod A)).foldl (fun (y z : ℕ) => y ||| z) 0 = _ at sig
          simpa only [terms,prod,ed,keep hb] using sig
  obtain ⟨D,M,H,liveD,many⟩ := pad _ B U rfl okB liveB
  obtain ⟨model,ne,price,bd,good,sig⟩ := H
  refine ⟨D,M,model,ne,by omega,many,bd,good,liveD,?_⟩
  change M.foldl (fun s e => s ||| prod D e) 0 = 65535
  simpa only [List.foldl_map,Function.comp_def,Nat.lor_eq] using sig
