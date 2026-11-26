import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8174_386
    (compile : ∀ (n : ℕ) (C : Circuit) (groups : List (Fin n × List (Fin n))),
      IsAO2 n C → (∀ g ∈ groups, 2 ≤ g.2.length) →
      ∃ (D : Circuit) (L : List (ℕ × ℕ)) (extra : List Gate),
        D.gates = C.gates ++ extra ∧ (∀ g ∈ extra, g.op = .or) ∧ IsAO2 n D ∧
        extra.length + groups.length ≤ (groups.map (fun g => g.2.length)).sum ∧
        L.length = groups.length ∧
        (∀ e ∈ L, e.1 < n+D.size ∧ e.2 < n+D.size ∧ n ≤ e.2) ∧
        (∀ x : Fin n → Bool, (L.any fun e =>
          BlindGate.wireValue D n x e.1 && BlindGate.wireValue D n x e.2) =
          groups.any fun g => x g.1 && g.2.any x) ∧
        ∀ j, C.size ≤ j → j < D.size → ∃ i : Fin n, ∀ x : Fin n → Bool,
          x i = true → BlindGate.wireValue D n x (n+j) = true)
    (groupRows : ∀ (n : ℕ) (R N : List ℕ) (S : Finset (Fin n)),
      (∀ r ∈ R, r ∉ N) → (∀ r ∈ R, ∃ u ∈ S, r.testBit u.val = true) →
      (∀ r ∈ R, ∀ u : Fin n, r.testBit u.val = true → ∃ v : Fin n, ∀ t ∈ R ++ N,
        (t.testBit u.val && t.testBit v.val) = decide (t = r)) →
      ∃ groups : List (Fin n × List (Fin n)), (∀ g ∈ groups, 2 ≤ g.2.length) ∧
        let h := fun (r : ℕ) => groups.any fun g => r.testBit g.1.val && g.2.any (fun v => r.testBit v.val)
        (groups.map (fun g => g.2.length+1)).sum + 2*(R.filter fun r => !(h r)).length ≤ R.length+S.card ∧
          ∀ t ∈ N, h t = false)
    (core : ∃ (C : Circuit) (T : List (ℕ × ℕ)) (S : Finset (Fin 11)),
      let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let N : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let v (r w : ℕ) := BlindGate.wireValue C 11 (fun i => r.testBit i.val) w
      let hit (r : ℕ) := T.any fun e => v r e.1 && v r e.2
      let R := P.filter fun r => !(hit r)
      IsAO2 11 C ∧ T ≠ [] ∧ 3 ≤ ReadTwo.nAnd C ∧
      C.size + 2*T.length + R.length + S.card ≤ 22 ∧
      (∀ r ∈ R, ∃ u ∈ S, r.testBit u.val = true) ∧
      (∀ e ∈ T, e.1 < 11+C.size ∧ e.2 < 11+C.size ∧ (11≤e.1 ∨ 11≤e.2)) ∧
      (∀ j < C.size, (P.any fun r => v r (11+j)) = true ∧ (N.any fun r => v r (11+j)) = true) ∧
      (∀ j < C.size, ReadTwo.isAnd C j → ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
        w=11+j ∨ 11≤w ∧ EdgeOwnership.InCone 11 C j (w-11)) ∧
      ∀ t ∈ N, hit t = false)
    : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   have x6 : ℕ → Bool := fun (x6 : ℕ) => x2.any fun (x7 : ℕ × ℕ) => x5 x6 x7.1 && x5 x6 x7.2;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * (x2.length + (List.filter (fun (x7 : ℕ) => !x6 x7) x3).length) ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x7 ∈ x2, x7.1 < (11 : ℕ) + x1.size ∧ x7.2 < (11 : ℕ) + x1.size ∧ ((11 : ℕ) ≤ x7.1 ∨ (11 : ℕ) ≤ x7.2)) ∧ (∀ x7 < x1.size, (x3.any fun (x9 : ℕ) => x5 x9 ((11 : ℕ) + x7)) = Bool.true ∧ (x4.any fun (x9 : ℕ) => x5 x9 ((11 : ℕ) + x7)) = Bool.true) ∧ (∀ x7 < x1.size, PEqualNP.ReadTwo.isAnd x1 x7 → ∃ x10 ∈ x2, ∃ x11 ∈ [x10.1, x10.2], x11 = (11 : ℕ) + x7 ∨ (11 : ℕ) ≤ x11 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x7 (x11 - (11 : ℕ))) ∧ ∀ x7 ∈ x4, x6 x7 = Bool.false) := by
  classical
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let N : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let row (r : ℕ) (i : Fin 11) := r.testBit i.val
  obtain ⟨C,T,S,model,nonempty,ands,budget,covered,valid,dirty,paths,safe⟩ := core
  let old (r : ℕ) := T.any fun e => BlindGate.wireValue C 11 (row r) e.1 && BlindGate.wireValue C 11 (row r) e.2
  let R := P.filter fun r => !(old r)
  change C.size+2*T.length+R.length+S.card ≤ 22 at budget
  change ∀ r ∈ R, ∃ u ∈ S, r.testBit u.val = true at covered
  have sep : ∀ r ∈ P, r ∉ N := by decide +kernel
  have pair : ∀ r ∈ P, ∀ u : Fin 11, r.testBit u.val = true → ∃ v : Fin 11,
      ∀ t ∈ P ++ N, (t.testBit u.val && t.testBit v.val) = decide (t=r) := by decide +kernel
  have sub {r : ℕ} (hr : r ∈ R) : r ∈ P := (List.mem_filter.mp hr).1
  obtain ⟨groups,wide,price,reject⟩ := groupRows 11 R N S (fun r hr => sep r (sub hr)) covered
    (fun r hr u hu => by
      obtain ⟨v,hv⟩ := pair r (sub hr) u hu
      refine ⟨v,fun t ht => hv t ?_⟩
      exact (List.mem_append.mp ht).elim (fun h => List.mem_append_left _ (sub h)) (List.mem_append_right _))
  let star (r : ℕ) := groups.any fun g => row r g.1 && g.2.any (row r)
  change (groups.map fun g => g.2.length+1).sum + 2*(R.filter fun r => !(star r)).length ≤ R.length+S.card at price
  obtain ⟨D,L,extra,shape,onlyOr,modelD,cost,count,bounded,computes,pure⟩ := compile 11 C groups model wide
  have sizes : D.size = C.size+extra.length := by
    change D.gates.length = C.gates.length + extra.length
    rw [shape,List.length_append]
  have still {w : ℕ} (hw : w < 11+C.size) (x : Fin 11 → Bool) :
      BlindGate.wireValue D 11 x w = BlindGate.wireValue C 11 x w := by
    let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
    have aux (gs : List Gate) (v : List Bool) : ∃ z, gs.foldl step v = v ++ z := by
      induction gs generalizing v with
      | nil => exact ⟨[],by simp⟩
      | cons g gs ih =>
        obtain ⟨z,hz⟩ := ih (step v g)
        exact ⟨g.op.eval (g.inputs.map fun i => v.getD i false)::z,by simpa [step,List.append_assoc] using hz⟩
    have len (gs : List Gate) (v : List Bool) : (gs.foldl step v).length = v.length+gs.length := by
      induction gs generalizing v with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons,ih]
        simp [step]
        omega
    let v := C.gates.foldl step (List.ofFn x)
    have before : w < v.length := by simpa [v,len] using (show w < 11+C.gates.length from hw)
    obtain ⟨z,hz⟩ := aux extra v
    change (D.gates.foldl step (List.ofFn x)).getD w false = v.getD w false
    rw [shape,List.foldl_append]
    change (extra.foldl step v).getD w false = _
    simp only [hz,List.getD_eq_getElem?_getD,List.getElem?_append_left before]
  have gateOld (j : ℕ) (hj : j < C.size) : gateAt D j=gateAt C j := by
    delta gateAt
    simp [shape,List.getD_eq_getElem?_getD,List.getElem?_append_left (show j<C.gates.length from hj)]
  have kind {j : ℕ} (ha : ReadTwo.isAnd D j) : j < C.size := by
    by_contra! hn
    have dj : j < D.gates.length := ha.1
    have hlen : j-C.size < extra.length := by change j < D.size at dj; omega
    have hop : (gateAt D j).op = .or := by
      delta gateAt
      simp only [shape,List.getD_eq_getElem?_getD,List.getElem?_append_right (show C.gates.length ≤ j from hn),
        List.getElem?_eq_getElem (show j-C.gates.length < extra.length from hlen),Option.getD_some]
      exact onlyOr _ (List.getElem_mem hlen)
    have ea := ha.2
    rw [hop] at ea
    contradiction
  have sameCount : ReadTwo.nAnd D = ReadTwo.nAnd C := by
    unfold ReadTwo.nAnd
    rw [shape,List.filter_append,List.length_append]
    apply Nat.add_eq_left.mpr
    apply List.length_eq_zero_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro g hg
    simp [onlyOr g hg]
  have cone {j k : ℕ} (hk : k < C.size) (h : EdgeOwnership.InCone 11 C j k) :
      EdgeOwnership.InCone 11 D j k := by
    let step := EdgeOwnership.coneStep 11
    have ext (gs : List Gate) (v : List (List ℕ)) : ∃ z, gs.foldl step v=v++z := by
      induction gs generalizing v with
      | nil => exact ⟨[],by simp⟩
      | cons g gs ih =>
        obtain ⟨z,hz⟩ := ih (step v g)
        rw [List.foldl_cons,hz]
        dsimp only [step]
        delta EdgeOwnership.coneStep
        rw [List.append_assoc]
        exact ⟨_,rfl⟩
    have len (gs : List Gate) (v : List (List ℕ)) : (gs.foldl step v).length=v.length+gs.length := by
      induction gs generalizing v with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons,ih]
        change (v ++ [_]).length + gs.length = _
        simp
        omega
    let v := C.gates.foldl step []
    obtain ⟨z,hz⟩ := ext extra v
    have hk' : k<v.length := by simpa [v,len] using (show k < C.gates.length from hk)
    change j ∈ (D.gates.foldl step []).getD k []
    rw [shape,List.foldl_append]
    change j ∈ (extra.foldl step v).getD k []
    change j ∈ v.getD k [] at h
    simpa only [hz,List.getD_eq_getElem?_getD,List.getElem?_append_left hk'] using h
  let newHit (r : ℕ) := (T++L).any fun e => BlindGate.wireValue D 11 (row r) e.1 && BlindGate.wireValue D 11 (row r) e.2
  have hit (r : ℕ) : newHit r = (old r || star r) := by
    have eqT : (T.any fun e => BlindGate.wireValue D 11 (row r) e.1 && BlindGate.wireValue D 11 (row r) e.2) = old r := by
      apply Bool.eq_iff_iff.mpr
      simp only [old,List.any_eq_true]
      apply exists_congr
      intro e
      apply and_congr_right
      intro hm
      rw [still (valid e hm).1,still (valid e hm).2.1]
    simp only [newHit,List.any_append,eqT,computes]
    rfl
  have misses : (P.filter fun r => !(newHit r)) = R.filter fun r => !(star r) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r _
    simp [hit,Bool.and_comm]
  have starsum : (groups.map fun g => g.2.length+1).sum = (groups.map fun g => g.2.length).sum + groups.length := by
    induction groups with
    | nil => simp
    | cons g gs ih => simp; omega
  have inputs : ∀ i : Fin 11, (∃ r ∈ P, row r i = true) ∧ ∃ r ∈ N, row r i = true := by decide +kernel
  refine ⟨D,T++L,modelD,?_,?_,by rwa [sameCount],?_,?_,?_,?_⟩
  · intro h
    exact nonempty (List.append_eq_nil_iff.mp h).1
  · change D.size+2*((T++L).length+(P.filter fun r => !(newHit r)).length) ≤ 22
    rw [List.length_append,misses,count]
    rw [starsum] at price
    omega
  · intro e he
    rcases List.mem_append.mp he with h | h
    · obtain ⟨a,b,c⟩ := valid e h
      exact ⟨by omega,by omega,c⟩
    · obtain ⟨a,b,c⟩ := bounded e h
      exact ⟨a,b,Or.inr c⟩
  · intro j hj
    by_cases h : j < C.size
    · obtain ⟨pos,neg⟩ := dirty j h
      constructor <;> apply List.any_eq_true.mpr
      · obtain ⟨r,m,yes⟩ := List.any_eq_true.mp pos
        exact ⟨r,m,(still (by omega) (row r)).trans yes⟩
      · obtain ⟨r,m,yes⟩ := List.any_eq_true.mp neg
        exact ⟨r,m,(still (by omega) (row r)).trans yes⟩
    · obtain ⟨i,hi⟩ := pure j (by omega) hj
      obtain ⟨⟨p,pm,py⟩,q,qm,qy⟩ := inputs i
      exact ⟨List.any_eq_true.mpr ⟨p,pm,hi (row p) py⟩,List.any_eq_true.mpr ⟨q,qm,hi (row q) qy⟩⟩
  · intro j _ ha
    have oldj := kind ha
    have oldAnd : ReadTwo.isAnd C j := ⟨oldj,by simpa [gateOld j oldj] using ha.2⟩
    obtain ⟨e,he,w,hw,whereUsed⟩ := paths j oldj oldAnd
    refine ⟨e,List.mem_append_left _ he,w,hw,?_⟩
    rcases whereUsed with h | ⟨lo,h⟩
    · exact Or.inl h
    · have wlt : w < 11+C.size := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        obtain ⟨a,b,_⟩ := valid e he
        rcases hw with rfl | rfl <;> assumption
      exact Or.inr ⟨lo,cone (by omega) h⟩
  · intro t ht
    change newHit t = false
    have h1 : old t = false := safe t ht
    have h2 : star t = false := reject t ht
    simp [hit,h1,h2]
