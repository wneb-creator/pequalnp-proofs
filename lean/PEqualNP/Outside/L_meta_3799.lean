import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Rebuild the final OR gates after the last AND.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_3799 : 
    have diff : Finset (Fin 13) := {0, 1, 3, 9}
    have correct : Circuit → Prop := fun C =>
      (∀ p l : Fin 13, p - l ∈ diff →
        C.eval ((List.ofFn fun i : Fin 13 => decide (i = p)) ++
          List.ofFn fun i : Fin 13 => decide (i = l)) = true) ∧
      ∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ l : Fin 13, (Q.filter fun i => i - l ∈ diff).card ≤ 2) →
        C.eval ((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ i ∈ Q, i - l ∉ diff)) = false
    have nested : Circuit → Prop := fun C => ∃ i j : ℕ,
      (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → C.size < 64 → nested C →
      (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      2 ≤ PEqualNP.TopForm.andPairs 26 C →
      (∀ j < C.gates.length, (gateAt C j).op = .and → 2 ≤ (PEqualNP.TopForm.readers 26 C j).card) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size := by
  classical
  have assemble (n : ℕ) (P : Circuit) (B : Finset ℕ)
      (hne : B.Nonempty) (valid : ∀ i ∈ B, i < n + P.size)
      (mono : Monotone2 P) (back : ReadsBack n P) :
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = P.size + B.card ∧
        (∃ extra : List Gate, D.gates = P.gates ++ extra) ∧
        ∀ x : List Bool, x.length = n →
          (D.eval x = true ↔ ∃ i ∈ B, (P.wires x).getD i false = true) := by
    classical
    have snocRead {α : Type} (l : List α) (v d : α) (j : ℕ) :
        (l ++ [v]).getD j d = if j = l.length then v else l.getD j d := by
      induction l generalizing j with
      | nil => cases j <;> rfl
      | cons a l ih =>
        cases j with
        | zero => rfl
        | succ j => simpa using ih j
    have wireLength (D : Circuit) (x : List Bool) : (D.wires x).length = x.length + D.size := by
      let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have aux (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [step]
          omega
      exact aux D.gates x
    have build (S : Finset ℕ) :
        S.Nonempty → (∀ i ∈ S, i < n + P.size) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = P.size + S.card ∧
          D.output < n + D.size ∧ (∃ extra : List Gate, D.gates = P.gates ++ extra) ∧
          (∀ x : List Bool, x.length = n → ∀ i < n + P.size,
            (D.wires x).getD i false = (P.wires x).getD i false) ∧
          ∀ x : List Bool, x.length = n →
            (D.eval x = true ↔ ∃ i ∈ S, (P.wires x).getD i false = true) := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S fresh ih =>
        intro _ hv
        have va := hv a (by simp)
        by_cases has : S.Nonempty
        · obtain ⟨D, dm, db, ds, dout, ⟨ext, dext⟩, same, output⟩ :=
            ih has (fun i hi => hv i (Finset.mem_insert_of_mem hi))
          let g : Gate := ⟨.or, [D.output, a]⟩
          let E : Circuit := ⟨D.gates ++ [g], n + D.size⟩
          have growing : P.size ≤ D.size := by simp [Circuit.size, dext]
          have es : E.size = D.size + 1 := by simp [E, Circuit.size]
          have pair (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
          have after (x : List Bool) : E.wires x = D.wires x ++
              [(D.wires x).getD D.output false || (D.wires x).getD a false] := by
            change (D.gates ++ [g]).foldl _ x = _
            rw [List.foldl_append]
            change D.wires x ++ [GateOp.or.eval [(D.wires x).getD D.output false,
              (D.wires x).getD a false]] = _
            rw [pair]
          refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro h hh
            change h ∈ D.gates ++ [g] at hh
            rcases List.mem_append.mp hh with old | new
            · exact dm h old
            · have eq : h = g := by simpa using new
              subst h
              exact ⟨by simp [g], by change 2 ≤ 2; exact le_rfl⟩
          · intro j hj i hi
            change j < (D.gates ++ [g]).length at hj
            change i ∈ ((D.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
            rw [snocRead] at hi
            by_cases last : j = D.gates.length
            · subst j
              rw [ite_eq_left (rfl : D.gates.length = D.gates.length)] at hi
              change i ∈ [D.output, a] at hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              change i < n + D.size
              rcases hi with rfl | rfl <;> omega
            · rw [ite_eq_right last] at hi
              apply db j _ i hi
              simp at hj
              omega
          · rw [es, Finset.card_insert_of_notMem fresh]
            omega
          · change n + D.size < n + E.size
            omega
          · exact ⟨ext ++ [g], by change D.gates ++ [g] = _; rw [dext, List.append_assoc]⟩
          · intro x hx i vi
            have len : (D.wires x).length = n + D.size := (wireLength D x).trans (by rw [hx])
            rw [after, snocRead, ite_eq_right (by omega)]
            exact same x hx i vi
          · intro x hx
            have len : (D.wires x).length = n + D.size := (wireLength D x).trans (by rw [hx])
            change (E.wires x).getD (n + D.size) false = true ↔ _
            rw [after, snocRead, ite_eq_left len.symm, same x hx a va]
            change (D.eval x || (P.wires x).getD a false) = true ↔ _
            rw [Bool.or_eq_true, output x hx]
            constructor
            · rintro (⟨i, hi, value⟩ | value)
              · exact ⟨i, Finset.mem_insert_of_mem hi, value⟩
              · exact ⟨a, by simp, value⟩
            · rintro ⟨i, hi, value⟩
              rcases Finset.mem_insert.mp hi with rfl | kept
              · exact Or.inr value
              · exact Or.inl ⟨i, kept, value⟩
        · have clear : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp has
          subst S
          let D : Circuit := ⟨P.gates, a⟩
          refine ⟨D, mono, back, by simp [D, Circuit.size], va, ⟨[], by simp [D]⟩, ?_, ?_⟩
          · exact fun _ _ _ _ => rfl
          · intro x hx
            change (P.wires x).getD a false = true ↔ _
            simp
    obtain ⟨D, dm, db, ds, _, ext, _, output⟩ := build B hne valid
    exact ⟨D, dm, db, ds, ext, output⟩
  have collapse (n : ℕ) (C : Circuit) (p a : ℕ)
      (hp : p ≤ C.gates.length) (ha : a < p)
      (tail : ∀ j, p ≤ j → j < C.gates.length →
        ∃ u v : ℕ, (gateAt C j).op = .or ∧ (gateAt C j).inputs = [u,v] ∧ u < n+j ∧ v < n+j)
      (two : 2 ≤ (PEqualNP.TopForm.readers n C a).card)
      (located : ∀ j ∈ PEqualNP.TopForm.readers n C a, p ≤ j)
      (out : C.output < n + C.gates.length) :
      ∃ B : Finset ℕ, B.Nonempty ∧ (∀ i ∈ B, i < n + p) ∧ B.card ≤ C.gates.length - p ∧
        ∀ x : List Bool, x.length = n →
          (C.eval x = true ↔ ∃ i ∈ B, ((Circuit.mk (C.gates.take p) 0).wires x).getD i false = true) := by
    classical
    let b := n + a
    let R := PEqualNP.TopForm.readers n C a
    let spare (j : ℕ) := ((Finset.Ico p j).filter fun i => i ∉ R).card
    let pop (w u v : ℕ) (S : Finset ℕ) : Finset ℕ :=
      if w ∈ S then (S.erase w) ∪ {u,v} else S
    let val (l : List Bool) (S : Finset ℕ) := ∃ i ∈ S, l.getD i false = true
    have snoc (l : List Bool) (d : Bool) (i : ℕ) :
        (l ++ [d]).getD i false = if i = l.length then d else l.getD i false := by
      induction l generalizing i with
      | nil => cases i <;> rfl
      | cons x l ih =>
        cases i with
        | zero => rfl
        | succ i => simpa using ih i
    have popVal (l : List Bool) (w u v : ℕ) (S : Finset ℕ) (lw : l.length = w) :
        val (l ++ [l.getD u false || l.getD v false]) S ↔ val l (pop w u v S) := by
      by_cases hit : w ∈ S
      · have src (i : ℕ) (hi : i ∈ ({u,v} : Finset ℕ)) (on : l.getD i false = true) :
            (l.getD u false || l.getD v false) = true := by
          apply Bool.or_eq_true_iff.mpr
          rcases (show i = u ∨ i = v by simpa using hi) with eq | eq
          · exact Or.inl (eq ▸ on)
          · exact Or.inr (eq ▸ on)
        constructor
        · rintro ⟨i,hi,on⟩
          rw [snoc, lw] at on
          by_cases eq : i = w
          · rw [ite_eq_left eq] at on
            rcases Bool.or_eq_true_iff.mp on with left | right
            · exact ⟨u, by simp [pop,hit], left⟩
            · exact ⟨v, by simp [pop,hit], right⟩
          · exact ⟨i, by simp [pop,hit,hi,eq], by simpa [eq] using on⟩
        · rintro ⟨i,hi,on⟩
          rw [show pop w u v S = (S.erase w) ∪ {u,v} by simp [pop,hit]] at hi
          rcases Finset.mem_union.mp hi with old | fresh
          · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp old
            exact ⟨i,mem, by simpa only [snoc,lw,ite_eq_right ne] using on⟩
          · refine ⟨w,hit,?_⟩
            rw [snoc,lw,ite_eq_left (show w = w from rfl)]
            exact src i fresh on
      · have unchanged : pop w u v S = S := by simp [pop,hit]
        rw [unchanged]
        constructor
        · rintro ⟨i,hi,on⟩
          have ne : i ≠ w := fun eq => hit (eq ▸ hi)
          exact ⟨i,hi,by simpa only [snoc,lw,ite_eq_right ne] using on⟩
        · rintro ⟨i,hi,on⟩
          have ne : i ≠ w := fun eq => hit (eq ▸ hi)
          exact ⟨i,hi,by simpa only [snoc,lw,ite_eq_right ne] using on⟩
    have popCard (w u v : ℕ) (S : Finset ℕ) (wb : w ≠ b) :
        ((pop w u v S).erase b).card ≤ (S.erase b).card +
          (if b ∈ ({u,v} : Finset ℕ) then 0 else 1) := by
      by_cases hit : w ∈ S
      · let T := (S.erase b).erase w
        let parents : Finset ℕ := {u,v}
        have old : T.card + 1 = (S.erase b).card :=
          Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨wb,hit⟩)
        have splitSet : (pop w u v S).erase b = T ∪ parents.erase b := by
          ext i
          simp only [pop,ite_eq_left hit,T,parents,Finset.mem_erase,Finset.mem_union]
          tauto
        have lim := Finset.card_union_le T (parents.erase b)
        rw [splitSet]
        have pairLim : parents.card ≤ 2 := by
          exact le_trans (Finset.card_insert_le u {v}) (by simp)
        change _ ≤ _ + (if b ∈ parents then 0 else 1)
        by_cases pr : b ∈ parents
        · have cnt := Finset.card_erase_add_one pr
          rw [ite_eq_left pr]
          omega
        · have cnt := Finset.card_le_card (Finset.erase_subset b parents)
          rw [ite_eq_right pr]
          omega
      · simp [pop,hit]
    have spareNext (j : ℕ) (pj : p ≤ j) :
        spare (j+1) = spare j + (if j ∈ R then 0 else 1) := by
      have interval : Finset.Ico p (j+1) = insert j (Finset.Ico p j) := by
        ext i
        simp only [Finset.mem_Ico,Finset.mem_insert]
        omega
      by_cases hj : j ∈ R <;> simp [spare,interval,Finset.filter_insert,hj]
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let wires := fun (j : ℕ) (x : List Bool) => (C.gates.take j).foldl step x
    have foldLen (gs : List Gate) (x : List Bool) :
        (gs.foldl step x).length = x.length + gs.length := by
      induction gs generalizing x with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]
        omega
    have atLen (j : ℕ) (jc : j ≤ C.gates.length) (x : List Bool) (xn : x.length = n) :
        (wires j x).length = n+j := by simp [wires,foldLen,xn,Nat.min_eq_left jc]
    have stepWires (j : ℕ) (jc : j < C.gates.length) (x : List Bool) :
        wires (j+1) x = step (wires j x) (gateAt C j) := by
      have takeEq : C.gates.take (j+1) = C.gates.take j ++ [gateAt C j] := by
        have read : gateAt C j = C.gates[j] := by
          simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem jc,Option.getD_some]
        rw [List.take_succ_eq_append_getElem jc, read]
      simp only [wires,takeEq,List.foldl_append,List.foldl_cons,List.foldl_nil]
    have expand (j : ℕ) (pj : p ≤ j) : j ≤ C.gates.length →
        ∀ S : Finset ℕ, S.Nonempty → (∀ i ∈ S, i < n+j) →
          ∃ B : Finset ℕ, B.Nonempty ∧ (∀ i ∈ B, i < n+p) ∧
            (B.erase b).card ≤ (S.erase b).card + spare j ∧
            ∀ x : List Bool, x.length = n → (val (wires j x) S ↔ val (wires p x) B) := by
      induction j, pj using Nat.le_induction with
      | base =>
        intro _ S ne vr
        exact ⟨S,ne,vr,by simp [spare],fun _ _ => Iff.rfl⟩
      | succ j pj ih =>
        intro jc S ne vr
        obtain ⟨u,v,op,ins,hu,hv⟩ := tail j pj (by omega)
        let w := n+j
        let S' := pop w u v S
        have ne' : S'.Nonempty := by
          by_cases hit : w ∈ S
          · exact ⟨u,by simp [S',pop,hit]⟩
          · simpa [S',pop,hit] using ne
        have valid' : ∀ i ∈ S', i < n+j := by
          intro i mem
          by_cases hit : w ∈ S
          · change i ∈ pop w u v S at mem
            simp only [pop,ite_eq_left hit,Finset.mem_union,Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton] at mem
            rcases mem with ⟨h,old⟩ | rfl | rfl
            · have hle := vr i old
              change i ≠ n+j at h
              omega
            · exact hu
            · exact hv
          · have old : i ∈ S := by simpa [S',pop,hit] using mem
            have hle := vr i old
            have h : i ≠ w := fun e => hit (e ▸ old)
            change i ≠ n+j at h
            omega
        have isReader : j ∈ R ↔ b ∈ ({u,v} : Finset ℕ) := by
          simp [R,PEqualNP.TopForm.readers,ins,b,show j < C.gates.length by omega]
        have card := popCard w u v S (by dsimp [w,b]; omega)
        simp only [← isReader] at card
        obtain ⟨B,nb,goodB,bound,sem⟩ := ih (by omega) S' ne' valid'
        refine ⟨B,nb,goodB,?_,?_⟩
        · change (B.erase b).card ≤ ((pop w u v S).erase b).card + spare j at bound
          rw [spareNext j pj]
          omega
        · intro x xn
          apply Iff.trans _ (sem x xn)
          rw [stepWires j (by omega)]
          have eq : step (wires j x) (gateAt C j) = wires j x ++
              [(wires j x).getD u false || (wires j x).getD v false] := by
            simp only [step, op, ins, List.map_cons, List.map_nil]
            cases (wires j x).getD u false <;> cases (wires j x).getD v false <;> rfl
          rw [eq]
          exact popVal (wires j x) w u v S (atLen j (by omega) x xn)
    obtain ⟨B,ne,valid,card,sem⟩ := expand C.gates.length hp (le_refl _)
      {C.output} (by simp) (by simpa using out)
    have rr : R ⊆ Finset.Ico p C.gates.length := by
      intro j hj
      have lim : j < C.gates.length := (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      exact Finset.mem_Ico.mpr ⟨located j hj,lim⟩
    have number : spare C.gates.length = C.gates.length - p - R.card := by
      have se : ((Finset.Ico p C.gates.length).filter fun i => i ∉ R) = Finset.Ico p C.gates.length \ R := by
        ext i
        simp
      simp [spare,se,Finset.card_sdiff_of_subset rr,Nat.card_Ico]
    have singletonBound : (({C.output} : Finset ℕ).erase b).card ≤ 1 :=
      le_trans (Finset.card_le_card (Finset.erase_subset _ _)) (by simp)
    have lastBound : B.card ≤ (B.erase b).card + 1 := by
      by_cases hb : b ∈ B
      · exact le_of_eq (Finset.card_erase_add_one hb).symm
      · simp [Finset.erase_eq_of_notMem hb]
    change 2 ≤ R.card at two
    have within := Finset.card_le_card rr
    rw [Nat.card_Ico] at within
    rw [number] at card
    refine ⟨B, ne, valid, by omega, ?_⟩
    intro x xn
    have statement := sem x xn
    simpa [val,wires,step,Circuit.eval,Circuit.wires] using statement

  -- This compression preserves the output on every input of the given length.
  have shrink (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
      (someAnd : ∃ j, (gateAt C j).op = .and)
      (binary : ∀ g ∈ C.gates, g.inputs.length = 2)
      (many : ∀ j < C.gates.length, (gateAt C j).op = .and →
        2 ≤ (PEqualNP.TopForm.readers n C j).card) :
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
    have actual (j : ℕ) (andOp : (gateAt C j).op = .and) : j < C.gates.length := by
      by_contra! large
      have past : gateAt C j = ⟨.or, []⟩ := by
        simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none large,Option.getD_none]
      rw [past] at andOp
      cases andOp
    let ands := (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and
    obtain ⟨w, hw⟩ := someAnd
    have nonempty : ands.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (actual w hw),hw⟩⟩
    let a := ands.max' nonempty
    have aMem : a ∈ ands := Finset.max'_mem _ _
    obtain ⟨ar, ha⟩ := Finset.mem_filter.mp aMem
    have realA : a < C.gates.length := Finset.mem_range.mp ar
    let p := a+1
    have hp : p ≤ C.gates.length := realA
    have ap : a < p := Nat.lt_succ_self _
    have belongs (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
      simpa only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
        using List.getElem_mem hj
    have tail (j : ℕ) (pj : p ≤ j) (jc : j < C.gates.length) :
        ∃ u v : ℕ, (gateAt C j).op = .or ∧ (gateAt C j).inputs = [u,v] ∧ u < n+j ∧ v < n+j := by
      have ok := (mono _ (belongs j jc)).1
      change (gateAt C j).op = .and ∨ (gateAt C j).op = .or at ok
      have isOr : (gateAt C j).op = .or := by
        apply ok.resolve_left
        intro andOp
        have mem : j ∈ ands := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jc,andOp⟩
        have upper : j ≤ a := Finset.le_max' ands j mem
        omega
      have parse (l : List ℕ) (len : l.length = 2) : ∃ u v, l = [u,v] := by
        cases l with
        | nil => simp at len
        | cons u l =>
          cases l with
          | nil => simp at len
          | cons v rest =>
            cases rest with
            | nil => exact ⟨u,v,rfl⟩
            | cons t rest => simp at len
      obtain ⟨u,v,ins⟩ := parse _ (binary _ (belongs j jc))
      exact ⟨u,v,isOr,ins,back j jc u (by simp [ins]),back j jc v (by simp [ins])⟩
    have located (j : ℕ) (r : j ∈ PEqualNP.TopForm.readers n C a) : p ≤ j := by
      obtain ⟨jr, uses⟩ := Finset.mem_filter.mp r
      have order := back j (Finset.mem_range.mp jr) (n+a) uses
      change a + 1 ≤ j
      omega
    by_cases out : C.output < n + C.gates.length
    · obtain ⟨B,hasB,vB,cB,front⟩ := collapse n C p a hp ap tail (many a realA ha) located out
      let P : Circuit := ⟨C.gates.take p,0⟩
      have pSize : P.size = p := List.length_take_of_le hp
      have monP : Monotone2 P := fun g hg => mono g (List.mem_of_mem_take hg)
      have backP : ReadsBack n P := by
        intro j hj i hi
        have jp : j < p := by simpa [P,List.length_take_of_le hp] using hj
        have same : gateAt P j = gateAt C j := by
          simp only [gateAt,P,List.getD_eq_getElem?_getD,List.getElem?_take_of_lt jp]
        rw [same] at hi
        exact back j (by omega) i hi
      have within (i : ℕ) (hi : i ∈ B) : i < n + P.size := pSize ▸ vB i hi
      obtain ⟨D, md, bd, dSize, _, eval⟩ := assemble n P B hasB within monP backP
      refine ⟨D,md,bd,?_,?_⟩
      · change D.size < C.gates.length
        omega
      · intro x hx
        have iff : D.eval x = true ↔ C.eval x = true :=
          (eval x hx).trans (front x hx).symm
        cases d : D.eval x <;> cases c : C.eval x <;> simp [d,c] at iff ⊢
    · let D : Circuit := ⟨[], n⟩
      have size0 : D.size = 0 := rfl
      have len (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
        let st := fun (l : List Bool) (g : Gate) => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]
        have aux (gs : List Gate) (l : List Bool) : (gs.foldl st l).length = l.length + gs.length := by
          induction gs generalizing l with
          | nil => simp
          | cons g gs ih =>
            simp only [List.foldl_cons,ih,st,List.length_append,List.length_cons,List.length_nil]
            omega
        exact aux _ _
      refine ⟨D,?_,?_,?_,?_⟩
      · intro g hg
        cases hg
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
      · change 0 < C.gates.length
        omega
      · intro x hx
        have hc : (C.wires x).length ≤ C.output := by rw [len,hx]; omega
        have h0 : x.length ≤ n := le_of_eq hx
        change x.getD n false = (C.wires x).getD C.output false
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none h0,List.getElem?_eq_none hc]
  intro _diff _correct _nestedPred C mono back fits _size nested shape _pairs many
  obtain ⟨i, j, hi, _, _⟩ := nested
  obtain ⟨D,good,order,small,same⟩ :=
    shrink 26 C mono back ⟨i,hi⟩ (fun g hg => (shape g hg).1) many
  refine ⟨D,good,order,?_,small⟩
  obtain ⟨incident, quadrangles⟩ := fits
  constructor
  · intro p l h
    rw [same _ (by simp)]
    exact incident p l h
  · intro Q card arc
    rw [same _ (by simp)]
    exact quadrangles Q card arc
