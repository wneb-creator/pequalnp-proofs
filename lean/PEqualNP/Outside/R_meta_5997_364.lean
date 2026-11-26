import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5997_364
    (geometry : let E := fun p l : Fin 13 => p ≠ 0 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)
      ∀ a b : Fin 26, ∃ P L : Equiv.Perm (Fin 13), (∀ p l, E (P p) (L l) ↔ E p l) ∧
        let key := fun i : Fin 26 => if i.val < 13 then (P (Fin.ofNat 13 i.val)).val
          else 13 + (L (Fin.ofNat 13 (i.val-13))).val
        26 * min (key a) (key b) + max (key a) (key b) ∈ ([0,1,13,14,27,28,29,39,40,41,43,351,352,355,378,379] : List ℕ))
    (representatives : ∀ (C : Circuit),
      (∀ (op : GateOp) (a b : ℕ), C.gates[0]? = some ⟨op,[a,b]⟩ →
        26 * min a b + max a b ∈ ([0,1,13,14,27,28,29,39,40,41,43,351,352,355,378,379] : List ℕ)) →
      IsAO2 26 C → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ p ≠ 0 ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) → 59 ≤ C.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  classical
  intro C hc hf
  by_cases empty : C.gates = []
  · apply representatives C _ hc hf
    simp [empty]
  obtain ⟨g,gs,head⟩ := List.exists_cons_of_ne_nil empty
  have mem : g ∈ C.gates := by simp [head]
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hc.2.2 g mem)
  have back (j : ℕ) (hj : j < C.gates.length) (k : ℕ) (hk : k ∈ C.gates[j].inputs) :
      k < 26+j := by
    apply hc.2.1 j hj k
    change k ∈ (C.gates.getD j _).inputs
    simpa [List.getD_eq_getElem?_getD,hj] using hk
  have hb0 {k : ℕ} (hk : k ∈ [a,b]) : k < 26 := by
    have h0 : 0 < C.gates.length := by simp [head]
    have h := back 0 h0 k (by simpa [head,hab] using hk)
    omega
  have ha := hb0 (k := a) (by simp)
  have hb := hb0 (k := b) (by simp)
  obtain ⟨P,L,inc,chosen⟩ := geometry ⟨a,ha⟩ ⟨b,hb⟩
  let t : Fin 26 → Fin 26 := Fin.addCases (motive := fun _ => Fin 26) (fun p => Fin.castAdd 13 (P p))
    (fun l => Fin.natAdd 13 (L l))
  let key := fun i : Fin 26 => if i.val < 13 then (P (Fin.ofNat 13 i.val)).val
    else 13 + (L (Fin.ofNat 13 (i.val-13))).val
  have key_eq (i : Fin 26) : (t i).val = key i := by
    refine Fin.addCases (m := 13) (n := 13) (motive := fun i => (t i).val = key i) ?_ ?_ i
    · intro j
      simp only [t,Fin.addCases_left,Fin.val_castAdd,key,if_pos j.isLt,Fin.ofNat_val_eq_self]
    · intro j
      simp only [t,Fin.addCases_right,Fin.val_natAdd,key]
      simp [show ¬13+j.val < 13 by omega]
  let w := fun i : ℕ => if hi : i < 26 then (t ⟨i,hi⟩).val else i
  let rename := fun h : Gate => (⟨h.op,h.inputs.map w⟩ : Gate)
  let R : Circuit := ⟨C.gates.map rename,w C.output⟩
  have len : R.gates.length = C.gates.length := List.length_map _
  have early (i j : ℕ) (h : i < 26+j) : w i < 26+j := by
    dsimp [w]
    split
    · have := (t ⟨i,by assumption⟩).isLt
      omega
    · exact h
  have hR : IsAO2 26 R := by
    refine ⟨?_,?_,?_⟩
    · intro z hz
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
      exact hc.1 q hq
    · intro j hj k hk
      have hj' : j < C.gates.length := by omega
      have gate : PEqualNP.MetaComplexity.NestedCover.gateAt R j = rename C.gates[j] := by
        change (C.gates.map rename).getD j _ = _
        simp [List.getD_eq_getElem?_getD,hj']
      rw [gate] at hk
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
      exact early i j (back j hj' i hi)
    · intro z hz
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
      exact (List.length_map w).trans (hc.2.2 q hq)
  let step := fun (u : List Bool) (h : Gate) =>
    u ++ [h.op.eval (h.inputs.map fun i => u.getD i false)]
  have old (u : List Bool) (v : Bool) (i : ℕ) (hi : i ≠ u.length) :
      (u ++ [v]).getD i false = u.getD i false := by
    by_cases h : i < u.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have run (hs : List Gate) (u v : List Bool) (hu : 26 ≤ u.length) (hl : v.length = u.length)
      (agree : ∀ i, v.getD (w i) false = u.getD i false) :
      ∀ i, ((hs.map rename).foldl step v).getD (w i) false = (hs.foldl step u).getD i false := by
    induction hs generalizing u v with
    | nil => exact agree
    | cons q hs ih =>
      apply ih (step u q) (step v (rename q)) (by simp [step]; omega) (by simp [step,hl])
      intro i
      by_cases hi : i = u.length
      · have wi : w i = i := by simp [w,show ¬ i < 26 by omega]
        have val : (rename q).op.eval ((rename q).inputs.map (fun j => v.getD j false)) =
            q.op.eval (q.inputs.map (fun j => u.getD j false)) := by
          congr 1
          simp only [rename,List.map_map,Function.comp_def]
          exact List.map_congr_left fun j _ => agree j
        unfold step
        rw [wi,List.getD_append_right _ _ _ _ (by omega : v.length ≤ i),
          List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),hl,hi,Nat.sub_self]
        exact val
      · have wi : w i ≠ v.length := by
          by_cases h : i < 26
          · have := (t ⟨i,h⟩).isLt
            simp only [w,dite_eq_left h]
            omega
          · simpa [w,h,hl] using hi
        exact (old _ _ _ wi).trans ((agree i).trans (old _ _ _ hi).symm)
  have act (x : Fin 26 → Bool) : R.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (t i))) := by
    apply run C.gates (List.ofFn (fun i => x (t i))) (List.ofFn x) (by simp) (by simp)
    intro i
    by_cases h : i < 26
    · simp only [w,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
        dite_eq_left (t ⟨i,h⟩).isLt,dite_eq_left h,Option.getD_some]
    · simp only [w,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
        dite_eq_right h,Option.getD_none]
  have correct : ∀ x : Fin 26 → Bool, R.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ p ≠ 0 ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    rw [act,hf]
    constructor
    · rintro ⟨p,l,e,n,hp,hl⟩
      obtain ⟨nz,edge⟩ := (inc p l).2 ⟨n,e⟩
      exact ⟨P p,L l,edge,nz,by simpa [t] using hp,by simpa only [t,Fin.addCases_right] using hl⟩
    · rintro ⟨p,l,e,n,hp,hl⟩
      let u := P.symm p
      let v := L.symm l
      have pu : P u = p := P.apply_symm_apply _
      have lv : L v = l := L.apply_symm_apply _
      obtain ⟨nz,edge⟩ := (inc u v).1 (by rw [pu,lv]; exact ⟨n,e⟩)
      exact ⟨u,v,edge,nz,by simpa [t,pu] using hp,by simpa only [t,Fin.addCases_right,lv] using hl⟩
  have result := representatives R (by
    intro op i j h
    have eq : (rename g).inputs = [i,j] := congrArg Gate.inputs (by simpa [R,head] using h)
    change g.inputs.map w = [i,j] at eq
    rw [hab] at eq
    obtain ⟨rfl,rfl⟩ : w a = i ∧ w b = j := by simpa using eq
    simp only [w,dite_eq_left ha,dite_eq_left hb,key_eq]
    exact chosen) hR correct
  change 59 ≤ R.gates.length at result
  change 59 ≤ C.gates.length
  rwa [len] at result
