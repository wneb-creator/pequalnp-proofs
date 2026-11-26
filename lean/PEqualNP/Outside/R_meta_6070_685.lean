import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadTwo PEqualNP.ReadK

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_6070_685
    (pointBeforeLine : let I := fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ);
      ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.MetaComplexity.circuitFun 26 C = fpl 13 I →
      let ns := fun a b => lineSingle C 26 (fun i => decide (i=b)) a b;
      ns 0 13 = false → ns 13 0 = false →
      let W := fun S => wval C (indW 26 S);
      let V := W {0,13};
      let G := fun j => gateAt C (j-26);
      let R := fun i j => let g := G j; let a := g.inputs.getD 0 0;
        26 ≤ j ∧ i ∈ g.inputs ∧ (g.op.eval [false,true] = false ∨
          i = (if V a then a else g.inputs.getD 1 0));
      let P := Relation.ReflTransGen R;
      let E := fun s j => 26 ≤ j ∧ P j C.output ∧ isAnd C (j-26) ∧
        ∀ b ∈ (G j).inputs, V b = true ∧ W {s} b = false;
      ∀ u v, E 0 u → E 13 v → W {13} u = true → W {0} v = true →
      (∃ i, i ≠ u ∧ P u i ∧ R i v) → False)
    (lineBeforePoint : let I := fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ);
      ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.MetaComplexity.circuitFun 26 C = fpl 13 I →
      let ns := fun a b => lineSingle C 26 (fun i => decide (i=b)) a b;
      ns 0 13 = false → ns 13 0 = false →
      let W := fun S => wval C (indW 26 S);
      let V := W {0,13};
      let G := fun j => gateAt C (j-26);
      let R := fun i j => let g := G j; let a := g.inputs.getD 0 0;
        26 ≤ j ∧ i ∈ g.inputs ∧ (g.op.eval [false,true] = false ∨
          i = (if V a then a else g.inputs.getD 1 0));
      let P := Relation.ReflTransGen R;
      let E := fun s j => 26 ≤ j ∧ P j C.output ∧ isAnd C (j-26) ∧
        ∀ b ∈ (G j).inputs, V b = true ∧ W {s} b = false;
      ∀ u v, E 0 u → E 13 v → W {13} u = true → W {0} v = true →
      (∃ i, i ≠ v ∧ P v i ∧ R i u) → False)
    (joinCase : let I := fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ);
      ∀ C : Circuit, 63 ≤ C.size → C.size ≤ 64 → IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      PEqualNP.MetaComplexity.circuitFun 26 C = fpl 13 I →
      let ns := fun a b => lineSingle C 26 (fun i => decide (i=b)) a b;
      ns 0 13 = false → ns 13 0 = false →
      let W := fun S => wval C (indW 26 S);
      let V := W {0,13};
      let G := fun j => gateAt C (j-26);
      let R := fun i j => let g := G j; let a := g.inputs.getD 0 0;
        26 ≤ j ∧ i ∈ g.inputs ∧ (g.op.eval [false,true] = false ∨
          i = (if V a then a else g.inputs.getD 1 0));
      let P := Relation.ReflTransGen R;
      let E := fun s j => 26 ≤ j ∧ P j C.output ∧ isAnd C (j-26) ∧
        ∀ b ∈ (G j).inputs, V b = true ∧ W {s} b = false;
      ∀ u v, E 0 u → E 13 v → W {13} u = true → W {0} v = true →
      (∃ i j k, i ≠ j ∧ P u i ∧ P v j ∧
        R i k ∧ R j k ∧ P k C.output ∧ (G k).op.eval [false,true] = false) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧ x9 {(13 : ℕ)} ((26 : ℕ) + x12) = Bool.true ∧ x9 {(0 : ℕ)} ((26 : ℕ) + x13) = Bool.true) → False := by
  classical
  intro C lo hi ao nd correct noPoint noLine
  dsimp only
  rintro ⟨u,v,distinct,hu,hv,su,sv⟩
  let W := fun S => wval C (indW 26 S)
  let V := W {0,13}
  let G := fun j => gateAt C (j-26)
  let R := fun i j => let g := G j; let a := g.inputs.getD 0 0
    26 ≤ j ∧ i ∈ g.inputs ∧ (g.op.eval [false,true] = false ∨
      i = (if V a then a else g.inputs.getD 1 0))
  let P := Relation.ReflTransGen R
  let E := fun s j => 26 ≤ j ∧ P j C.output ∧ isAnd C (j-26) ∧
    ∀ b ∈ (G j).inputs, V b = true ∧ W {s} b = false
  let old := fun i j => ∃ (k : ℕ) (g : Gate) (a b : ℕ),
    C.gates[k]? = some g ∧ j = 26+k ∧ g.inputs = [a,b] ∧
      (g.op = .and ∧ (i = a ∨ i = b) ∨ g.op = .or ∧ i = if W {0,13} a = true then a else b) ∧
      W {0,13} i = true ∧ W {0,13} j = true
  have step {i j : ℕ} (h : old i j) : R i j := by
    obtain ⟨k,g,a,b,hg,rfl,inp,choice,_,_⟩ := h
    have bk := List.getElem?_eq_some_iff.mp hg
    have hg' : gateAt C k = g := by
      change C.gates.getD k _ = g
      rw [List.getD_eq_getElem _ _ bk.choose]
      exact bk.choose_spec
    have sub : 26+k-26=k := by omega
    unfold R
    simp only [G,sub,hg',inp]
    refine ⟨by omega,?_⟩
    rcases choice with ⟨op,read⟩ | ⟨op,read⟩
    · have hEval : g.op.eval [false,true] = false := by rw [op]; rfl
      exact ⟨by simpa only [List.mem_cons,List.not_mem_nil,or_false] using read, Or.inl hEval⟩
    · have picked : i ∈ [a,b] := by
        by_cases h : W {0,13} a = true
        · have eq : i = a := by simpa only [h,ite_true] using read
          simp [eq]
        · have eq : i = b := by simpa only [ite_eq_right h] using read
          simp [eq]
      exact ⟨picked, Or.inr read⟩
  have convert {s j : ℕ}
      (h : Relation.ReflTransGen old (26+j) C.output ∧ isAnd C j ∧
        ∀ b ∈ (gateAt C j).inputs, W {0,13} b = true ∧ W {s} b = false) : E s (26+j) := by
    have sub : 26+j-26=j := by omega
    refine ⟨by omega,Relation.ReflTransGen.mono (r := old) (p := R) (fun _ _ e => step e) _ _ h.1,?_⟩
    simpa only [G,sub] using h.2
  have eu : E 0 (26+u) := convert hu
  have ev : E 13 (26+v) := convert hv
  have incident : ∀ p l : Fin 13, ((p-l).val ∈ ([0,1,3,9] : List ℕ)) ↔
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by decide +kernel
  have newCorrect : PEqualNP.MetaComplexity.circuitFun 26 C =
      fpl 13 (fun p l : Fin 13 => (p-l).val ∈ ([0,1,3,9] : List ℕ)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ decide (∃ p l : Fin 13,
      (p-l).val ∈ ([0,1,3,9] : List ℕ) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) = true
    rw [decide_eq_true_eq]
    simpa only [incident] using correct x
  have endpoint {a b : ℕ} (h : P a b) (ne : a ≠ b) :
      ∃ z, P a z ∧ R z b := by
    cases h with
    | refl => exact (ne rfl).elim
    | tail before last => exact ⟨_,before,last⟩
  have distinctWires : 26+u ≠ 26+v := by omega
  have noDirect {k i j : ℕ} (off : ∀ b ∈ (G j).inputs, W {k} b = false)
      (on : W {k} i = true) : ¬ R i j := by
    intro r
    have contradiction := off _ r.2.1
    rw [on] at contradiction
    cases contradiction
  have uvDirect : ¬ R (26+u) (26+v) :=
    noDirect (fun b hb => (ev.2.2.2 b hb).2) su
  have vuDirect : ¬ R (26+v) (26+u) :=
    noDirect (fun b hb => (eu.2.2.2 b hb).2) sv
  by_cases uv : P (26+u) (26+v)
  · obtain ⟨i,p,r⟩ := endpoint uv distinctWires
    have ne : i ≠ 26+u := fun iEq => uvDirect (iEq ▸ r)
    exact pointBeforeLine C lo hi ao nd newCorrect noPoint noLine (26+u) (26+v) eu ev su sv ⟨i,ne,p,r⟩
  by_cases vu : P (26+v) (26+u)
  · obtain ⟨i,p,r⟩ := endpoint vu distinctWires.symm
    have ne : i ≠ 26+v := fun iEq => vuDirect (iEq ▸ r)
    exact lineBeforePoint C lo hi ao nd newCorrect noPoint noLine (26+u) (26+v) eu ev su sv ⟨i,ne,p,r⟩
  have join {z : ℕ} (ap : P (26+u) z) (bp : P (26+v) z) :
      ∃ i j k, i ≠ j ∧ P (26+u) i ∧ P (26+v) j ∧ R i k ∧ R j k ∧ P k z := by
    induction ap with
    | refl => exact (vu bp).elim
    | @tail t z ap last ih =>
      have zNe : 26+v ≠ z := fun h => uv (h ▸ ap.tail last)
      obtain ⟨q,bq,other⟩ := endpoint bp zNe
      by_cases same : t = q
      · subst q
        obtain ⟨i,j,k,ne,pa,pb,ra,rb,rest⟩ := ih bq
        exact ⟨i,j,k,ne,pa,pb,ra,rb,rest.tail last⟩
      · exact ⟨t,q,z,same,ap,bq,last,other,.refl⟩
  obtain ⟨i,j,k,ne,pa,pb,ra,rb,rest⟩ := join eu.2.1 ev.2.1
  have op : (G k).op.eval [false,true] = false := by
    rcases ra.2.2 with yes | a
    · exact yes
    rcases rb.2.2 with yes | b
    · exact yes
    exact (ne (a.trans b.symm)).elim
  exact joinCase C lo hi ao nd newCorrect noPoint noLine (26+u) (26+v) eu ev su sv
    ⟨i,j,k,ne,pa,pb,ra,rb,rest,op⟩
