import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadTwo
open PEqualNP.ReadK PEqualNP.MetaComplexity.NestedCover

-- Check positive edges at their two endpoints. On the negative side use
-- every point subset with all lines avoiding that subset.
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_6064_481
    (size63 : ∀ C : Circuit, C.size = 63 → IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        let D : Finset (Fin 13) := {0, 1, 3, 9}
        let input := fun (x : Fin 26 → Bool) => C.eval (List.ofFn x)
        let v := fun S w => wval C (indW 26 S) w
        let step := fun a b => ∃ j g x y, C.gates[j]? = some g ∧ b = 26+j ∧ g.inputs = [x,y] ∧
          (g.op = GateOp.and ∧ (a = x ∨ a = y) ∨
           g.op = GateOp.or ∧ a = if v {0,13} x = true then x else y) ∧ v {0,13} a = true ∧ v {0,13} b = true
        (∀ p l : Fin 13, p-l ∈ D →
          input (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        (∀ Q : Finset (Fin 13), input (fun i =>
          if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ Q)
          else decide (∀ p ∈ Q, p - Fin.ofNat 13 (i.val - 13) ∉ D)) = false) →
        lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
        lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
        (∃ j, Relation.ReflTransGen step (26+j) C.output ∧ isAnd C j ∧
          ∀ w ∈ (gateAt C j).inputs, v {0,13} w = true ∧ v {0} w = false ∧ v {13} w = false) → False)
    (size64 : ∀ C : Circuit, C.size = 64 → IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        let D : Finset (Fin 13) := {0, 1, 3, 9}
        let input := fun (x : Fin 26 → Bool) => C.eval (List.ofFn x)
        let v := fun S w => wval C (indW 26 S) w
        let step := fun a b => ∃ j g x y, C.gates[j]? = some g ∧ b = 26+j ∧ g.inputs = [x,y] ∧
          (g.op = GateOp.and ∧ (a = x ∨ a = y) ∨
           g.op = GateOp.or ∧ a = if v {0,13} x = true then x else y) ∧ v {0,13} a = true ∧ v {0,13} b = true
        (∀ p l : Fin 13, p-l ∈ D →
          input (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        (∀ Q : Finset (Fin 13), input (fun i =>
          if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ Q)
          else decide (∀ p ∈ Q, p - Fin.ofNat 13 (i.val - 13) ∉ D)) = false) →
        lineSingle C 26 (fun i => decide (i = 13)) 0 13 = false →
        lineSingle C 26 (fun i => decide (i = 0)) 13 0 = false →
        (∃ j, Relation.ReflTransGen step (26+j) C.output ∧ isAnd C j ∧
          ∀ w ∈ (gateAt C j).inputs, v {0,13} w = true ∧ v {0} w = false ∧ v {13} w = false) → False) :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ), x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧ x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;                 have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) => Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs, x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;                 (∃ (x12 : ℕ), x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x12) → False) := by
  dsimp only
  intro C hlo hhi ao nodup correct singleL singleP witness
  let D : Finset (Fin 13) := {0,1,3,9}
  have edge (p l : Fin 13) : p-l ∈ D ↔ p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9 := by
    revert p l
    decide +kernel
  have pos : ∀ p l : Fin 13, p-l ∈ D →
      C.eval (List.ofFn (fun (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true := by
    intro p l e
    apply (correct _).mpr
    refine ⟨p,l,(edge p l).mp e, ?_, ?_⟩
    · exact decide_eq_true (Or.inl rfl)
    · exact decide_eq_true (Or.inr rfl)
  have neg : ∀ Q : Finset (Fin 13), C.eval (List.ofFn (fun (i : Fin 26) =>
      if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ Q)
      else decide (∀ p ∈ Q, p - Fin.ofNat 13 (i.val - 13) ∉ D))) = false := by
    intro Q
    apply Bool.eq_false_iff.mpr
    intro y
    obtain ⟨p,l,e,hp,hl⟩ := (correct _).mp y
    have pq : p ∈ Q := by
      change (if p.val < 13 then decide (Fin.ofNat 13 p.val ∈ Q) else _) = true at hp
      have he : Fin.ofNat 13 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
      rw [ite_eq_left p.isLt, he] at hp
      exact of_decide_eq_true hp
    have ln : ∀ a ∈ Q, a-l ∉ D := by
      change (if 13 + l.val < 13 then _ else decide (∀ a ∈ Q, a - Fin.ofNat 13 (13+l.val-13) ∉ D)) = true at hl
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
        show Fin.ofNat 13 l.val = l from Fin.ext (Nat.mod_eq_of_lt l.isLt)] at hl
      exact of_decide_eq_true hl
    exact ln p pq ((edge p l).mpr e)
  obtain ⟨j,⟨hpath,hAnd,h0⟩,⟨_,_,h13⟩⟩ := witness
  have count : C.size = 63 ∨ C.size = 64 := by omega
  rcases count with h | h
  · exact size63 C h ao nodup pos neg singleL singleP
      ⟨j,hpath,hAnd,fun w hw => ⟨(h0 w hw).1,(h0 w hw).2,(h13 w hw).2⟩⟩
  · exact size64 C h ao nodup pos neg singleL singleP
      ⟨j,hpath,hAnd,fun w hw => ⟨(h0 w hw).1,(h0 w hw).2,(h13 w hw).2⟩⟩
