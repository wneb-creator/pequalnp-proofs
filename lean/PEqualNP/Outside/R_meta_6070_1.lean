import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_6070_1
    (h63 : ∀ (x1 : Circuit),
      x1.size = 63 → 26 ≤ x1.output ∧ x1.output < 26 + x1.size →
      IsAO2 26 x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      (∀ x6 : Fin 26 → Bool, x1.eval (List.ofFn x6) = true ↔
        ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧
          x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      lineSingle x1 26 (fun x7 : ℕ => decide (x7 = 13)) 0 13 = false →
      lineSingle x1 26 (fun x8 : ℕ => decide (x8 = 0)) 13 0 = false →
      have x9 : Finset ℕ → ℕ → Bool := fun x9 => wval x1 (indW 26 x9);
      have x10 : ℕ → ℕ → Prop := fun x10 x11 =>
        ∃ (x12 : ℕ) (x13 : Gate) (x14 x15 : ℕ),
          x1.gates[x12]? = some x13 ∧ x11 = 26 + x12 ∧ x13.inputs = [x14, x15] ∧
          (x13.op = GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨
           x13.op = GateOp.or ∧ x10 = if x9 {0, 13} x14 = true then x14 else x15) ∧
          x9 {0, 13} x10 = true ∧ x9 {0, 13} x11 = true;
      have x11 : ℕ → ℕ → Prop := fun x11 x12 =>
        Relation.ReflTransGen x10 (26 + x12) x1.output ∧ isAnd x1 x12 ∧
        ∀ x13 ∈ (gateAt x1 x12).inputs, x9 {0, 13} x13 = true ∧ x9 {x11} x13 = false;
      (∃ x12 x13 : ℕ, x12 ≠ x13 ∧ x11 0 x12 ∧ x11 13 x13 ∧
        x9 {13} (26 + x12) = true ∧ x9 {0} (26 + x13) = true) → False)
    (h64 : ∀ (x1 : Circuit),
      x1.size = 64 → 26 ≤ x1.output ∧ x1.output < 26 + x1.size →
      IsAO2 26 x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      (∀ x6 : Fin 26 → Bool, x1.eval (List.ofFn x6) = true ↔
        ∃ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) ∧
          x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) →
      lineSingle x1 26 (fun x7 : ℕ => decide (x7 = 13)) 0 13 = false →
      lineSingle x1 26 (fun x8 : ℕ => decide (x8 = 0)) 13 0 = false →
      have x9 : Finset ℕ → ℕ → Bool := fun x9 => wval x1 (indW 26 x9);
      have x10 : ℕ → ℕ → Prop := fun x10 x11 =>
        ∃ (x12 : ℕ) (x13 : Gate) (x14 x15 : ℕ),
          x1.gates[x12]? = some x13 ∧ x11 = 26 + x12 ∧ x13.inputs = [x14, x15] ∧
          (x13.op = GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨
           x13.op = GateOp.or ∧ x10 = if x9 {0, 13} x14 = true then x14 else x15) ∧
          x9 {0, 13} x10 = true ∧ x9 {0, 13} x11 = true;
      have x11 : ℕ → ℕ → Prop := fun x11 x12 =>
        Relation.ReflTransGen x10 (26 + x12) x1.output ∧ isAnd x1 x12 ∧
        ∀ x13 ∈ (gateAt x1 x12).inputs, x9 {0, 13} x13 = true ∧ x9 {x11} x13 = false;
      (∃ x12 x13 : ℕ, x12 ≠ x13 ∧ x11 0 x12 ∧ x11 13 x13 ∧
        x9 {13} (26 + x12) = true ∧ x9 {0} (26 + x13) = true) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size → x1.size ≤ (64 : ℕ) →
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
        ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)),
          (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧
          x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →
      PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →
      PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →
      have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);
      have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) =>
        ∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 : ℕ) (x15 : ℕ),
          x1.gates[x12]? = Option.some x13 ∧ x11 = (26 : ℕ) + x12 ∧ x13.inputs = [x14, x15] ∧
          (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10 = x14 ∨ x10 = x15) ∨
           x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x10 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x15) ∧
          x9 {(0 : ℕ), (13 : ℕ)} x10 = Bool.true ∧ x9 {(0 : ℕ), (13 : ℕ)} x11 = Bool.true;
      have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>
        Relation.ReflTransGen x10 ((26 : ℕ) + x12) x1.output ∧ PEqualNP.ReadTwo.isAnd x1 x12 ∧
        ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs,
          x9 {(0 : ℕ), (13 : ℕ)} x13 = Bool.true ∧ x9 {x11} x13 = Bool.false;
      (∃ (x12 : ℕ) (x13 : ℕ), x12 ≠ x13 ∧ x11 (0 : ℕ) x12 ∧ x11 (13 : ℕ) x13 ∧
        x9 {(13 : ℕ)} ((26 : ℕ) + x12) = Bool.true ∧ x9 {(0 : ℕ)} ((26 : ℕ) + x13) = Bool.true) → False := by
  intro C hge hle hAO hnodup hfun hs0 hs13 x9 x10 x11 hex
  have hge26 : 26 ≤ C.output := by
    by_contra! hlt
    let a : Fin 26 → Bool := fun i => decide (i.val = C.output)
    have hfold_lt : ∀ (gs : List Gate) (u : List Bool) (k : ℕ), k < u.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD k false = u.getD k false := by
      intro gs
      induction gs with
      | nil => intro u k _; rfl
      | cons g gs ih =>
        intro u k hk
        simp only [List.foldl_cons]
        rw [ih _ k (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    have hev : C.eval (List.ofFn a) = true := by
      change (C.wires (List.ofFn a)).getD C.output false = true
      dsimp only [Circuit.wires]
      rw [hfold_lt C.gates (List.ofFn a) C.output (by rw [List.length_ofFn]; exact hlt)]
      have hlen : C.output < (List.ofFn a).length := by rw [List.length_ofFn]; exact hlt
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
      simp [a]
    obtain ⟨p, l, _, hp, hl⟩ := (hfun a).mp hev
    have hne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    simp only [a, decide_eq_true_eq] at hp hl
    exact hne (Fin.ext (hp.trans hl.symm))
  have hlt26 : C.output < 26 + C.size := by
    by_contra! hle26
    let a : Fin 26 → Bool := fun i => decide (i.val = 0 ∨ i.val = 13)
    have htrue : C.eval (List.ofFn a) = true := (hfun a).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hfold_len : ∀ (gs : List Gate) (u : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).length = u.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro u; simp
      | cons g gs ih => intro u; simp only [List.foldl_cons]; rw [ih]; simp; omega
    have hdef : C.eval (List.ofFn a) = false := by
      change (C.wires (List.ofFn a)).getD C.output false = false
      dsimp only [Circuit.wires]
      apply List.getD_eq_default
      rw [hfold_len, List.length_ofFn]
      exact hle26
    rw [htrue] at hdef
    exact absurd hdef (by decide)
  have hcases : C.size = 63 ∨ C.size = 64 := by omega
  rcases hcases with h | h
  · exact h63 C h ⟨hge26, hlt26⟩ hAO hnodup hfun hs0 hs13 hex
  · exact h64 C h ⟨hge26, hlt26⟩ hAO hnodup hfun hs0 hs13 hex
