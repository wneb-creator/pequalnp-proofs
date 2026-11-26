import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_7261_314
    (twoWires :
      let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row := fun (side : Bool) (s : Finset (Fin 13)) =>
        let bit := fun i : Fin 13 => decide (i ∈ s)
        let free := fun i : Fin 13 => decide (∀ j ∈ s, ¬ (if side then E j i else E i j))
        if side then Fin.append bit free else Fin.append free bit
      ∃ (D : Circuit) (a b : ℕ), D.size ≤ 63 ∧ IsAO2 26 D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ a ≠ b ∧ a < 26+D.size ∧ b < 26+D.size ∧
        (∀ p l, E p l →
          let x := pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)
          wireValue D 26 x a = true ∧ wireValue D 26 x b = true) ∧
        ∀ side s, s.card ≤ 3 →
          wireValue D 26 (row side s) (if row side s 13 then a else b) = false)
    (appendAnd : ∀ (n : ℕ) (D : Circuit) (a b : ℕ), IsAO2 n D →
      (∀ g ∈ D.gates, g.inputs.Nodup) → a ≠ b → a < n+D.size → b < n+D.size →
      let C : Circuit := ⟨D.gates ++ [⟨.and,[a,b]⟩], n+D.size⟩
      IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        ∀ (x : Fin n → Bool) (w : ℕ), w < n+D.size → wireValue C n x w = wireValue D n x w) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Bool) (x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x7 x8) (if x2 x7 x8 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  obtain ⟨D,a,b,hn,hm,hd,hab,ha,hb,hpos,hneg⟩ := twoWires
  let C : Circuit := ⟨D.gates ++ [⟨.and,[a,b]⟩], 26+D.size⟩
  obtain ⟨hmodel,hinputs,preserve⟩ := appendAnd 26 D a b hm hd hab ha hb
  refine ⟨C,D.size,a,b,?_,hmodel,hinputs,rfl,?_,?_,?_⟩
  · change (D.gates ++ [_]).length ≤ 64
    change D.gates.length ≤ 63 at hn
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · change (D.gates ++ [_])[D.gates.length]? = _
    simp
  · intro p l h
    have hp := hpos p l h
    dsimp only
    rw [preserve _ a ha, preserve _ b hb]
    exact hp
  · intro side s small
    split <;> rename_i h
    · rw [preserve _ a ha]
      simpa only [ite_eq_left h] using hneg side s small
    · rw [preserve _ b hb]
      simpa only [ite_eq_right h] using hneg side s small
