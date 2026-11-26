import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

-- The two searches are separate: trace a unique occurrence through the
-- circuit, and prove that one of the endpoints has such a single-read proof.
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5987_481
    (trace : ∀ (C : Circuit) (p l : ℕ), IsAO2 26 C → p < 26 → l < 26 →
      lineSingle C 26 (fun i => decide (i = l)) p l = true →
      Relation.ReflTransGen (fun a b => ∃ j k g, b = 26+j ∧ C.gates[j]? = some g ∧
        (g.inputs = [a,k] ∨ g.inputs = [k,a]) ∧ (g.op = GateOp.or ∨
          (C.wires (List.ofFn (fun i : Fin 26 => decide (i.val = p)))).getD k false = true))
        l C.output)
    (single : let D : Finset (Fin 13) := {0,1,3,9}
      ∀ C : Circuit, IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.size ≤ 64 →
        let v := fun (x : Fin 26 → Bool) w => (C.wires (List.ofFn x)).getD w false
        (∀ x, v x C.output = true ↔ ∃ p l : Fin 13, p-l ∈ D ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∀ p l : Fin 13, p-l ∈ D → ∃ S ⊆ Finset.range C.size, 56 ≤ S.card ∧
          ∀ j ∈ S, ∀ k < 26+j, ∃ x, x (Fin.castAdd 13 p) = false ∧
            x (Fin.natAdd 13 l) = false ∧ v x k ≠ v x (26+j)) →
        lineSingle C 26 (fun i => decide (i = 13)) 0 13 = true ∨
          lineSingle C 26 (fun i => decide (i = 0)) 13 0 = true) :
  (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       x2.size ≤ (64 : ℕ) →         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →             have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;             x9 (0 : ℕ) ∨ x9 (13 : ℕ)) := by
  dsimp only
  intro C ao nodup size correct signature
  let D : Finset (Fin 13) := {0,1,3,9}
  have edge : ∀ p l : Fin 13, p-l ∈ D ↔ p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9 := by
    decide +kernel
  have hits := single C ao nodup size (by
    intro x
    rw [correct x]
    constructor
    · rintro ⟨p,l,e,hp,hl⟩
      exact ⟨p,l,(edge p l).mpr e,hp,hl⟩
    · rintro ⟨p,l,e,hp,hl⟩
      exact ⟨p,l,(edge p l).mp e,hp,hl⟩)
    (fun p l e => signature p l ((edge p l).mp e))
  rcases hits with hl | hp
  · exact Or.inl (trace C 0 13 ao (by decide) (by decide) hl)
  · exact Or.inr (trace C 13 0 ao (by decide) (by decide) hp)
