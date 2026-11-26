import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_18077 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → x1.gates.head? ≠ Option.none := by
  intro C _ computes head
  cases hg : C.gates with
  | cons g rest => simp [hg] at head
  | nil =>
    have raw (x : Fin 26 → Bool) : C.eval (List.ofFn x) = (List.ofFn x).getD C.output false := by
      simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil]
    have full := (computes (fun _ => true)).2 ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    have bound : C.output < 26 := by
      by_contra! h
      rw [raw, List.getD_eq_default _ _ (by simpa using h)] at full
      contradiction
    let i : Fin 26 := ⟨C.output, bound⟩
    let singleton (x : Fin 26) := decide (x = i)
    have yes : C.eval (List.ofFn singleton) = true := by
      rw [raw, List.getD_eq_getElem _ _ (by simpa using bound), List.getElem_ofFn]
      exact decide_eq_true rfl
    obtain ⟨u, v, _, hu, hv⟩ := (computes singleton).1 yes
    have eq : Fin.castAdd 13 u = Fin.natAdd 13 v :=
      (of_decide_eq_true hu).trans (of_decide_eq_true hv).symm
    have val := congrArg Fin.val eq
    change u.val = 13 + v.val at val
    omega
