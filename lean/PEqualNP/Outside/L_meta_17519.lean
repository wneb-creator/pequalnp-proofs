import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_17519 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → x1.size = (0 : ℕ) → (59 : ℕ) ≤ x1.size) := by
  intro C hout _ hgood hsize
  have hnil : C.gates = [] := List.length_eq_zero_iff.mp hsize
  have ht := (hgood (fun _ => true)).mpr ⟨1, 1, Or.inl rfl, by decide, rfl, rfl⟩
  have hlen : (List.ofFn (fun _ : Fin 26 => true)).length ≤ C.output := by simpa
  have hf : C.eval (List.ofFn (fun _ : Fin 26 => true)) = false := by
    simp only [Circuit.eval, Circuit.wires, hnil, List.foldl_nil, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hlen]
    rfl
  rw [hf] at ht
  contradiction

