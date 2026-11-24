import PEqualNP.Outside.L_meta_1325
import PEqualNP.Outside.L_meta_1395
import PEqualNP.MetaComplexity.L1396

/-- The ladder for every projective plane order with its closed form: every fan-in-two AND/OR/NOT
list with at most s NOT gates computing all line-ORs of a plane of order q >= 2 has at least
q * (q * (q + 1 - 2^s) / 2^(s+1)) gates. Closing file: the checked conditional L-meta-1396 applied
to the outside proof of the general ladder (theorem L_meta_1325, whose statement is that of L-meta-1358) and the outside proof of L-meta-1395. -/
theorem PEqualNP.Outside.L_meta_1397 : ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ gates.length :=
  PEqualNP.MetaComplexity.L1396 PEqualNP.Outside.L_meta_1325 PEqualNP.Outside.L_meta_1395
