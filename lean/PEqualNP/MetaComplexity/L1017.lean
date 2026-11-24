import PEqualNP.MetaComplexity.Helpers.NormalForm3d

/-- The normal form at line-degree 3, with sizes. On inputs listed points first, then lines
(line-degree: line input 1, point input 0, AND gate the sum over its inputs with repeats counted,
OR gate the maximum), every circuit `C` of AND and OR gates of fan-in at most two, with `s` gates
and an output of line-degree at most 3, is equal on every input to a circuit `D` of at most
`2 s + 1` gates, itself of line-degree at most 3, whose last gate is the output `OR(u, r)`: `r` is
a wire of line-degree at most 2, and `u` has the value of the OR over `j` of `AND(a_j, b_j)` for
wires `a_j` of line-degree at most 2 and `b_j` of line-degree at most 1, with `j` at most the
number of gates of `D`. -/
theorem PEqualNP.MetaComplexity.L1017 : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 3 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 2 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 3 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 1) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 2 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) :=
  PEqualNP.MetaComplexity.Helpers.NormalForm3.nf3d_main
