import PEqualNP.MetaComplexity.Helpers.Deg2S0

/-- The degree-two count for a circuit only below the incidence function: on an incidence of N
points and N lines with no two points on two common lines, an AND/OR circuit of fan-in two and
line-degree at most 2 that is true only where an incident point and line are both on accepts at
most 48 times its size plus 2 N of the inputs with exactly one point and one incident line on. -/
theorem PEqualNP.MetaComplexity.L963 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true → ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true)).card ≤ 48 * C.size + 2 * N :=
  PEqualNP.MetaComplexity.Deg2.assembly_below
