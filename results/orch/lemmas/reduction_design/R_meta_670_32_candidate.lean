import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_670_32
    (normalize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (and_bound : ∀ C : Circuit, Monotone2 C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      5 ≤ PEqualNP.ReadTwo.nAnd C)
    (or_bound : ∀ C : Circuit, Monotone2 C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      11 ≤ PEqualNP.ReadTwo.nOr C) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C, hC, hsize, hfun⟩
  obtain ⟨D, hD, hle, heq⟩ := normalize C hC (funext hfun)
  have ha := and_bound D hD heq
  have ho := or_bound D hD heq
  have hcount : PEqualNP.ReadTwo.nAnd D + PEqualNP.ReadTwo.nOr D ≤ D.size := by
    unfold PEqualNP.ReadTwo.nAnd PEqualNP.ReadTwo.nOr Circuit.size
    generalize D.gates = gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      by_cases ha : g.op = GateOp.and
      · have ho : g.op ≠ GateOp.or := by simp [ha]
        simp [ha, ho]
        omega
      · by_cases ho : g.op = GateOp.or
        · simp [ha, ho]
          omega
        · simp [ha, ho]
          omega
  omega
