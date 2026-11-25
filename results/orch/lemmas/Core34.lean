import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.Core34_check :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let S : Finset (Fin 13) := {0, 1, 2, 3, 4, 9, 10}
      let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))
      ∃ B : Circuit, Monotone2 B ∧ B.output < 20 + B.size ∧ B.size ≤ 34 ∧
        (∀ p w : Fin 13, p ∈ S → p - w ∈ D →
          B.eval (inp.map (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) ∧
        (∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t dual,
          B.eval (inp.map (row z m t dual)) = false) := by
  intro D S reps row inp
  let B : Circuit := ⟨[⟨.or, [7, 11]⟩,
      ⟨.or, [20, 17]⟩,
      ⟨.or, [21, 19]⟩,
      ⟨.and, [0, 22]⟩,
      ⟨.or, [7, 8]⟩,
      ⟨.or, [24, 12]⟩,
      ⟨.or, [25, 18]⟩,
      ⟨.and, [1, 26]⟩,
      ⟨.or, [8, 9]⟩,
      ⟨.or, [28, 13]⟩,
      ⟨.or, [29, 19]⟩,
      ⟨.and, [2, 30]⟩,
      ⟨.or, [7, 9]⟩,
      ⟨.or, [32, 10]⟩,
      ⟨.or, [33, 14]⟩,
      ⟨.and, [3, 34]⟩,
      ⟨.or, [8, 10]⟩,
      ⟨.or, [36, 11]⟩,
      ⟨.or, [37, 15]⟩,
      ⟨.and, [4, 38]⟩,
      ⟨.or, [7, 13]⟩,
      ⟨.or, [40, 15]⟩,
      ⟨.or, [41, 16]⟩,
      ⟨.and, [5, 42]⟩,
      ⟨.or, [8, 14]⟩,
      ⟨.or, [44, 16]⟩,
      ⟨.or, [45, 17]⟩,
      ⟨.and, [6, 46]⟩,
      ⟨.or, [23, 27]⟩,
      ⟨.or, [48, 31]⟩,
      ⟨.or, [49, 35]⟩,
      ⟨.or, [50, 39]⟩,
      ⟨.or, [51, 43]⟩,
      ⟨.or, [52, 47]⟩], 53⟩
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · simp [B, Monotone2]
  · decide
  · decide
  · decide +kernel
  · decide +kernel
