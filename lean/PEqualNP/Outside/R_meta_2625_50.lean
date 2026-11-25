import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2625_50
    (complete :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let outside : Finset (Fin 13) := {5, 6, 7, 8, 11, 12}
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))
      let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ outside, ∃ w : Fin 13,
        p - w ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)
      ∀ B : Circuit, Monotone2 B → B.output < 20 + B.size →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ B.size + 30 ∧
          ∀ x : Fin 26 → Bool, circuitFun 26 C x = (B.eval (inp.map x) || hit x))
    (core :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let S : Finset (Fin 13) := {0, 1, 2, 3, 4, 9, 10}
      let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))
      ∃ B : Circuit, Monotone2 B ∧ B.output < 20 + B.size ∧ B.size ≤ 33 ∧
        (∀ p w : Fin 13, p ∈ S → p - w ∈ D →
          B.eval (inp.map (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) ∧
        (∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t dual,
          B.eval (inp.map (row z m t dual)) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  intro D reps row
  let S : Finset (Fin 13) := {0, 1, 2, 3, 4, 9, 10}
  let outside : Finset (Fin 13) := {5, 6, 7, 8, 11, 12}
  let inp := (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))
  let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ outside, ∃ w : Fin 13,
    p - w ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)
  obtain ⟨B, hm, ho, hs, pos, neg⟩ := core
  obtain ⟨C, hc, hsize, hsem⟩ := complete B hm ho
  refine ⟨C, hc, by omega, ?_, ?_⟩
  · intro p w hp
    rcases hp with ⟨d, hd, heq⟩
    have hdiff : p - w ∈ D := by simpa [heq, add_comm] using hd
    rw [hsem, Bool.or_eq_true]
    by_cases hin : p ∈ S
    · exact Or.inl (pos p w hin hdiff)
    · right
      apply decide_eq_true
      have hout : p ∈ outside := by
        have cover : ∀ p : Fin 13, p ∈ S ∨ p ∈ outside := by decide
        exact (cover p).resolve_left hin
      exact ⟨p, hout, w, hdiff, by simp, by simp⟩
  · intro z hz m hmult t dual
    have safe : ∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t dual,
        hit (row z m t dual) = false := by
      decide +kernel
    change circuitFun 26 C (row z m t dual) = false
    rw [hsem, neg z hz m hmult t dual]
    exact safe z hz m hmult t dual
