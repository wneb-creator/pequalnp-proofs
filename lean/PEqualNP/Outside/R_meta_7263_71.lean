import PEqualNP.Defs

-- Select a coordinate in the original labelling. The ten permutations below
-- move it to the last input while preserving the Petersen edge function.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_7263_71
    (cofactor : let F : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))))
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
        let w := fun x : Fin 10 → Bool => (C.wires (List.ofFn x))
        let A := fun x => (w x).getD a false
        let B := fun x => (w x).getD b false
        let P := fun x => A x && B x
        (∃ x, A x = true ∧ B x = false) → (∃ x, A x = false ∧ B x = true) →
        (∀ x, F x = false ∨ (List.ofFn x).count true ≤ 2 → P x = F x) →
        ∃ (i : Fin 10) (v : Bool) (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D ∧
          D.size ≤ (if v then 10 else 15) ∧
          ∀ x : Fin 10 → Bool, x i = v → D.eval (List.ofFn x) = P x)
    (specialize : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Equiv.Perm (Fin (n+1))) (v : Bool),
        PEqualNP.MetaComplexity.FanInTwo C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ max 1 C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn ((Fin.lastCases v x) ∘ p))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 && x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  let F : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))))
  let table : List (List (Fin 10)) := [[9, 6, 8, 5, 7, 4, 1, 3, 0, 2], [7, 9, 6, 8, 5, 2, 4, 1, 3, 0], [5, 7, 9, 6, 8, 0, 2, 4, 1, 3], [8, 5, 7, 9, 6, 3, 0, 2, 4, 1], [6, 8, 5, 7, 9, 1, 3, 0, 2, 4], [4, 0, 1, 2, 3, 9, 5, 6, 7, 8], [3, 4, 0, 1, 2, 8, 9, 5, 6, 7], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let perm := fun (i j : Fin 10) => ((table.getD i.val []).getD j.val 0)
  have hi : ∀ i : Fin 10, Function.Injective (perm i) := by decide +kernel
  have hl : ∀ i : Fin 10, perm i i = 9 := by decide +kernel
  have ha : ∀ i : Fin 10, ∀ x : Fin 10 → Bool, F (x ∘ perm i) = F x := by decide +kernel
  dsimp only at cofactor ⊢
  intro C a b hf hsize hA hB hsample
  obtain ⟨i,v,D,hD,hn,he⟩ := cofactor C a b hf hsize hA hB hsample
  let σ := Equiv.ofBijective (perm i) ((Finite.injective_iff_bijective).mp (hi i))
  obtain ⟨R,hR,hs,hr⟩ := specialize 9 D σ v hD
  refine ⟨σ,v,R,ha i,hR,?_,?_⟩
  · cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;> omega
  · intro x
    rw [hr]
    apply he
    change Fin.lastCases v x (perm i i) = v
    rw [hl]
    rfl
