import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BlindGate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_7368_871
  (assemble : ∀ (C : Circuit) (P : List (ℕ × ℕ)),
    Monotone2 C → C.gates ≠ [] → P ≠ [] →
    (∀ p ∈ P, p.1 < 24+C.size ∧ p.2 < 24+C.size) →
    ∃ D : Circuit, Monotone2 D ∧ D.gates.head? = C.gates.head? ∧
      C.size ≤ D.size ∧ D.size+1 ≤ C.size+2*P.length ∧ D.output < 24+D.size ∧
      ∀ x : Fin 24 → Bool,
        (∀ i < 24+C.size, wireValue D 24 x i = wireValue C 24 x i) ∧
        D.eval (List.ofFn x) = P.any (fun p => wireValue C 24 x p.1 && wireValue C 24 x p.2))
  (core : let S : Finset (Fin 13) := {0,1,3,9}
    let F := fun x : Fin 24 → Bool => ∃ a b : Fin 12,
      (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈ S ∧
      x (Fin.castAdd 12 a) = true ∧ x (Fin.natAdd 12 b) = true
    ∃ (C : Circuit) (P : List (ℕ × ℕ)) (l r : ℕ),
      Monotone2 C ∧ C.gates.head? = some ⟨.or,[0,1]⟩ ∧ P ≠ [] ∧
      C.size+2*P.length ≤ 59 ∧ l < 24+C.size ∧ r < 24+C.size ∧
      (∀ p ∈ P, p.1 < 24+C.size ∧ p.2 < 24+C.size) ∧
      ∀ x : Fin 24 → Bool,
        ((P.any (fun p => wireValue C 24 x p.1 && wireValue C 24 x p.2)) = true ↔ F x) ∧
        (¬ F x →
          wireValue C 24 x l = (x 0 || x 1 || x 3) ∧
          wireValue C 24 x r = (x 15 || x 16 || x 18))) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 + x3 ∈ x1; have x3 : (Fin (24 : ℕ) → Bool) → Prop := fun (x3 : Fin (24 : ℕ) → Bool) => ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (12 : ℕ)), x2 (Fin.succAbove (9 : Fin (13 : ℕ)) x4) (Fin.succAbove (0 : Fin (13 : ℕ)) x5) ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (58 : ℕ) ∧ x4.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧ x4.output < (24 : ℕ) + x4.size ∧ x5 < (24 : ℕ) + x4.size ∧ x6 < (24 : ℕ) + x4.size ∧ (∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.true ↔ x3 x7) ∧ ∀ (x7 : Fin (24 : ℕ) → Bool), x4.eval (List.ofFn x7) = Bool.false → (x4.wires (List.ofFn x7)).getD x5 Bool.false = (x7 (0 : Fin (24 : ℕ)) || x7 (1 : Fin (24 : ℕ)) || x7 (3 : Fin (24 : ℕ))) ∧ (x4.wires (List.ofFn x7)).getD x6 Bool.false = (x7 (15 : Fin (24 : ℕ)) || x7 (16 : Fin (24 : ℕ)) || x7 (18 : Fin (24 : ℕ))) := by
  classical
  obtain ⟨C,P,l,r,mono,head,nonempty,budget,left,right,valid,sem⟩ := core
  have hasHead : C.gates ≠ [] := by
    intro eq
    rw [eq] at head
    cases head
  obtain ⟨D,dm,dh,le,ds,out,done⟩ := assemble C P mono hasHead nonempty valid
  refine ⟨D,l,r,dm,by omega,dh.trans head,out,by omega,by omega,?_,?_⟩
  · intro x
    rw [(done x).2]
    exact (sem x).1
  · intro x falseD
    rw [(done x).2] at falseD
    have rejected := fun h => Bool.false_ne_true (falseD.symm.trans ((sem x).1.mpr h))
    obtain ⟨pl,pr⟩ := (sem x).2 rejected
    change wireValue D 24 x l = _ ∧ wireValue D 24 x r = _
    rw [(done x).1 l left,(done x).1 r right]
    exact ⟨pl,pr⟩
