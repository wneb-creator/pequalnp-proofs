import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3821_38
    (hcompile : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Equiv.Perm (Fin 10)) (v : Bool),
  PEqualNP.MetaComplexity.FanInTwo C →
  let R := fun y : Fin 9 → Bool => (Fin.lastCases v y : Fin 10 → Bool) ∘ s
  let W := fun i : ℕ => fun y : Fin 9 → Bool => (C.wires (List.ofFn (R y))).getD i false
  PEqualNP.MetaComplexity.HasCircuitSize 9 (fun y => C.eval (List.ofFn (R y)))
    (((Finset.range (10 + C.size)).image W) \ insert (fun _ : Fin 9 → Bool => false) (Finset.univ.image (fun i : Fin 9 => fun y : Fin 9 → Bool => y i))).card)
    (hcount : let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i => (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) || (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) || (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)));
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 19 →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) →
    (∀ x : Fin 10 → Bool, G x = false ∨ (List.ofFn x).count true ≤ 2 →
      C.eval (List.ofFn x) = G x) →
    ∃ (s : Equiv.Perm (Fin 10)) (v : Bool),
      (∀ x : Fin 10 → Bool, G (x ∘ s) = G x) ∧
      let R := fun y : Fin 9 → Bool => (Fin.lastCases v y : Fin 10 → Bool) ∘ s
      let W := fun i : ℕ => fun y : Fin 9 → Bool => (C.wires (List.ofFn (R y))).getD i false
      (((Finset.range (10 + C.size)).image W) \ insert (fun _ : Fin 9 → Bool => false) (Finset.univ.image (fun i : Fin 9 => fun y : Fin 9 → Bool => y i))).card ≤ if v = true then 10 else 15) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  classical
  dsimp only
  intro C a b fan small left right promise
  let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i => (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) || (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) || (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  let W := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
  let U := fun x : Fin 10 → Bool => W x a || W x b
  change ∀ x : Fin 10 → Bool, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x at promise
  let A : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates ++ [⟨.or, [a, b]⟩], 10 + C.size⟩
  have fanA : PEqualNP.MetaComplexity.FanInTwo A := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact fan g hg
    · obtain rfl := List.mem_singleton.mp hg
      simp
  have smallA : A.size ≤ 19 := by
    change (C.gates ++ [_]).length ≤ 19
    change C.gates.length ≤ 18 at small
    simp only [List.length_append, List.length_singleton]
    omega
  have wirelen (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
      ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      change ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (x ++ [_])).length = _
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have evalA (x : Fin 10 → Bool) : A.eval (List.ofFn x) = U x := by
    have len : (C.wires (List.ofFn x)).length = 10 + C.size := by
      simpa [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.CircuitLowerBounds.Circuit.wires] using wirelen C.gates (List.ofFn x)
    change ((C.gates ++ [_]).foldl _ (List.ofFn x)).getD (10 + C.size) false = _
    rw [List.foldl_append]
    change ((C.wires (List.ofFn x)) ++ [W x a || (W x b || false)]).getD (10 + C.size) false = U x
    rw [Bool.or_false, ← len]
    simp [U]
  let P := fun n : ℕ => ∃ B : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo B ∧ B.size = n ∧
      ∀ x : Fin 10 → Bool, B.eval (List.ofFn x) = U x
  have existsP : ∃ n, P n := ⟨A.size, A, fanA, rfl, evalA⟩
  obtain ⟨B, fanB, sizeB, evalB⟩ := Nat.find_spec existsP
  have smallB : B.size ≤ 19 := by
    have bound := Nat.find_min' existsP (show P A.size from ⟨A, fanA, rfl, evalA⟩)
    omega
  have minimalB (D : PEqualNP.CircuitLowerBounds.Circuit)
      (fanD : PEqualNP.MetaComplexity.FanInTwo D)
      (same : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = B.eval (List.ofFn x)) : B.size ≤ D.size := by
    have bound := Nat.find_min' existsP (show P D.size from
      ⟨D, fanD, rfl, fun x => (same x).trans (evalB x)⟩)
    omega
  obtain ⟨s, v, symmetry, bound⟩ := hcount B fanB smallB minimalB
    (fun x hx => (evalB x).trans (promise x hx))
  obtain ⟨E, fanE, sizeE, evalE⟩ := hcompile B s v fanB
  refine ⟨s, v, E, symmetry, fanE, le_trans sizeE bound, ?_⟩
  intro y
  exact (evalE y).trans (evalB _)
