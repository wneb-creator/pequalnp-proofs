import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3079_584
    (compile : let read (w : List Bool) (i : Fin 26) :=
        if i.val = 25 then true else w.getD i.val false
      let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
        w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
      ∀ (a b o : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)), gs.length ≤ 13 →
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
          C.size ≤ 15 ∧
          (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧
          ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
            (((1, a, b) :: gs).foldl step (List.ofFn x ++ [x 0 || x 4])).getD o.val false)
    (lower :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 →
      Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9
      C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4
      && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 &&
      x 8) || (x 8 && x 5)) → 16 ≤ C.size) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13
      : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →
      (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2
      ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨
      (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →
      ∃ x10 < (512 : ℕ),
        have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11
        have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if
          ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false
        have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin
          (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1
          = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11
          (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4)
        x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ),
          (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ)
          (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b o gs hlen _ _ _ _
  by_contra! agrees
  obtain ⟨C, fan, size, first, eval⟩ := compile a b o gs hlen
  apply Nat.not_le_of_gt (show C.size < 16 by omega)
  apply lower C fan first
  funext x
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  let input (r : ℕ) (i : Fin 9) := r.testBit i.val
  have bounded : bits.toNat < 512 := by
    simpa only [List.length_ofFn] using bits.isLt
  have recover : input bits.toNat = x := by
    funext i
    change bits.getLsbD i.val = x i
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    simp only [bits, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
  let trace (z : Fin 9 → Bool) :=
    (((1, a, b) :: gs).foldl step (List.ofFn z ++ [z 0 || z 4])).getD o.val false
  let edge (z : Fin 9 → Bool) :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => z (Fin.ofNat 9 (e / 10)) && z (Fin.ofNat 9 (e % 10)))
  have row : trace (input bits.toNat) = edge (input bits.toNat) :=
    Classical.not_not.mp (agrees bits.toNat bounded)
  rw [recover] at row
  change C.eval (List.ofFn x) = _
  refine (eval x).trans (row.trans ?_)
  simp [edge, List.any_cons, Bool.or_assoc] <;> rfl
