import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4037_27
    (extractPins : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : Fin C.gates.length),
      PEqualNP.MetaComplexity.FanInTwo C →
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 0 ∈ (C.gates.get i).inputs →
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and → 10 ∈ (C.gates.get j).inputs →
      (∀ k : Fin C.gates.length, k ≠ i → k ≠ j →
        let g := C.gates.get k
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not →
          g.inputs.head? ≠ some 0 ∧ g.inputs.head? ≠ some 10) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 0 ∉ g.inputs ∧ 10 ∉ g.inputs)) →
      ∃ (A B D : PEqualNP.CircuitLowerBounds.Circuit) (first : Bool) (a b : Bool ⊕ ℕ),
        (∀ T ∈ [A,B,D], PEqualNP.MetaComplexity.FanInTwo T) ∧
        A.size + B.size + D.size + 2 ≤ C.size ∧ ∀ x : Fin 10 → Bool,
        let pin := fun (pos : Bool) (s : Bool ⊕ ℕ) (ws : List Bool) =>
          let v := s.elim id (fun k => ws.getD k false)
          if pos then x 0 || v else (!x 0) && v
        let w := A.wires (List.ofFn (fun i : Fin 9 => x i.succ))
        let w' := B.wires (w ++ [pin first a w])
        C.eval (List.ofFn x ++ [!x 0]) = D.eval (w' ++ [pin (!first) b w']))
    (obstruction : ∀ (A B D : PEqualNP.CircuitLowerBounds.Circuit) (first : Bool) (a b : Bool ⊕ ℕ),
      (∀ T ∈ [A,B,D], PEqualNP.MetaComplexity.FanInTwo T) →
      A.size + B.size + D.size ≤ 16 → ∃ x : Fin 10 → Bool,
        let pin := fun (pos : Bool) (s : Bool ⊕ ℕ) (ws : List Bool) =>
          let v := s.elim id (fun k => ws.getD k false)
          if pos then x 0 || v else (!x 0) && v
        let w := A.wires (List.ofFn (fun i : Fin 9 => x i.succ))
        let w' := B.wires (w ++ [pin first a w])
        D.eval (w' ++ [pin (!first) b w']) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → ¬∃ (x5 : Fin x1.gates.length) (x6 : Fin x1.gates.length), x5 ≠ x6 ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∈ (x1.gates.get x5).inputs ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (10 : ℕ) ∈ (x1.gates.get x6).inputs ∧ ∀ x7 ∈ [((0 : ℕ), x5), ((10 : ℕ), x6)], ∀ (x9 : Fin x1.gates.length), ((x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x9).inputs.head? = Option.some x7.1 → x9 = x7.2) ∧ ((x1.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.1 ∈ (x1.gates.get x9).inputs → x9 = x7.2)) := by
  intro C hfan hsize hEval
  rintro ⟨i,j,_,oi,mi,oj,mj,unique⟩
  obtain ⟨A,B,D,first,a,b,hparts,small,sound⟩ := extractPins C i j hfan oi mi oj mj (by
    intro k ki kj
    have left := unique ((0 : ℕ),i) (by simp) k
    have right := unique ((10 : ℕ),j) (by simp) k
    exact ⟨fun op => ⟨fun m => ki (left.1 op m),fun m => kj (right.1 op m)⟩,
      fun op => ⟨fun m => ki (left.2 op m),fun m => kj (right.2 op m)⟩⟩)
  obtain ⟨x,miss⟩ := obstruction A B D first a b hparts (by omega)
  exact miss ((sound x).symm.trans (hEval x))
