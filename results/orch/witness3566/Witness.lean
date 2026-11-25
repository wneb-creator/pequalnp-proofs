import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem input_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem edgeList_graph_eval (n : ℕ) (es : List (ℕ × ℕ))
    (hvalid : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) (x : Fin n → Bool) :
    graphFun (edgeGraph n es) ∅ x =
      es.any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, hAdj, hu, hv⟩
    rcases hAdj with ⟨_, hmem | hmem⟩
    · exact ⟨(u.val, v.val), hmem, (input_getD x u).trans hu, (input_getD x v).trans hv⟩
    · exact ⟨(v.val, u.val), hmem, (input_getD x v).trans hv, (input_getD x u).trans hu⟩
  · rintro ⟨⟨a, b⟩, he, ha, hb⟩
    have hh := hvalid (a, b) he
    let u : Fin n := ⟨a, hh.1⟩
    let v : Fin n := ⟨b, hh.2.1⟩
    refine ⟨u, v, ⟨?_, Or.inl he⟩, ?_, ?_⟩
    · intro h
      exact hh.2.2 (congrArg Fin.val h)
    · exact (input_getD x u).symm.trans ha
    · exact (input_getD x v).symm.trans hb

abbrev witnessGraph : SimpleGraph (Fin 14) :=
  PEqualNP.EdgeOwnership.edgeGraph 14 [(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)]

def witnessCircuit : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [12, 19]⟩,
    ⟨.or, [13, 20]⟩,
    ⟨.and, [1, 21]⟩,
    ⟨.and, [3, 22]⟩,
    ⟨.and, [2, 23]⟩,
    ⟨.and, [4, 24]⟩,
    ⟨.and, [0, 25]⟩,
    ⟨.and, [5, 26]⟩,
    ⟨.and, [6, 27]⟩,
    ⟨.or, [28, 32]⟩,
    ⟨.or, [30, 35]⟩,
    ⟨.or, [29, 36]⟩,
    ⟨.or, [31, 37]⟩,
    ⟨.or, [33, 38]⟩,
    ⟨.or, [34, 39]⟩], 40⟩

def witnessExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : Bool :=
  let g0 := b7 || b8
  let g1 := b7 || b9
  let g2 := b8 || b9
  let g3 := b8 || b10
  let g4 := b7 || b11
  let g5 := b9 || b11
  let g6 := b10 || b12
  let g7 := b12 || g0
  let g8 := b10 || g1
  let g9 := b13 || g2
  let g10 := b11 || g3
  let g11 := b13 || g4
  let g12 := b12 || g5
  let g13 := b13 || g6
  let g14 := b1 && g7
  let g15 := b3 && g8
  let g16 := b2 && g9
  let g17 := b4 && g10
  let g18 := b0 && g11
  let g19 := b5 && g12
  let g20 := b6 && g13
  let g21 := g14 || g18
  let g22 := g16 || g21
  let g23 := g15 || g22
  let g24 := g17 || g23
  let g25 := g19 || g24
  let g26 := g20 || g25
  g26

def witnessGraphExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : Bool :=
  (b0 && b7) || (b1 && b7) || (b3 && b7) || (b1 && b8) || (b2 && b8) || (b4 && b8) || (b2 && b9) || (b3 && b9) || (b5 && b9) || (b3 && b10) || (b4 && b10) || (b6 && b10) || (b4 && b11) || (b5 && b11) || (b0 && b11) || (b5 && b12) || (b6 && b12) || (b1 && b12) || (b6 && b13) || (b0 && b13) || (b2 && b13)

def witnessStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem witnessStep_and (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witnessStep_or (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witness_ao : PEqualNP.TopForm.IsAO2 14 witnessCircuit := by
  decide

theorem witness_size : witnessCircuit.size = 27 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_formula (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) :
    witnessExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 = witnessGraphExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 := by
  simp [witnessExpr, witnessGraphExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
    Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_eval (x : Fin 14 → Bool) :
    circuitFun 14 witnessCircuit x = witnessExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) := by
  let g0 := (x 7) || (x 8)
  let g1 := (x 7) || (x 9)
  let g2 := (x 8) || (x 9)
  let g3 := (x 8) || (x 10)
  let g4 := (x 7) || (x 11)
  let g5 := (x 9) || (x 11)
  let g6 := (x 10) || (x 12)
  let g7 := (x 12) || g0
  let g8 := (x 10) || g1
  let g9 := (x 13) || g2
  let g10 := (x 11) || g3
  let g11 := (x 13) || g4
  let g12 := (x 12) || g5
  let g13 := (x 13) || g6
  let g14 := (x 1) && g7
  let g15 := (x 3) && g8
  let g16 := (x 2) && g9
  let g17 := (x 4) && g10
  let g18 := (x 0) && g11
  let g19 := (x 5) && g12
  let g20 := (x 6) && g13
  let g21 := g14 || g18
  let g22 := g16 || g21
  let g23 := g15 || g22
  let g24 := g17 || g23
  let g25 := g19 || g24
  let g26 := g20 || g25
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by rfl
  have h0 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] ⟨.or, [7, 8]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0] := by rw [witnessStep_or]; rfl
  have h1 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0] ⟨.or, [7, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1] := by rw [witnessStep_or]; rfl
  have h2 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1] ⟨.or, [8, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2] := by rw [witnessStep_or]; rfl
  have h3 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2] ⟨.or, [8, 10]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3] := by rw [witnessStep_or]; rfl
  have h4 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3] ⟨.or, [7, 11]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4] := by rw [witnessStep_or]; rfl
  have h5 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4] ⟨.or, [9, 11]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5] := by rw [witnessStep_or]; rfl
  have h6 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5] ⟨.or, [10, 12]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6] := by rw [witnessStep_or]; rfl
  have h7 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6] ⟨.or, [12, 14]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7] := by rw [witnessStep_or]; rfl
  have h8 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7] ⟨.or, [10, 15]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8] := by rw [witnessStep_or]; rfl
  have h9 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8] ⟨.or, [13, 16]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by rw [witnessStep_or]; rfl
  have h10 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] ⟨.or, [11, 17]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] := by rw [witnessStep_or]; rfl
  have h11 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] ⟨.or, [13, 18]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] := by rw [witnessStep_or]; rfl
  have h12 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] ⟨.or, [12, 19]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] := by rw [witnessStep_or]; rfl
  have h13 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] ⟨.or, [13, 20]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] := by rw [witnessStep_or]; rfl
  have h14 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ⟨.and, [1, 21]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] := by rw [witnessStep_and]; rfl
  have h15 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] ⟨.and, [3, 22]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] := by rw [witnessStep_and]; rfl
  have h16 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] ⟨.and, [2, 23]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] := by rw [witnessStep_and]; rfl
  have h17 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] ⟨.and, [4, 24]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] := by rw [witnessStep_and]; rfl
  have h18 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] ⟨.and, [0, 25]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18] := by rw [witnessStep_and]; rfl
  have h19 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18] ⟨.and, [5, 26]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] := by rw [witnessStep_and]; rfl
  have h20 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] ⟨.and, [6, 27]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20] := by rw [witnessStep_and]; rfl
  have h21 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20] ⟨.or, [28, 32]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21] := by rw [witnessStep_or]; rfl
  have h22 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21] ⟨.or, [30, 35]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22] := by rw [witnessStep_or]; rfl
  have h23 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22] ⟨.or, [29, 36]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23] := by rw [witnessStep_or]; rfl
  have h24 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23] ⟨.or, [31, 37]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24] := by rw [witnessStep_or]; rfl
  have h25 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24] ⟨.or, [33, 38]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25] := by rw [witnessStep_or]; rfl
  have h26 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25] ⟨.or, [34, 39]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26] := by rw [witnessStep_or]; rfl
  unfold circuitFun Circuit.eval Circuit.wires witnessCircuit
  change (List.foldl witnessStep (List.ofFn x) _).getD 40 false = _
  rw [hinput]
  rw [List.foldl_cons, h0]
  rw [List.foldl_cons, h1]
  rw [List.foldl_cons, h2]
  rw [List.foldl_cons, h3]
  rw [List.foldl_cons, h4]
  rw [List.foldl_cons, h5]
  rw [List.foldl_cons, h6]
  rw [List.foldl_cons, h7]
  rw [List.foldl_cons, h8]
  rw [List.foldl_cons, h9]
  rw [List.foldl_cons, h10]
  rw [List.foldl_cons, h11]
  rw [List.foldl_cons, h12]
  rw [List.foldl_cons, h13]
  rw [List.foldl_cons, h14]
  rw [List.foldl_cons, h15]
  rw [List.foldl_cons, h16]
  rw [List.foldl_cons, h17]
  rw [List.foldl_cons, h18]
  rw [List.foldl_cons, h19]
  rw [List.foldl_cons, h20]
  rw [List.foldl_cons, h21]
  rw [List.foldl_cons, h22]
  rw [List.foldl_cons, h23]
  rw [List.foldl_cons, h24]
  rw [List.foldl_cons, h25]
  rw [List.foldl_cons, h26]
  rw [List.foldl_nil]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_graph_eval (x : Fin 14 → Bool) :
    graphFun witnessGraph ∅ x = witnessGraphExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) := by
  have hv : ∀ e ∈ ([(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)] : List (ℕ × ℕ)),
      e.1 < 14 ∧ e.2 < 14 ∧ e.1 ≠ e.2 := by decide
  rw [edgeList_graph_eval 14 _ hv x]
  simp [witnessGraphExpr, List.getD_eq_getElem?_getD, Bool.or_assoc]

theorem witness_correct : circuitFun 14 witnessCircuit = graphFun witnessGraph ∅ := by
  funext x
  rw [witness_eval, witness_graph_eval]
  exact witness_formula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)

end PEqualNP.Outside.L_meta_3566
