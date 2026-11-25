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

abbrev witnessGraph : SimpleGraph (Fin 16) :=
  PEqualNP.EdgeOwnership.edgeGraph 16 [(0, 4), (0, 5), (1, 6), (1, 7), (2, 4), (2, 6), (3, 5), (3, 7), (8, 0), (8, 1), (8, 9), (10, 2), (10, 3), (10, 11), (12, 4), (12, 7), (12, 13), (14, 5), (14, 6), (14, 15)]

def witnessCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.and, [2, 21]⟩,
    ⟨.and, [3, 22]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [24, 27]⟩,
    ⟨.or, [25, 28]⟩,
    ⟨.or, [26, 29]⟩,
    ⟨.or, [16, 9]⟩,
    ⟨.and, [8, 31]⟩,
    ⟨.or, [30, 32]⟩,
    ⟨.or, [17, 11]⟩,
    ⟨.and, [10, 34]⟩,
    ⟨.or, [33, 35]⟩,
    ⟨.or, [18, 13]⟩,
    ⟨.and, [12, 37]⟩,
    ⟨.or, [36, 38]⟩,
    ⟨.or, [19, 15]⟩,
    ⟨.and, [14, 40]⟩,
    ⟨.or, [39, 41]⟩], 42⟩

noncomputable def witnessExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) : Bool :=
  let g0 := b0 || b1
  let g1 := b2 || b3
  let g2 := b4 || b7
  let g3 := b5 || b6
  let g4 := b4 || b5
  let g5 := b4 || b6
  let g6 := b5 || b7
  let g7 := b6 || b7
  let g8 := b0 && g4
  let g9 := b2 && g5
  let g10 := b3 && g6
  let g11 := b1 && g7
  let g12 := g8 || g11
  let g13 := g9 || g12
  let g14 := g10 || g13
  let g15 := g0 || b9
  let g16 := b8 && g15
  let g17 := g14 || g16
  let g18 := g1 || b11
  let g19 := b10 && g18
  let g20 := g17 || g19
  let g21 := g2 || b13
  let g22 := b12 && g21
  let g23 := g20 || g22
  let g24 := g3 || b15
  let g25 := b14 && g24
  let g26 := g23 || g25
  g26

noncomputable def witnessGraphExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) : Bool :=
  (b0 && b4) || (b0 && b5) || (b1 && b6) || (b1 && b7) || (b2 && b4) || (b2 && b6) || (b3 && b5) || (b3 && b7) || (b8 && b0) || (b8 && b1) || (b8 && b9) || (b10 && b2) || (b10 && b3) || (b10 && b11) || (b12 && b4) || (b12 && b7) || (b12 && b13) || (b14 && b5) || (b14 && b6) || (b14 && b15)

def witnessStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem witnessStep_and (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witnessStep_or (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witness_ao : PEqualNP.TopForm.IsAO2 16 witnessCircuit := by
  decide

theorem witness_size : witnessCircuit.size = 27 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_cut_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    ((b3 && (b5 || b7)) || ((b2 && (b4 || b6)) || ((b0 && (b4 || b5)) || (b1 && (b6 || b7))))) = ((b0 && b4) || (b0 && b5) || (b1 && b6) || (b1 && b7) || (b2 && b4) || (b2 && b6) || (b3 && b5) || (b3 && b7)) := by
  first
  | solve | simp [Bool.and_or_distrib_left, Bool.and_or_distrib_right,
        Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
        Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  | revert b0 b1 b2 b3 b4 b5 b6 b7
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_formula (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) :
    witnessExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 = witnessGraphExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  change ((((((b3 && (b5 || b7)) || ((b2 && (b4 || b6)) || ((b0 && (b4 || b5)) || (b1 && (b6 || b7))))) || (b8 && ((b0 || b1) || b9))) || (b10 && ((b2 || b3) || b11))) || (b12 && ((b4 || b7) || b13))) || (b14 && ((b5 || b6) || b15))) = _
  rw [witness_cut_0 b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [witnessGraphExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_eval (x : Fin 16 → Bool) :
    circuitFun 16 witnessCircuit x = witnessExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) := by
  let g0 := (x 0) || (x 1)
  let g1 := (x 2) || (x 3)
  let g2 := (x 4) || (x 7)
  let g3 := (x 5) || (x 6)
  let g4 := (x 4) || (x 5)
  let g5 := (x 4) || (x 6)
  let g6 := (x 5) || (x 7)
  let g7 := (x 6) || (x 7)
  let g8 := (x 0) && g4
  let g9 := (x 2) && g5
  let g10 := (x 3) && g6
  let g11 := (x 1) && g7
  let g12 := g8 || g11
  let g13 := g9 || g12
  let g14 := g10 || g13
  let g15 := g0 || (x 9)
  let g16 := (x 8) && g15
  let g17 := g14 || g16
  let g18 := g1 || (x 11)
  let g19 := (x 10) && g18
  let g20 := g17 || g19
  let g21 := g2 || (x 13)
  let g22 := (x 12) && g21
  let g23 := g20 || g22
  let g24 := g3 || (x 15)
  let g25 := (x 14) && g24
  let g26 := g23 || g25
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15] := by rfl
  have h0 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15] ⟨.or, [0, 1]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0] := by rw [witnessStep_or]; rfl
  have h1 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0] ⟨.or, [2, 3]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1] := by rw [witnessStep_or]; rfl
  have h2 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1] ⟨.or, [4, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2] := by rw [witnessStep_or]; rfl
  have h3 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2] ⟨.or, [5, 6]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3] := by rw [witnessStep_or]; rfl
  have h4 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3] ⟨.or, [4, 5]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4] := by rw [witnessStep_or]; rfl
  have h5 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4] ⟨.or, [4, 6]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5] := by rw [witnessStep_or]; rfl
  have h6 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5] ⟨.or, [5, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6] := by rw [witnessStep_or]; rfl
  have h7 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6] ⟨.or, [6, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7] := by rw [witnessStep_or]; rfl
  have h8 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7] ⟨.and, [0, 20]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8] := by rw [witnessStep_and]; rfl
  have h9 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8] ⟨.and, [2, 21]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by rw [witnessStep_and]; rfl
  have h10 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] ⟨.and, [3, 22]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] := by rw [witnessStep_and]; rfl
  have h11 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] ⟨.and, [1, 23]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] := by rw [witnessStep_and]; rfl
  have h12 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] ⟨.or, [24, 27]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] := by rw [witnessStep_or]; rfl
  have h13 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] ⟨.or, [25, 28]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] := by rw [witnessStep_or]; rfl
  have h14 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ⟨.or, [26, 29]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] := by rw [witnessStep_or]; rfl
  have h15 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] ⟨.or, [16, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] := by rw [witnessStep_or]; rfl
  have h16 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] ⟨.and, [8, 31]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] := by rw [witnessStep_and]; rfl
  have h17 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] ⟨.or, [30, 32]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] := by rw [witnessStep_or]; rfl
  have h18 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] ⟨.or, [17, 11]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18] := by rw [witnessStep_or]; rfl
  have h19 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18] ⟨.and, [10, 34]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] := by rw [witnessStep_and]; rfl
  have h20 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] ⟨.or, [33, 35]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20] := by rw [witnessStep_or]; rfl
  have h21 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20] ⟨.or, [18, 13]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21] := by rw [witnessStep_or]; rfl
  have h22 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21] ⟨.and, [12, 37]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22] := by rw [witnessStep_and]; rfl
  have h23 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22] ⟨.or, [36, 38]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23] := by rw [witnessStep_or]; rfl
  have h24 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23] ⟨.or, [19, 15]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24] := by rw [witnessStep_or]; rfl
  have h25 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24] ⟨.and, [14, 40]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25] := by rw [witnessStep_and]; rfl
  have h26 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25] ⟨.or, [39, 41]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26] := by rw [witnessStep_or]; rfl
  unfold circuitFun Circuit.eval Circuit.wires witnessCircuit
  change (List.foldl witnessStep (List.ofFn x) _).getD 42 false = _
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
theorem witness_graph_eval (x : Fin 16 → Bool) :
    graphFun witnessGraph ∅ x = witnessGraphExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15) := by
  have hv : ∀ e ∈ ([(0, 4), (0, 5), (1, 6), (1, 7), (2, 4), (2, 6), (3, 5), (3, 7), (8, 0), (8, 1), (8, 9), (10, 2), (10, 3), (10, 11), (12, 4), (12, 7), (12, 13), (14, 5), (14, 6), (14, 15)] : List (ℕ × ℕ)),
      e.1 < 16 ∧ e.2 < 16 ∧ e.1 ≠ e.2 := by decide
  rw [edgeList_graph_eval 16 _ hv x]
  simp [witnessGraphExpr, List.getD_eq_getElem?_getD, Bool.or_assoc]

theorem witness_correct : circuitFun 16 witnessCircuit = graphFun witnessGraph ∅ := by
  funext x
  rw [witness_eval, witness_graph_eval]
  exact witness_formula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) (x 14) (x 15)

end PEqualNP.Outside.L_meta_3566
