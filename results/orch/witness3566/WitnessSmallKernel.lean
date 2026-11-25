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

abbrev witnessGraph : SimpleGraph (Fin 11) :=
  PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (4, 6), (1, 7), (3, 7), (1, 8), (4, 8), (2, 9), (3, 9), (2, 10), (4, 10)]

def witnessCircuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.and, [1, 17]⟩,
    ⟨.and, [3, 18]⟩,
    ⟨.and, [4, 19]⟩,
    ⟨.and, [2, 20]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [22, 26]⟩,
    ⟨.or, [23, 27]⟩], 28⟩

def witnessExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) : Bool :=
  let g0 := b5 || b6
  let g1 := b5 || b7
  let g2 := b6 || b7
  let g3 := b6 || b8
  let g4 := b5 || b9
  let g5 := b0 && g0
  let g6 := b8 || g1
  let g7 := b9 || g2
  let g8 := b10 || g3
  let g9 := b10 || g4
  let g10 := b1 && g6
  let g11 := b3 && g7
  let g12 := b4 && g8
  let g13 := b2 && g9
  let g14 := g5 || g10
  let g15 := g13 || g14
  let g16 := g11 || g15
  let g17 := g12 || g16
  g17

def witnessGraphExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) : Bool :=
  (b0 && b5) || (b1 && b5) || (b2 && b5) || (b0 && b6) || (b3 && b6) || (b4 && b6) || (b1 && b7) || (b3 && b7) || (b1 && b8) || (b4 && b8) || (b2 && b9) || (b3 && b9) || (b2 && b10) || (b4 && b10)

def witnessStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem witnessStep_and (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witnessStep_or (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witness_ao : PEqualNP.TopForm.IsAO2 11 witnessCircuit := by
  decide

theorem witness_size : witnessCircuit.size = 18 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_formula (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) :
    witnessExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 = witnessGraphExpr b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_eval (x : Fin 11 → Bool) :
    circuitFun 11 witnessCircuit x = witnessExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) := by
  let g0 := (x 5) || (x 6)
  let g1 := (x 5) || (x 7)
  let g2 := (x 6) || (x 7)
  let g3 := (x 6) || (x 8)
  let g4 := (x 5) || (x 9)
  let g5 := (x 0) && g0
  let g6 := (x 8) || g1
  let g7 := (x 9) || g2
  let g8 := (x 10) || g3
  let g9 := (x 10) || g4
  let g10 := (x 1) && g6
  let g11 := (x 3) && g7
  let g12 := (x 4) && g8
  let g13 := (x 2) && g9
  let g14 := g5 || g10
  let g15 := g13 || g14
  let g16 := g11 || g15
  let g17 := g12 || g16
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] := by rfl
  have h0 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] ⟨.or, [5, 6]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0] := by rw [witnessStep_or]; rfl
  have h1 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0] ⟨.or, [5, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1] := by rw [witnessStep_or]; rfl
  have h2 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1] ⟨.or, [6, 7]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2] := by rw [witnessStep_or]; rfl
  have h3 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2] ⟨.or, [6, 8]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3] := by rw [witnessStep_or]; rfl
  have h4 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3] ⟨.or, [5, 9]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4] := by rw [witnessStep_or]; rfl
  have h5 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4] ⟨.and, [0, 11]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5] := by rw [witnessStep_and]; rfl
  have h6 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5] ⟨.or, [8, 12]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6] := by rw [witnessStep_or]; rfl
  have h7 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6] ⟨.or, [9, 13]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7] := by rw [witnessStep_or]; rfl
  have h8 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7] ⟨.or, [10, 14]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8] := by rw [witnessStep_or]; rfl
  have h9 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8] ⟨.or, [10, 15]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] := by rw [witnessStep_or]; rfl
  have h10 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9] ⟨.and, [1, 17]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] := by rw [witnessStep_and]; rfl
  have h11 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] ⟨.and, [3, 18]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] := by rw [witnessStep_and]; rfl
  have h12 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] ⟨.and, [4, 19]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] := by rw [witnessStep_and]; rfl
  have h13 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12] ⟨.and, [2, 20]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] := by rw [witnessStep_and]; rfl
  have h14 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13] ⟨.or, [16, 21]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] := by rw [witnessStep_or]; rfl
  have h15 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14] ⟨.or, [24, 25]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] := by rw [witnessStep_or]; rfl
  have h16 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] ⟨.or, [22, 26]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] := by rw [witnessStep_or]; rfl
  have h17 : witnessStep [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16] ⟨.or, [23, 27]⟩ =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] := by rw [witnessStep_or]; rfl
  unfold circuitFun Circuit.eval Circuit.wires witnessCircuit
  change (List.foldl witnessStep (List.ofFn x) _).getD 28 false = _
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
  rw [List.foldl_nil]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_graph_eval (x : Fin 11 → Bool) :
    graphFun witnessGraph ∅ x = witnessGraphExpr (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) := by
  have hv : ∀ e ∈ ([(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (4, 6), (1, 7), (3, 7), (1, 8), (4, 8), (2, 9), (3, 9), (2, 10), (4, 10)] : List (ℕ × ℕ)),
      e.1 < 11 ∧ e.2 < 11 ∧ e.1 ≠ e.2 := by decide
  rw [edgeList_graph_eval 11 _ hv x]
  simp [witnessGraphExpr, List.getD_eq_getElem?_getD, Bool.or_assoc]

theorem witness_correct : circuitFun 11 witnessCircuit = graphFun witnessGraph ∅ := by
  funext x
  rw [witness_eval, witness_graph_eval]
  exact witness_formula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)

end PEqualNP.Outside.L_meta_3566
