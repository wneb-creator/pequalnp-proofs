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

abbrev witnessGraph : SimpleGraph (Fin 31) :=
  PEqualNP.EdgeOwnership.edgeGraph 31 [(0, 6), (3, 6), (0, 7), (4, 7), (0, 8), (5, 8), (1, 9), (3, 9), (1, 10), (4, 10), (1, 11), (5, 11), (2, 12), (3, 12), (2, 13), (4, 13), (2, 14), (5, 14), (15, 0), (15, 1), (15, 2), (15, 16), (17, 3), (17, 4), (17, 5), (17, 18), (19, 6), (19, 10), (19, 14), (19, 20), (21, 6), (21, 11), (21, 13), (21, 22), (23, 7), (23, 9), (23, 14), (23, 24), (25, 7), (25, 11), (25, 12), (25, 26), (27, 8), (27, 9), (27, 13), (27, 28), (29, 8), (29, 10), (29, 12), (29, 30)]

def witnessCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [31, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [33, 5]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [35, 14]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [37, 13]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [39, 14]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [41, 12]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [43, 13]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [45, 12]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [47, 8]⟩,
    ⟨.and, [0, 48]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [50, 11]⟩,
    ⟨.and, [1, 51]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [53, 14]⟩,
    ⟨.and, [2, 54]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [56, 12]⟩,
    ⟨.and, [3, 57]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [59, 13]⟩,
    ⟨.and, [4, 60]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [62, 14]⟩,
    ⟨.and, [5, 63]⟩,
    ⟨.or, [49, 52]⟩,
    ⟨.or, [65, 55]⟩,
    ⟨.or, [66, 58]⟩,
    ⟨.or, [67, 61]⟩,
    ⟨.or, [68, 64]⟩,
    ⟨.or, [32, 16]⟩,
    ⟨.and, [15, 70]⟩,
    ⟨.or, [69, 71]⟩,
    ⟨.or, [34, 18]⟩,
    ⟨.and, [17, 73]⟩,
    ⟨.or, [72, 74]⟩,
    ⟨.or, [36, 20]⟩,
    ⟨.and, [19, 76]⟩,
    ⟨.or, [75, 77]⟩,
    ⟨.or, [38, 22]⟩,
    ⟨.and, [21, 79]⟩,
    ⟨.or, [78, 80]⟩,
    ⟨.or, [40, 24]⟩,
    ⟨.and, [23, 82]⟩,
    ⟨.or, [81, 83]⟩,
    ⟨.or, [42, 26]⟩,
    ⟨.and, [25, 85]⟩,
    ⟨.or, [84, 86]⟩,
    ⟨.or, [44, 28]⟩,
    ⟨.and, [27, 88]⟩,
    ⟨.or, [87, 89]⟩,
    ⟨.or, [46, 30]⟩,
    ⟨.and, [29, 91]⟩,
    ⟨.or, [90, 92]⟩], 93⟩

noncomputable def witnessExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 : Bool) : Bool :=
  let g0 := b0 || b1
  let g1 := g0 || b2
  let g2 := b3 || b4
  let g3 := g2 || b5
  let g4 := b6 || b10
  let g5 := g4 || b14
  let g6 := b6 || b11
  let g7 := g6 || b13
  let g8 := b7 || b9
  let g9 := g8 || b14
  let g10 := b7 || b11
  let g11 := g10 || b12
  let g12 := b8 || b9
  let g13 := g12 || b13
  let g14 := b8 || b10
  let g15 := g14 || b12
  let g16 := b6 || b7
  let g17 := g16 || b8
  let g18 := b0 && g17
  let g19 := b9 || b10
  let g20 := g19 || b11
  let g21 := b1 && g20
  let g22 := b12 || b13
  let g23 := g22 || b14
  let g24 := b2 && g23
  let g25 := b6 || b9
  let g26 := g25 || b12
  let g27 := b3 && g26
  let g28 := b7 || b10
  let g29 := g28 || b13
  let g30 := b4 && g29
  let g31 := b8 || b11
  let g32 := g31 || b14
  let g33 := b5 && g32
  let g34 := g18 || g21
  let g35 := g34 || g24
  let g36 := g35 || g27
  let g37 := g36 || g30
  let g38 := g37 || g33
  let g39 := g1 || b16
  let g40 := b15 && g39
  let g41 := g38 || g40
  let g42 := g3 || b18
  let g43 := b17 && g42
  let g44 := g41 || g43
  let g45 := g5 || b20
  let g46 := b19 && g45
  let g47 := g44 || g46
  let g48 := g7 || b22
  let g49 := b21 && g48
  let g50 := g47 || g49
  let g51 := g9 || b24
  let g52 := b23 && g51
  let g53 := g50 || g52
  let g54 := g11 || b26
  let g55 := b25 && g54
  let g56 := g53 || g55
  let g57 := g13 || b28
  let g58 := b27 && g57
  let g59 := g56 || g58
  let g60 := g15 || b30
  let g61 := b29 && g60
  let g62 := g59 || g61
  g62

noncomputable def witnessGraphExpr (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 : Bool) : Bool :=
  (b0 && b6) || (b3 && b6) || (b0 && b7) || (b4 && b7) || (b0 && b8) || (b5 && b8) || (b1 && b9) || (b3 && b9) || (b1 && b10) || (b4 && b10) || (b1 && b11) || (b5 && b11) || (b2 && b12) || (b3 && b12) || (b2 && b13) || (b4 && b13) || (b2 && b14) || (b5 && b14) || (b15 && b0) || (b15 && b1) || (b15 && b2) || (b15 && b16) || (b17 && b3) || (b17 && b4) || (b17 && b5) || (b17 && b18) || (b19 && b6) || (b19 && b10) || (b19 && b14) || (b19 && b20) || (b21 && b6) || (b21 && b11) || (b21 && b13) || (b21 && b22) || (b23 && b7) || (b23 && b9) || (b23 && b14) || (b23 && b24) || (b25 && b7) || (b25 && b11) || (b25 && b12) || (b25 && b26) || (b27 && b8) || (b27 && b9) || (b27 && b13) || (b27 && b28) || (b29 && b8) || (b29 && b10) || (b29 && b12) || (b29 && b30)

def witnessStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem witnessStep_and (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witnessStep_or (w : List Bool) (a b : ℕ) :
    witnessStep w ⟨.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [witnessStep, GateOp.eval]

theorem witness_ao : PEqualNP.TopForm.IsAO2 31 witnessCircuit := by
  decide

theorem witness_size : witnessCircuit.size = 63 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_cut_0 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    ((((((b0 && ((b6 || b7) || b8)) || (b1 && ((b9 || b10) || b11))) || (b2 && ((b12 || b13) || b14))) || (b3 && ((b6 || b9) || b12))) || (b4 && ((b7 || b10) || b13))) || (b5 && ((b8 || b11) || b14))) = ((b0 && b6) || (b3 && b6) || (b0 && b7) || (b4 && b7) || (b0 && b8) || (b5 && b8) || (b1 && b9) || (b3 && b9) || (b1 && b10) || (b4 && b10) || (b1 && b11) || (b5 && b11) || (b2 && b12) || (b3 && b12) || (b2 && b13) || (b4 && b13) || (b2 && b14) || (b5 && b14)) := by
  simp [Bool.and_or_distrib_left, Bool.and_or_distrib_right,
    Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

end PEqualNP.Outside.L_meta_3566
