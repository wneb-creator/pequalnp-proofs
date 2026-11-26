import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4031_31
    (binaryFloor : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      17 + PEqualNP.NotBracket.notCount C ≤ C.size)
    (monotoneTail : ∀ A B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 A → PEqualNP.MetaComplexity.Monotone2 B → A.size = 2 → B.size ≤ 16 →
      ∃ i : Fin 30, let mask := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ).getD i.val 0
        B.eval (A.wires (List.ofFn (fun v : Fin 10 => mask.testBit v.val))) ≠ decide (i.val < 15))
    (oneInversion : ∀ A B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 A → PEqualNP.MetaComplexity.Monotone2 B → A.size+B.size ≤ 17 →
      ∃ x : Fin 10 → Bool, let w := List.ofFn x
        B.eval (A.wires w ++ [!A.eval w]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    (¬PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))) (18 : ℕ)) := by
  classical
  rintro ⟨C,fan,small,correct⟩
  let target := fun x : Fin 10 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  have comp : ∀ x, C.eval (List.ofFn x) = target x := correct
  have floor := binaryFloor C fan correct
  have cap : PEqualNP.NotBracket.notCount C ≤ 1 := by omega
  have lengthLo : 17 ≤ C.gates.length := by change 17 ≤ C.size; omega
  have lengthHi : C.gates.length ≤ 18 := small
  let isN := fun g : PEqualNP.CircuitLowerBounds.Gate => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
  have ntest (g : PEqualNP.CircuitLowerBounds.Gate) : isN g=true ↔ g.op=PEqualNP.CircuitLowerBounds.GateOp.not := by
    exact decide_eq_true_iff
  have tally : (C.gates.filter isN).length ≤ 1 := by
    convert cap using 1
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using ntest g
  have mono (D : PEqualNP.CircuitLowerBounds.Circuit) (sub : ∀ g ∈ D.gates, g ∈ C.gates)
      (free : ∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    obtain ⟨ops,ar⟩ := fan g (sub g hg)
    refine ⟨?_,ar⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops ⊢
    exact ops.elim Or.inl (fun rest => Or.inr (rest.resolve_right (free g hg)))
  by_cases has : ∃ g ∈ C.gates, g.op=PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g,hg,op⟩ := has
    obtain ⟨pre,post,split⟩ := List.append_of_mem hg
    have mark := (ntest g).mpr op
    rw [split,List.filter_append,List.filter_cons_of_pos mark,List.length_append,List.length_cons] at tally
    have preEmpty : pre.filter isN = [] := List.length_eq_zero_iff.mp (by omega)
    have postEmpty : post.filter isN = [] := List.length_eq_zero_iff.mp (by omega)
    have clean (l : List PEqualNP.CircuitLowerBounds.Gate) (h : l.filter isN=[]) :
        ∀ z ∈ l, z.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro z hz zn
      have hit := List.mem_filter.mpr ⟨hz,(ntest z).mpr zn⟩
      rw [h] at hit
      exact List.not_mem_nil hit
    let A : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre,g.inputs.headD (10+pre.length)⟩
    let B : PEqualNP.CircuitLowerBounds.Circuit := ⟨post,C.output⟩
    have ha := mono A (by intro z hz; rw [split]; exact List.mem_append_left _ hz) (clean _ preEmpty)
    have hb := mono B (by intro z hz; rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)) (clean _ postEmpty)
    have sz : pre.length+post.length≤17 := by
      rw [split,List.length_append,List.length_cons] at lengthHi; omega
    obtain ⟨x,bad⟩ := oneInversion A B ha hb sz
    let w := List.ofFn x
    have lengthRun (ts : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) :
        (ts.foldl (fun (ws : List Bool) g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) xs).length =
          xs.length+ts.length := by
      induction ts generalizing xs with
      | nil => simp
      | cons z ts ih => simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil]; omega
    have aw : (A.wires w).length=10+pre.length := by
      change (pre.foldl _ (List.ofFn x)).length = 10+pre.length
      simpa only [List.length_ofFn] using lengthRun pre (List.ofFn x)
    have invert : g.op.eval (g.inputs.map (fun i => (A.wires w).getD i false)) = !A.eval w := by
      rw [op]
      change (!((g.inputs.map (fun i => (A.wires w).getD i false)).headD false)) = (!((A.wires w).getD (g.inputs.headD (10+pre.length)) false))
      cases hi : g.inputs with
      | nil => simp [aw]
      | cons a as => rfl
    have eval : C.eval w = B.eval (A.wires w ++ [!A.eval w]) := by
      change (C.gates.foldl _ w).getD C.output false = _
      rw [split,List.foldl_append,List.foldl_cons]
      change B.eval (A.wires w ++ [g.op.eval (g.inputs.map (fun i => (A.wires w).getD i false))]) = _
      rw [invert]
    exact bad (eval.symm.trans (comp x))
  · let A : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take 2,0⟩
    let B : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.drop 2,C.output⟩
    have split : C.gates = A.gates ++ B.gates := (List.take_append_drop 2 C.gates).symm
    have free (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g∈C.gates) := fun eq => has ⟨g,hg,eq⟩
    have left (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g∈A.gates) : g∈C.gates := split ▸ List.mem_append_left _ hg
    have right (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g∈B.gates) : g∈C.gates := split ▸ List.mem_append_right _ hg
    have ha := mono A left (fun g hg => free g (left g hg))
    have hb := mono B right (fun g hg => free g (right g hg))
    have sa : A.size=2 := by change (C.gates.take 2).length=2; simp [Nat.min_eq_left (show 2≤C.gates.length by omega)]
    have sb : B.size≤16 := by change (C.gates.drop 2).length≤16; simp; omega
    obtain ⟨i,bad⟩ := monotoneTail A B ha hb sa sb
    let rows := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ)
    let assignment := fun (j : Fin 30) (v : Fin 10) => (rows.getD j.val 0).testBit v.val
    have table : ∀ j : Fin 30, target (assignment j) = decide (j.val<15) := by decide +kernel
    have faithful (w : List Bool) : C.eval w = B.eval (A.wires w) := by
      change (C.gates.foldl _ w).getD C.output false = _
      rw [split,List.foldl_append]
      rfl
    exact bad ((faithful _).symm.trans ((comp (assignment i)).trans (table i)))
