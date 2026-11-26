import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3138_427
    (encodeMono : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ r ∈ rows, r < 2 ^ n) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc n s g rows))
    (monoUnsat :
      have x1 : List ℕ := [(515 : ℕ), (6 : ℕ), (524 : ℕ), (536 : ℕ), (529 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (776 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)];
      have x2 : List ℕ := [(554 : ℕ), (50 : ℕ), (581 : ℕ), (616 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (402 : ℕ)];
      ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)))
    (notOfInput :
      ∀ u ∈ ([(0 : ℕ), (1 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ)] : List ℕ),
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ),
        gs.length = (12 : ℕ) → PEqualNP.MetaComplexity.Monotone2 { gates := gs, output := (0 : ℕ) } →
        a ≤ (24 : ℕ) → b ≤ (24 : ℕ) →
        ∃ (x : Fin (9 : ℕ) → Bool),
          let w := List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ))]
          let w1 := { gates := gs, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires
            (w ++ [!(w.getD u Bool.false)])
          (w1.getD a Bool.false || w1.getD b Bool.false) ≠
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
             x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
             x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
             x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
             x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
             x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (notOfGate :
      ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (u a b : ℕ),
        pre.length + post.length = (12 : ℕ) → (10 : ℕ) ≤ u → u < (10 : ℕ) + pre.length →
        PEqualNP.MetaComplexity.Monotone2 { gates := pre, output := (0 : ℕ) } →
        PEqualNP.MetaComplexity.Monotone2 { gates := post, output := (0 : ℕ) } →
        a ≤ (24 : ℕ) → b ≤ (24 : ℕ) →
        ∃ (x : Fin (9 : ℕ) → Bool),
          let w0 := { gates := pre, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires
            (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ))])
          let w1 := { gates := post, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires
            (w0 ++ [!(w0.getD u Bool.false)])
          (w1.getD a Bool.false || w1.getD b Bool.false) ≠
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) ||
             x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) ||
             x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) ||
             x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
             x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) ||
             x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), x1.length = (13 : ℕ) → PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) → x2 ≤ (24 : ℕ) → x3 ≤ (24 : ℕ) → ∃ (x9 : Fin (9 : ℕ) → Bool), have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]); (x10.getD x2 Bool.false || x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b hLen hFan hNotCnt ha hb
  by_contra hNoFail
  have hGood : ∀ x : Fin 9 → Bool,
      let w := ({ gates := gs, output := 0 } : Circuit).wires (List.ofFn x ++ [x 0 || x 3])
      (w.getD a false || w.getD b false) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hne
    exact hNoFail ⟨x, hne⟩
  let F9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have stepLen : ∀ (ls : List Gate) (w : List Bool), (ls.foldl step w).length = w.length + ls.length := by
    intro ls
    induction ls with
    | nil => intro w; simp
    | cons g ls ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have getDSnocNe : ∀ (w : List Bool) (v : Bool) (i : ℕ), i ≠ w.length →
      (w ++ [v]).getD i false = w.getD i false := by
    intro w v i hi
    by_cases hlt : i < w.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have getDSnocSelf : ∀ (w : List Bool) (v : Bool), (w ++ [v]).getD w.length false = v := by
    intro w v; simp
  have getDAppendLt : ∀ (w1 w2 : List Bool) (i : ℕ), i < w1.length →
      (w1 ++ w2).getD i false = w1.getD i false := fun w1 w2 i h => List.getD_append w1 w2 false i h
  have killMono14 : ∀ C : Circuit, Monotone2 C → C.size ≤ 14 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) = F9 x) → False := by
    intro C hMono hSz hEval
    let p : List ℕ := [515, 6, 524, 536, 529, 545, 66, 132, 776, 160, 320, 288]
    let n : List ℕ := [554, 50, 581, 616, 116, 650, 713, 208, 773, 276, 897, 402]
    let bare (r : ℕ) : List Bool := List.ofFn fun i : Fin 10 => r.testBit i.val
    let added (r : ℕ) : List Bool := (List.ofFn fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 3]
    have hBound : ∀ r ∈ p ++ n, r < 2 ^ 10 := by
      have chk : (p ++ n).all (fun r => decide (r < 2 ^ 10)) = true := by decide +kernel
      exact fun r hr => of_decide_eq_true (List.all_eq_true.mp chk r hr)
    have hRows : ∀ r ∈ p ++ n,
        bare r = added r ∧ F9 (fun i : Fin 9 => r.testBit i.val) = p.contains r := by
      have chk : (p ++ n).all (fun r => decide
          (bare r = added r ∧ F9 (fun i : Fin 9 => r.testBit i.val) = p.contains r)) = true := by
        decide +kernel
      exact fun r hr => of_decide_eq_true (List.all_eq_true.mp chk r hr)
    apply monoUnsat
    apply encodeMono 10 14 (fun r => p.contains r) (p ++ n) C hBound hMono hSz
    intro r hr
    obtain ⟨hb1, hb2⟩ := hRows r hr
    change C.eval (bare r) = p.contains r
    rw [hb1]
    exact (hEval (fun i : Fin 9 => r.testBit i.val)).trans hb2
  have isNotIff : ∀ g ∈ gs, g.op.eval [false] = true ↔ g.op = GateOp.not := by
    intro g hg
    have hop := (hFan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · rw [h]; exact ⟨fun h1 => Bool.noConfusion h1, fun h1 => GateOp.noConfusion h1⟩
    · rw [h]; exact ⟨fun h1 => Bool.noConfusion h1, fun h1 => GateOp.noConfusion h1⟩
    · rw [h]; exact ⟨fun _ => rfl, fun _ => rfl⟩
  have splitCount : ∀ (ls : List Gate),
      (∀ g ∈ ls, g.op.eval [false] = false) ∨
      ∃ pre N post, ls = pre ++ N :: post ∧ N.op.eval [false] = true ∧
        ∀ g ∈ pre, g.op.eval [false] = false := by
    intro ls
    induction ls with
    | nil => exact Or.inl (by simp)
    | cons g ls ih =>
      cases hge : g.op.eval [false] with
      | true => exact Or.inr ⟨[], g, ls, rfl, hge, by simp⟩
      | false =>
        rcases ih with h0 | ⟨pre, N, post, rfl, hN, hpre⟩
        · exact Or.inl (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hge) (h0 x))
        · refine Or.inr ⟨g :: pre, N, post, rfl, hN, ?_⟩
          intro x hx
          exact (List.mem_cons.mp hx).elim (fun e => e ▸ hge) (hpre x)
  have toMono : ∀ (ls : List Gate), (∀ g ∈ ls, g ∈ gs) →
      (∀ g ∈ ls, g.op.eval [false] = false) → Monotone2 ⟨ls, 0⟩ := by
    intro ls hsub hno g hg
    have hf := hFan g (hsub g hg)
    have hnot : g.op ≠ GateOp.not := by
      intro heq
      have h1 := (isNotIff g (hsub g hg)).mpr heq
      rw [hno g hg] at h1
      cases h1
    refine ⟨?_, hf.2⟩
    have hop := hf.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnot
  rcases splitCount gs with hAllMono | ⟨pre, N, post, hEqGs, hNtrue, hPreFalse⟩
  · let gOr : Gate := ⟨GateOp.or, [a, b]⟩
    let C : Circuit := ⟨gs ++ [gOr], 23⟩
    have hCMono : Monotone2 C := by
      intro g hg
      simp only [C, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact toMono gs (fun _ h => h) hAllMono g hg
      · exact ⟨by simp [gOr], by simp [gOr]⟩
    have hCSz : C.size ≤ 14 := by
      change (gs ++ [gOr]).length ≤ 14
      simp [hLen]
    apply killMono14 C hCMono hCSz
    intro x
    unfold Circuit.eval Circuit.wires
    change ((gs ++ [gOr]).foldl step (List.ofFn x ++ [x 0 || x 3])).getD 23 false = F9 x
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hwl : (gs.foldl step (List.ofFn x ++ [x 0 || x 3])).length = 23 := by
      rw [stepLen]; simp [hLen]
    rw [← hwl]
    dsimp only [step, gOr]
    rw [getDSnocSelf]
    change ((gs.foldl step (List.ofFn x ++ [x 0 || x 3])).getD a false ||
      ((gs.foldl step (List.ofFn x ++ [x 0 || x 3])).getD b false || false)) = F9 x
    rw [Bool.or_false]
    exact hGood x
  · have hPostFalse : ∀ g ∈ post, g.op.eval [false] = false := by
      have hc : (pre ++ N :: post).countP (fun g => g.op.eval [false]) ≤ 1 := hEqGs ▸ hNotCnt
      simp only [List.countP_append, List.countP_cons, hNtrue, ite_true] at hc
      have hpost0 : post.countP (fun g => g.op.eval [false]) = 0 := by omega
      intro g hg
      have hnot := (List.countP_eq_zero.mp hpost0) g hg
      cases hgv : g.op.eval [false] with
      | false => rfl
      | true => exact absurd hgv hnot
    have hLenPP : pre.length + post.length = 12 := by
      have h1 : (pre ++ N :: post).length = 13 := hEqGs ▸ hLen
      simp only [List.length_append, List.length_cons] at h1
      omega
    have hPreMono : Monotone2 ⟨pre, 0⟩ :=
      toMono pre (fun g hg => by rw [hEqGs]; simp [hg]) hPreFalse
    have hPostMono : Monotone2 ⟨post, 0⟩ :=
      toMono post (fun g hg => by rw [hEqGs]; simp [hg]) hPostFalse
    have hNop : N.op = GateOp.not :=
      (isNotIff N (by rw [hEqGs]; simp)).mp hNtrue
    let u : ℕ := N.inputs.headD (10 + pre.length)
    have hNeval : ∀ w : List Bool, w.length = 10 + pre.length →
        step w N = w ++ [!(w.getD u false)] := by
      intro w hwl
      dsimp only [step]
      rw [hNop]
      congr 2
      cases hi : N.inputs with
      | nil =>
        dsimp only [u]
        rw [hi]
        change (!false) = !(w.getD (10 + pre.length) false)
        rw [List.getD_eq_default _ _ (by omega)]
      | cons i is =>
        dsimp only [u]
        rw [hi]
        rfl
    by_cases huGe : 10 + pre.length ≤ u
    · -- N reads out-of-bounds false, so N outputs constant true = GateOp.and []
      let gTrue : Gate := ⟨GateOp.and, []⟩
      let gOr : Gate := ⟨GateOp.or, [a, b]⟩
      let C : Circuit := ⟨pre ++ gTrue :: post ++ [gOr], 23⟩
      have hCMono : Monotone2 C := by
        intro g hg
        simp only [C, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact hPreMono g hg
        · simp only [List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact ⟨by simp [gTrue], by simp [gTrue]⟩
          · exact hPostMono g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact ⟨by simp [gOr], by simp [gOr]⟩
      have hCSz : C.size ≤ 14 := by
        change (pre ++ gTrue :: post ++ [gOr]).length ≤ 14
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      apply killMono14 C hCMono hCSz
      intro x
      unfold Circuit.eval Circuit.wires
      change ((pre ++ gTrue :: post ++ [gOr]).foldl step (List.ofFn x ++ [x 0 || x 3])).getD 23 false = F9 x
      let w0 := pre.foldl step (List.ofFn x ++ [x 0 || x 3])
      have hw0Len : w0.length = 10 + pre.length := by rw [stepLen]; simp
      have hSameN : step w0 gTrue = step w0 N := by
        rw [hNeval w0 hw0Len, List.getD_eq_default _ _ (by omega)]
        rfl
      have hSameAll : (pre ++ gTrue :: post).foldl step (List.ofFn x ++ [x 0 || x 3]) =
          gs.foldl step (List.ofFn x ++ [x 0 || x 3]) := by
        rw [hEqGs, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
        change post.foldl step (step w0 gTrue) = post.foldl step (step w0 N)
        rw [hSameN]
      rw [List.foldl_append, hSameAll, List.foldl_cons, List.foldl_nil]
      have hwl : (gs.foldl step (List.ofFn x ++ [x 0 || x 3])).length = 23 := by
        rw [stepLen]; simp [hLen]
      rw [← hwl]
      dsimp only [step, gOr]
      rw [getDSnocSelf]
      change ((gs.foldl step (List.ofFn x ++ [x 0 || x 3])).getD a false ||
        ((gs.foldl step (List.ofFn x ++ [x 0 || x 3])).getD b false || false)) = F9 x
      rw [Bool.or_false]
      exact hGood x
    · by_cases hu10 : 10 ≤ u
      · -- u is a genuine monotone gate in pre: invoke notOfGate
        obtain ⟨x, hfail⟩ := notOfGate pre post u a b hLenPP hu10 (by omega) hPreMono hPostMono ha hb
        apply hfail
        have hg := hGood x
        dsimp only at hg ⊢
        let w0 := ({ gates := pre, output := 0 } : Circuit).wires (List.ofFn x ++ [x 0 || x 3])
        have hw0Len : w0.length = 10 + pre.length := by
          change (pre.foldl step (List.ofFn x ++ [x 0 || x 3])).length = 10 + pre.length
          rw [stepLen]; simp
        have hEqW : ({ gates := gs, output := 0 } : Circuit).wires (List.ofFn x ++ [x 0 || x 3]) =
            ({ gates := post, output := 0 } : Circuit).wires (w0 ++ [!(w0.getD u false)]) := by
          unfold Circuit.wires
          rw [hEqGs, List.foldl_append, List.foldl_cons]
          change post.foldl step (step w0 N) = post.foldl step (w0 ++ [!(w0.getD u false)])
          rw [hNeval w0 hw0Len]
        change ((({ gates := post, output := 0 } : Circuit).wires (w0 ++ [!(w0.getD u false)])).getD a false ||
          (({ gates := post, output := 0 } : Circuit).wires (w0 ++ [!(w0.getD u false)])).getD b false) = _
        rw [← hEqW]
        exact hg
      · -- u < 10: hoist N to wire 10 and reduce u to {0, 1, 4, 6, 9} via V4 symmetry
        have huLt10 : u < 10 := by omega
        let shiftPre (i : ℕ) : ℕ := if i < 10 then i else i + 1
        let shiftPreG (g : Gate) : Gate := ⟨g.op, g.inputs.map shiftPre⟩
        let moveUp (i : ℕ) : ℕ :=
          if i < 10 then i
          else if i < 10 + pre.length then i + 1
          else if i = 10 + pre.length then 10
          else i
        let moveUpG (g : Gate) : Gate := ⟨g.op, g.inputs.map moveUp⟩
        let gs0 : List Gate := pre.map shiftPreG ++ post.map moveUpG
        have hGs0Mono : Monotone2 ⟨gs0, 0⟩ := by
          intro g hg
          simp only [gs0, List.mem_append, List.mem_map] at hg
          rcases hg with ⟨g0, hg0, rfl⟩ | ⟨g0, hg0, rfl⟩
          · have ho := hPreMono g0 hg0; exact ⟨ho.1, by simpa [shiftPreG] using ho.2⟩
          · have ho := hPostMono g0 hg0; exact ⟨ho.1, by simpa [moveUpG] using ho.2⟩
        have hGs0Len : gs0.length = 12 := by
          simp only [gs0, List.length_append, List.length_map]
          omega
        have hMoveLe : ∀ i : ℕ, i ≤ 24 → moveUp i ≤ 24 := by
          intro i hi
          simp only [moveUp]
          split_ifs <;> omega
        have hPreSim : ∀ (ls : List Gate) (u1 u2 : List Bool),
            u1.length + 1 = u2.length → 10 ≤ u1.length →
            (∀ i, u1.getD i false = u2.getD (shiftPre i) false) →
            ∀ i, (ls.foldl step u1).getD i false = ((ls.map shiftPreG).foldl step u2).getD (shiftPre i) false := by
          intro ls
          induction ls with
          | nil => intro u1 u2 _ _ h i; exact h i
          | cons g ls ih =>
            intro u1 u2 hl h10 h
            have hgv : g.op.eval (g.inputs.map fun j => u1.getD j false) =
                (shiftPreG g).op.eval ((shiftPreG g).inputs.map fun j => u2.getD j false) := by
              simp only [shiftPreG, List.map_map]
              congr 1; apply List.map_congr_left; intro j _; exact h j
            rw [List.map_cons, List.foldl_cons, List.foldl_cons]
            refine ih _ _ (by simp [step]; omega) (by simp [step]; omega) ?_
            intro i
            simp only [step, hgv]
            by_cases hil : i = u1.length
            · have hsh : shiftPre i = u2.length := by
                simp only [shiftPre, show ¬ i < 10 by omega, ite_false]; omega
              rw [hsh, hil]; simp
            · have hsh : shiftPre i ≠ u2.length := by
                simp only [shiftPre]; split_ifs <;> omega
              rw [getDSnocNe _ _ _ hil, getDSnocNe _ _ _ hsh, h i]
        have hPostSim : ∀ (ls : List Gate) (u1 u2 : List Bool),
            u1.length = u2.length → 10 + pre.length + 1 ≤ u1.length →
            (∀ i, u1.getD i false = u2.getD (moveUp i) false) →
            ∀ i, (ls.foldl step u1).getD i false = ((ls.map moveUpG).foldl step u2).getD (moveUp i) false := by
          intro ls
          induction ls with
          | nil => intro u1 u2 _ _ h i; exact h i
          | cons g ls ih =>
            intro u1 u2 hl hge h
            have hgv : g.op.eval (g.inputs.map fun j => u1.getD j false) =
                (moveUpG g).op.eval ((moveUpG g).inputs.map fun j => u2.getD j false) := by
              simp only [moveUpG, List.map_map]
              congr 1; apply List.map_congr_left; intro j _; exact h j
            rw [List.map_cons, List.foldl_cons, List.foldl_cons]
            refine ih _ _ (by simp [step, hl]) (by simp [step]; omega) ?_
            intro i
            simp only [step, hgv]
            by_cases hil : i = u1.length
            · have hsh : moveUp i = u2.length := by
                simp only [moveUp]
                split_ifs <;> omega
              rw [hsh, hil]; simp
            · have hsh : moveUp i ≠ u2.length := by
                simp only [moveUp]
                split_ifs <;> omega
              rw [getDSnocNe _ _ _ hil, getDSnocNe _ _ _ hsh, h i]
        have hD0Eval : ∀ x : Fin 9 → Bool,
            let w := List.ofFn x ++ [x 0 || x 3]
            let w1 := gs0.foldl step (w ++ [!(w.getD u false)])
            (w1.getD (moveUp a) false || w1.getD (moveUp b) false) = F9 x := by
          intro x
          dsimp only
          let w := List.ofFn x ++ [x 0 || x 3]
          have hwLen : w.length = 10 := by simp [w]
          let w0 := pre.foldl step w
          have hw0Len : w0.length = 10 + pre.length := by rw [stepLen, hwLen]
          let w0' := (pre.map shiftPreG).foldl step (w ++ [!(w.getD u false)])
          have hw0'Len : w0'.length = 10 + pre.length + 1 := by
            rw [stepLen]; simp [w]; omega
          have hPreBase : ∀ i, w.getD i false = (w ++ [!(w.getD u false)]).getD (shiftPre i) false := by
            intro i
            by_cases hlt : i < 10
            · simp only [shiftPre, hlt, ite_true]
              rw [getDAppendLt w _ _ (by omega)]
            · simp only [shiftPre, hlt, ite_false]
              rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [w]; omega)]
          have hPreMatch : ∀ i, w0.getD i false = w0'.getD (shiftPre i) false :=
            hPreSim pre w (w ++ [!(w.getD u false)]) (by simp [w]) (by omega) hPreBase
          have hPostBase : ∀ i, (step w0 N).getD i false = w0'.getD (moveUp i) false := by
            intro i
            rw [hNeval w0 hw0Len]
            by_cases h10 : i < 10
            · have hsh : moveUp i = i := by simp [moveUp, h10]
              have hsp : shiftPre i = i := by simp [shiftPre, h10]
              rw [hsh, getDSnocNe _ _ _ (by omega), hPreMatch i, hsp]
            · by_cases hlt : i < 10 + pre.length
              · have hsh : moveUp i = i + 1 := by simp [moveUp, h10, hlt]
                have hsp : shiftPre i = i + 1 := by simp [shiftPre, h10]
                rw [hsh, getDSnocNe _ _ _ (by omega), hPreMatch i, hsp]
              · by_cases heq : i = 10 + pre.length
                · subst heq
                  have hsh : moveUp (10 + pre.length) = 10 := by simp [moveUp]
                  rw [hsh, ← hw0Len, getDSnocSelf]
                  have hKeep : ∀ (ls : List Gate) (v : List Bool) (k : ℕ), k < v.length →
                      (ls.foldl step v).getD k false = v.getD k false := by
                    intro ls
                    induction ls with
                    | nil => intro v k _; rfl
                    | cons g ls ih =>
                      intro v k hk
                      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
                      exact getDAppendLt v _ _ hk
                  have h10' : w0'.getD 10 false = !(w.getD u false) := by
                    rw [hKeep (pre.map shiftPreG) (w ++ [!(w.getD u false)]) 10 (by simp [w])]
                    rw [← hwLen, getDSnocSelf]
                  have hu' : w0.getD u false = w.getD u false :=
                    hKeep pre w u (by omega)
                  rw [h10', hu']
                · have hsh : moveUp i = i := by simp [moveUp, h10, hlt, heq]
                  rw [hsh, List.getD_eq_default _ _ (by simp [hw0Len]; omega),
                    List.getD_eq_default _ _ (by omega)]
          have hPostMatch := hPostSim post (step w0 N) w0'
            (by simp [step, hw0Len, hw0'Len]) (by simp [step, hw0Len]) hPostBase
          have hFullW : gs.foldl step w = post.foldl step (step w0 N) := by
            rw [hEqGs, List.foldl_append, List.foldl_cons]
          have hGs0Fold : gs0.foldl step (w ++ [!(w.getD u false)]) = (post.map moveUpG).foldl step w0' := by
            simp only [gs0, List.foldl_append]; rfl
          rw [hGs0Fold, ← hPostMatch a, ← hPostMatch b, ← hFullW]
          exact hGood x
        -- Symmetry helper: permute inputs 0..8 by sigma preserving {0, 3} and F9
        have applySym : ∀ (sigma : Fin 9 → Fin 9) (u' : ℕ),
            u' ∈ ([0, 1, 4, 6, 9] : List ℕ) →
            (∀ x : Fin 9 → Bool, F9 (x ∘ sigma) = F9 x) →
            (∀ x : Fin 9 → Bool, (x (sigma 0) || x (sigma 3)) = (x 0 || x 3)) →
            (∀ x : Fin 9 → Bool,
              (List.ofFn (x ∘ sigma) ++ [(x ∘ sigma) 0 || (x ∘ sigma) 3]).getD u false =
                (List.ofFn x ++ [x 0 || x 3]).getD u' false) → False := by
          intro sigma u' hu' hF9S h03S huS
          let mapW (i : ℕ) : ℕ := if h : i < 9 then (sigma ⟨i, h⟩).val else i
          let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map mapW⟩
          let gs1 : List Gate := gs0.map mapG
          have hGs1Mono : Monotone2 ⟨gs1, 0⟩ := by
            intro g hg
            simp only [gs1, List.mem_map] at hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            have ho := hGs0Mono g0 hg0
            exact ⟨ho.1, by simpa [mapG] using ho.2⟩
          have hGs1Len : gs1.length = 12 := by simpa [gs1] using hGs0Len
          have hMapLe : ∀ i : ℕ, i ≤ 24 → mapW i ≤ 24 := by
            intro i hi
            by_cases h9 : i < 9
            · simp only [mapW, h9, dite_true]
              have := (sigma ⟨i, h9⟩).isLt
              omega
            · simp only [mapW, h9, dite_false]; exact hi
          have hSymSim : ∀ (ls : List Gate) (u1 u2 : List Bool),
              u1.length = u2.length → 9 ≤ u1.length →
              (∀ i, u1.getD i false = u2.getD (mapW i) false) →
              ∀ i, (ls.foldl step u1).getD i false = ((ls.map mapG).foldl step u2).getD (mapW i) false := by
            intro ls
            induction ls with
            | nil => intro u1 u2 _ _ h i; exact h i
            | cons g ls ih =>
              intro u1 u2 hl h9 h
              have hgv : g.op.eval (g.inputs.map fun j => u1.getD j false) =
                  (mapG g).op.eval ((mapG g).inputs.map fun j => u2.getD j false) := by
                simp only [mapG, List.map_map]
                congr 1; apply List.map_congr_left; intro j _; exact h j
              rw [List.map_cons, List.foldl_cons, List.foldl_cons]
              refine ih _ _ (by simp [step, hl]) (by simp [step]; omega) ?_
              intro i
              simp only [step, hgv]
              by_cases hil : i = u1.length
              · have hmw : mapW i = u2.length := by
                  simp only [mapW, show ¬ i < 9 by omega, dite_false]; omega
                rw [hmw, hil]; simp
              · have hmw : mapW i ≠ u2.length := by
                  by_cases hlt : i < 9
                  · simp only [mapW, hlt, dite_true]
                    have : (sigma ⟨i, hlt⟩).val < 9 := (sigma ⟨i, hlt⟩).isLt
                    omega
                  · simp only [mapW, hlt, dite_false]; omega
                rw [getDSnocNe _ _ _ hil, getDSnocNe _ _ _ hmw, h i]
          obtain ⟨x, hfail⟩ := notOfInput u' hu' gs1 (mapW (moveUp a)) (mapW (moveUp b))
            hGs1Len hGs1Mono (hMapLe _ (hMoveLe a ha)) (hMapLe _ (hMoveLe b hb))
          apply hfail
          have hbase : ∀ i,
              (List.ofFn (x ∘ sigma) ++ [(x ∘ sigma) 0 || (x ∘ sigma) 3] ++
                [!((List.ofFn (x ∘ sigma) ++ [(x ∘ sigma) 0 || (x ∘ sigma) 3]).getD u false)]).getD i false =
              (List.ofFn x ++ [x 0 || x 3] ++ [!((List.ofFn x ++ [x 0 || x 3]).getD u' false)]).getD (mapW i) false := by
            intro i
            let wS := List.ofFn (x ∘ sigma) ++ [(x ∘ sigma) 0 || (x ∘ sigma) 3]
            let wX := List.ofFn x ++ [x 0 || x 3]
            have hwSLen : wS.length = 10 := by simp [wS]
            have hwXLen : wX.length = 10 := by simp [wX]
            change (wS ++ [!(wS.getD u false)]).getD i false = (wX ++ [!(wX.getD u' false)]).getD (mapW i) false
            by_cases h9 : i < 9
            · have h9' : (sigma ⟨i, h9⟩).val < 9 := (sigma ⟨i, h9⟩).isLt
              simp only [mapW, h9, dite_true]
              rw [getDAppendLt wS _ _ (by omega), getDAppendLt wX _ _ (by omega)]
              dsimp only [wS, wX]
              rw [getDAppendLt (List.ofFn (x ∘ sigma)) _ _ (by simp [h9]),
                getDAppendLt (List.ofFn x) _ _ (by simp [h9'])]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h9, h9', dite_true,
                Option.getD_some, Function.comp_apply, Fin.eta]
            · simp only [mapW, h9, dite_false]
              by_cases h9e : i = 9
              · subst h9e
                rw [getDAppendLt wS _ _ (by omega), getDAppendLt wX _ _ (by omega)]
                dsimp only [wS, wX]
                have hLS : (List.ofFn (x ∘ sigma)).length = 9 := by simp
                have hLX : (List.ofFn x).length = 9 := by simp
                have h1 := getDSnocSelf (List.ofFn (x ∘ sigma)) ((x ∘ sigma) 0 || (x ∘ sigma) 3)
                have h2 := getDSnocSelf (List.ofFn x) (x 0 || x 3)
                rw [hLS] at h1
                rw [hLX] at h2
                rw [h1, h2]
                exact h03S x
              · by_cases h10e : i = 10
                · subst h10e
                  have h1 := getDSnocSelf wS (!(wS.getD u false))
                  have h2 := getDSnocSelf wX (!(wX.getD u' false))
                  rw [hwSLen] at h1
                  rw [hwXLen] at h2
                  rw [h1, h2]
                  exact congrArg (!·) (huS x)
                · rw [List.getD_eq_default _ _ (by simp [hwSLen]; omega),
                    List.getD_eq_default _ _ (by simp [hwXLen]; omega)]
          have hsimA := hSymSim gs0 _ _ (by simp) (by simp) hbase (moveUp a)
          have hsimB := hSymSim gs0 _ _ (by simp) (by simp) hbase (moveUp b)
          unfold Circuit.wires
          change ((gs1.foldl step (List.ofFn x ++ [x 0 || x 3] ++ [!((List.ofFn x ++ [x 0 || x 3]).getD u' false)])).getD (mapW (moveUp a)) false ||
            (gs1.foldl step (List.ofFn x ++ [x 0 || x 3] ++ [!((List.ofFn x ++ [x 0 || x 3]).getD u' false)])).getD (mapW (moveUp b)) false) = F9 x
          dsimp only [gs1]
          rw [← hsimA, ← hsimB]
          exact (hD0Eval (x ∘ sigma)).trans (hF9S x)
        let s1 : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
        let s2 : Fin 9 → Fin 9 := ![3, 2, 1, 0, 4, 8, 7, 6, 5]
        let s3 : Fin 9 → Fin 9 := ![3, 8, 5, 0, 4, 2, 6, 7, 1]
        have hF9s1 : ∀ x : Fin 9 → Bool, F9 (x ∘ s1) = F9 x := by
          have key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
              F9 ((![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) ∘ s1) =
                F9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by decide +kernel
          intro x
          have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by funext i; fin_cases i <;> rfl
          conv_lhs => rw [hx]
          conv_rhs => rw [hx]
          exact key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
        have hF9s2 : ∀ x : Fin 9 → Bool, F9 (x ∘ s2) = F9 x := by
          have key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
              F9 ((![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) ∘ s2) =
                F9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by decide +kernel
          intro x
          have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by funext i; fin_cases i <;> rfl
          conv_lhs => rw [hx]
          conv_rhs => rw [hx]
          exact key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
        have hF9s3 : ∀ x : Fin 9 → Bool, F9 (x ∘ s3) = F9 x := by
          have key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
              F9 ((![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) ∘ s3) =
                F9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by decide +kernel
          intro x
          have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by funext i; fin_cases i <;> rfl
          conv_lhs => rw [hx]
          conv_rhs => rw [hx]
          exact key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
        interval_cases u
        · exact applySym id 0 (by simp) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        · exact applySym id 1 (by simp) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        · exact applySym s2 1 (by simp) hF9s2 (fun x => Bool.or_comm (x 3) (x 0))
            (fun x => by simp [s2, List.getD_eq_getElem?_getD])
        · exact applySym s2 0 (by simp) hF9s2 (fun x => Bool.or_comm (x 3) (x 0))
            (fun x => by simp [s2, List.getD_eq_getElem?_getD])
        · exact applySym id 4 (by simp) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        · exact applySym s1 1 (by simp) hF9s1 (fun _ => rfl)
            (fun x => by simp [s1, List.getD_eq_getElem?_getD])
        · exact applySym id 6 (by simp) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        · exact applySym s1 6 (by simp) hF9s1 (fun _ => rfl)
            (fun x => by simp [s1, List.getD_eq_getElem?_getD])
        · exact applySym s3 1 (by simp) hF9s3 (fun x => Bool.or_comm (x 3) (x 0))
            (fun x => by simp [s3, List.getD_eq_getElem?_getD])
        · exact applySym id 9 (by simp) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
