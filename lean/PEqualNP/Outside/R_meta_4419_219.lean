import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A checked cofactor lemma handles circuits with at least three constant readers.
theorem PEqualNP.Outside.R_meta_4419_219
    (erase : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ))
    (cofactor : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.cons Bool.false x2)) (11 : ℕ))
    (low : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : ℕ) (x3 : Fin x2 → Bool) (x4 x5 : Fin x2 → ℕ × Bool) (x6 : ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (13 : ℕ) ≤ x2 →     x2 ≤ (14 : ℕ) →       (∀ (x10 : Fin x2), (x4 x10).1 < (10 : ℕ) + ↑x10 ∧ (x5 x10).1 < (10 : ℕ) + ↑x10) →         x6 < (10 : ℕ) + x2 →           (∀ (x12 : Fin x2), ((x4 x12).2 = Bool.true → (x4 x12).1 = (0 : ℕ) ∨ (x4 x12).1 = (9 : ℕ)) ∧ ((x5 x12).2 = Bool.true → (x5 x12).1 = (0 : ℕ) ∨ (x5 x12).1 = (9 : ℕ))) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x2),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                   List.countP (fun b : Bool => b) (List.ofFn fun j : Fin x2 =>
        decide ((x4 j).1 = 0 ∨ (x4 j).1 = 9 ∨ (x5 j).1 = 0 ∨ (x5 j).1 = 9)) ≤ 2 →
      ∃ (x16 : Fin (9 : ℕ) → Bool), x7 x16 x6 ≠ x1 x16) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : ℕ) (x3 : Fin x2 → Bool) (x4 x5 : Fin x2 → ℕ × Bool) (x6 : ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (13 : ℕ) ≤ x2 →     x2 ≤ (14 : ℕ) →       (∀ (x10 : Fin x2), (x4 x10).1 < (10 : ℕ) + ↑x10 ∧ (x5 x10).1 < (10 : ℕ) + ↑x10) →         x6 < (10 : ℕ) + x2 →           (∀ (x12 : Fin x2), ((x4 x12).2 = Bool.true → (x4 x12).1 = (0 : ℕ) ∨ (x4 x12).1 = (9 : ℕ)) ∧ ((x5 x12).2 = Bool.true → (x5 x12).1 = (0 : ℕ) ∨ (x5 x12).1 = (9 : ℕ))) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x2),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                   ∃ (x16 : Fin (9 : ℕ) → Bool), x7 x16 x6 ≠ x1 x16 := by
  dsimp only
  intro k op left right out value h13 h14 earlier outBound signs inputs zero evaluate
  let flagged (j : Fin k) : Bool :=
    decide ((left j).1 = 0 ∨ (left j).1 = 9 ∨ (right j).1 = 0 ∨ (right j).1 = 9)
  rcases Nat.lt_or_ge ((List.ofFn flagged).countP id) 3 with few | many
  · exact low k op left right out value h13 h14 earlier outBound signs inputs zero evaluate (by
      change (List.ofFn flagged).countP id ≤ 2
      omega)
  by_contra! agree
  let ref (p : ℕ × Bool) : ℕ := if p.2 then 9 else if p.1 = 9 then 0 else p.1
  let gate (j : Fin k) : Gate := ⟨if op j then .and else .or, [ref (left j), ref (right j)]⟩
  let tail := List.ofFn gate
  let beginGate : Gate := ⟨.not, [0]⟩
  let D : Circuit := ⟨beginGate :: tail, if out = 9 then 0 else out⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have beginAt (x : Fin 9 → Bool) : step (List.ofFn x) beginGate = List.ofFn x ++ [!x 0] := by
    change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = List.ofFn x ++ [!x 0]
    simp [List.getD_eq_getElem?_getD]
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = !x 0 := by
    change (tail.foldl step (step (List.ofFn x) beginGate)).getD 9 false = _
    rw [beginAt, keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have legal : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hm
    · simp [beginGate]
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
      cases h : op j <;> simp [gate, h]
  have readIff (p : ℕ × Bool) (hp : p.2 = true → p.1 = 0 ∨ p.1 = 9) :
      (ref p = 0 ∨ ref p = 9) ↔ p.1 = 0 ∨ p.1 = 9 := by
    cases b : p.2
    · by_cases h : p.1 = 9 <;> simp [ref, b, h]
    · simp [ref, b, hp b]
  let norm (g : Gate) : Gate :=
    { op := g.op, inputs := if g.op.eval [false] then g.inputs.take 1 else g.inputs }
  let reads (g : Gate) : Bool := [0, 9].any fun w => g.inputs.contains w
  have three : 3 ≤ (((D.gates.drop 1).map norm).filter reads).length := by
    have unnorm (j : Fin k) : norm (gate j) = gate j := by
      cases b : op j <;> simp only [norm, gate, b, Bool.false_eq_true, if_false, if_true] <;> rfl
    change 3 ≤ ((tail.map norm).filter reads).length
    have mapped : tail.map norm = tail := by
      unfold tail
      rw [List.map_ofFn]
      congr 1
      funext j
      exact unnorm j
    rw [mapped, ← List.countP_eq_length_filter]
    have rr (j : Fin k) : reads (gate j) = flagged j := by
      rw [Bool.eq_iff_iff]
      simp [reads, flagged, gate, List.contains_iff_mem, eq_comm (a := 0), eq_comm (a := 9)]
      have l := readIff (left j) (signs j).1
      have r := readIff (right j) (signs j).2
      tauto
    have seq : tail.map reads = List.ofFn flagged := by
      unfold tail
      rw [List.map_ofFn]
      congr 1
      exact funext rr
    rw [← seq, List.countP_map] at many
    exact many
  let start (z : Fin 8 → Bool) := List.ofFn (Fin.cons false z : Fin 9 → Bool) ++ [true]
  let stage (z : Fin 8 → Bool) (m : ℕ) := (tail.take m).foldl step (start z)
  have startLen (z : Fin 8 → Bool) : (start z).length = 10 := by simp [start]
  have len (z : Fin 8 → Bool) (m : ℕ) (hm : m ≤ k) : (stage z m).length = 10 + m := by
    have f (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
    simp [stage, f, startLen, tail, min_eq_left hm]
  have fixed (z : Fin 8 → Bool) (m : ℕ) : (stage z m).getD 9 false = true := by
    rw [show stage z m = (tail.take m).foldl step (start z) from rfl, keep _ _ _ (by simp [startLen])]
    simp [start, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have sound (z : Fin 8 → Bool) (m : ℕ) (hm : m ≤ k) (i : ℕ) (hi : i < 10 + m)
      (hin : i ≠ 9) : (stage z m).getD i false = value (Fin.cons false z) i := by
    induction m generalizing i with
    | zero =>
      have ilt : i < 9 := by omega
      let ii : Fin 9 := ⟨i, ilt⟩
      change (start z).getD i false = value (Fin.cons false z) i
      rw [show value (Fin.cons false z) i = (Fin.cons false z : Fin 9 → Bool) ii from
        inputs (Fin.cons false z) ii]
      have hLen : i < (List.ofFn (Fin.cons false z : Fin 9 → Bool)).length := by simpa using ilt
      simp only [start, List.getD_eq_getElem?_getD, List.getElem?_append_left hLen]
      rw [List.getElem?_eq_getElem hLen]
      simp only [List.getElem_ofFn, Option.getD_some, ii]
    | succ m ih =>
      have hmk : m < k := by omega
      let j : Fin k := ⟨m, hmk⟩
      have expand : stage z (m+1) = step (stage z m) (gate j) := by
        unfold stage
        rw [List.take_succ_eq_append_getElem (by simpa [tail] using hmk), List.foldl_append]
        simp [tail, j]
      rw [expand]
      have lm := len z m (by omega)
      by_cases hit : i < 10 + m
      · rw [show (step (stage z m) (gate j)).getD i false = (stage z m).getD i false by
              simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < (stage z m).length)]]
        exact ih (by omega) i hit hin
      · have eq : i = 10 + m := by omega
        subst i
        have readSound (p : ℕ × Bool) (hp : p.1 < 10 + m)
            (hs : p.2 = true → p.1 = 0 ∨ p.1 = 9) :
            (stage z m).getD (ref p) false = (value (Fin.cons false z) p.1 ^^ p.2) := by
          cases b : p.2
          · by_cases h : p.1 = 9
            · have v0 := ih (by omega) 0 (by omega) (by decide)
              have vals : value (Fin.cons false z) 0 = false := inputs _ 0
              simpa [ref, b, h, vals, zero] using v0
            · simpa [ref, b, h] using ih (by omega) p.1 hp h
          · rcases hs b with hz | hz
            · have vals : value (Fin.cons false z) 0 = false := inputs _ 0
              rw [show ref p = 9 by simp [ref, b], fixed]
              simp [b, hz, vals]
            · rw [show ref p = 9 by simp [ref, b], fixed]
              simp [b, hz, zero]
        have next := evaluate (Fin.cons false z) j
        change value (Fin.cons false z) (10+m) = _ at next
        have l := readSound (left j) (earlier j).1 (signs j).1
        have r := readSound (right j) (earlier j).2 (signs j).2
        simp only [List.getD_eq_getElem?_getD] at l r
        have last (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
        simp only [step]
        rw [← lm, last, lm, next]
        cases h : op j
        · simp only [gate, h, Bool.false_eq_true, if_false]
          change ((stage z m).getD (ref (left j)) false ||
            ((stage z m).getD (ref (right j)) false || false)) = _
          simpa only [List.getD_eq_getElem?_getD, Bool.or_false] using congrArg₂ (· || ·) l r
        · simp only [gate, h, if_true]
          change ((stage z m).getD (ref (left j)) false &&
            ((stage z m).getD (ref (right j)) false && true)) = _
          simpa only [List.getD_eq_getElem?_getD, Bool.and_true] using congrArg₂ (· && ·) l r
  let f (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have coEval (z : Fin 8 → Bool) : circuitFun 9 D (Fin.cons false z) = f (Fin.cons false z) := by
    have all (x : Fin 9 → Bool) : value x out = f x := by
      rw [agree x]
      simp [f, Bool.or_assoc]
    change (tail.foldl step (step (List.ofFn (Fin.cons false z : Fin 9 → Bool)) beginGate)).getD
      (if out = 9 then 0 else out) false = _
    rw [beginAt]
    change (tail.foldl step (start z)).getD (if out = 9 then 0 else out) false = _
    have tailLen : tail.length = k := by simp [tail]
    rw [← show stage z k = tail.foldl step (start z) by
      simp only [stage, List.take_of_length_le (by omega : tail.length ≤ k)]]
    rw [← all]
    by_cases h : out = 9
    · rw [if_pos h, h, zero]
      rw [sound z k le_rfl 0 (by omega) (by decide)]
      exact inputs _ 0
    · simp only [if_neg h]
      exact sound z k le_rfl out outBound h
  have nonconstant : ∃ x y : Fin 8 → Bool,
      circuitFun 9 D (Fin.cons false x) ≠ circuitFun 9 D (Fin.cons false y) := by
    refine ⟨fun _ => false, ![true,true,false,false,false,false,false,false], ?_⟩
    rw [coEval, coEval]
    decide
  have size : D.size ≤ 15 := by
    change (beginGate :: tail).length ≤ 15
    simp [tail]
    omega
  have small := erase D legal first size (Or.inl three) nonconstant
  rw [show (fun z => circuitFun 9 D (Fin.cons false z : Fin 9 → Bool)) = (fun z => f (Fin.cons false z)) from funext coEval] at small
  exact cofactor small
