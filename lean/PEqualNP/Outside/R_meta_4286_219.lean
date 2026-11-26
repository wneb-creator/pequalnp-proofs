import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- An early conjunction can replace the final gate and give a forbidden 14-gate circuit.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4286_219
    (fourteen : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (early : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       ∀ (x4 : ℕ),         have x5 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x5 : Fin (9 : ℕ) → Bool) (x6 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))])).getD x6 Bool.false;         have x6 : (Fin (9 : ℕ) → Bool) → Bool := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ));         (∀ (x7 : Fin (9 : ℕ) → Bool), x6 x7 = Bool.true → x5 x7 x4 = Bool.true) → (∃ (x8 : Fin (9 : ℕ) → Bool), x5 x8 x4 = Bool.false) → (12 : ℕ) ≤ x4)
    (last : ∀ (gs : List Gate) (a : ℕ), gs.length = 13 →
      FanInTwo ⟨gs, 0⟩ → gs.countP (fun g => g.op.eval [false]) = 1 →
      12 ≤ a → a < 22 →
      let w := fun (x : Fin 9 → Bool) (i : ℕ) =>
        ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
      let f := fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      (∃ x, w x a = true ∧ w x 22 = false) →
      (∃ x, w x a = false ∧ w x 22 = true) →
      ∃ x, (w x a && w x 22) ≠ f x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (1 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro gs a b lengthGs legal one amin ab bmax
  let f (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wire (x : Fin 9 → Bool) (i : ℕ) := (gs.foldl step (init x)).getD i false
  change ∃ x, (wire x a && wire x b) ≠ f x
  by_contra! agreement
  have forbid : ¬ HasCircuitSize 9 f 14 := by
    convert fourteen using 2
    funext x
    simp [f, List.any_cons, Bool.or_assoc] <;> rfl
  let pre : Gate := ⟨.or, [0,3]⟩
  have preEval (x : Fin 9 → Bool) : step (List.ofFn x) pre = init x := by
    change List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 3 false || false)] = _
    simp [init, List.getD_eq_getElem?_getD]
  have preLegal : pre.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      pre.inputs.length ≤ 2 := by simp [pre]
  have cannot (i : ℕ) : ∃ x, wire x i ≠ f x := by
    by_contra! agrees
    apply forbid
    refine ⟨⟨pre :: gs, i⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact preLegal
      · exact legal g hg
    · change (pre :: gs).length ≤ 14
      simp [lengthGs]
    · intro x
      change (gs.foldl step (step (List.ofFn x) pre)).getD i false = f x
      rw [preEval]
      exact agrees x
  have late : b = 22 := by
    by_contra hb
    have bsmall : b < 22 := by omega
    let firstGates := gs.take 12
    let finish : Gate := ⟨.and, [a,b]⟩
    have firstGatesLen : firstGates.length = 12 := by simp [firstGates, lengthGs]
    have listLen (q : List Gate) (w : List Bool) :
        (q.foldl step w).length = w.length + q.length := by
      induction q generalizing w with
      | nil => simp
      | cons g q hq =>
        rw [List.foldl_cons, hq]
        simp [step]
        omega
    have keep (q : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (q.foldl step w).getD i false = w.getD i false := by
      induction q generalizing w with
      | nil => rfl
      | cons g q hq =>
        rw [List.foldl_cons, hq _ (by simp [step]; omega)]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have afterPrefix (x : Fin 9 → Bool) : (firstGates.foldl step (init x)).length = 22 := by
      rw [listLen, firstGatesLen]
      simp [init]
    have recover (x : Fin 9 → Bool) (i : ℕ) (hi : i < 22) :
        (firstGates.foldl step (init x)).getD i false = wire x i := by
      change _ = (gs.foldl step (init x)).getD i false
      have split : firstGates ++ gs.drop 12 = gs := List.take_append_drop 12 gs
      symm
      calc
        (gs.foldl step (init x)).getD i false =
            ((firstGates ++ gs.drop 12).foldl step (init x)).getD i false :=
          congrArg (fun q : List Gate => (q.foldl step (init x)).getD i false) split.symm
        _ = (firstGates.foldl step (init x)).getD i false := by
          rw [List.foldl_append]
          exact keep _ _ _ (by simpa only [afterPrefix] using hi)
    apply forbid
    refine ⟨⟨pre :: (firstGates ++ [finish]), 22⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact preLegal
      · rcases List.mem_append.mp hg with hp | hf
        · exact legal g (List.mem_of_mem_take hp)
        · obtain rfl := List.mem_singleton.mp hf
          simp [finish]
    · change (pre :: (firstGates ++ [finish])).length ≤ 14
      simp [firstGatesLen]
    · intro x
      change ((firstGates ++ [finish]).foldl step (step (List.ofFn x) pre)).getD 22 false =
        f x
      rw [preEval, List.foldl_append]
      let before := firstGates.foldl step (init x)
      change (before ++ [before.getD a false && (before.getD b false && true)]).getD 22 false = f x
      have sizeBefore : before.length = 22 := afterPrefix x
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), sizeBefore]
      change (before.getD a false && (before.getD b false && true)) = f x
      rw [Bool.and_true]
      exact congrArg₂ (· && ·) (recover x a (by omega)) (recover x b bsmall) |>.trans (agreement x)
  subst b
  have leftOnly : ∃ x, wire x a = true ∧ wire x 22 = false := by
    rcases cannot a with ⟨x, hx⟩
    specialize agreement x
    exact ⟨x, by cases ha : wire x a <;> cases hb : wire x 22 <;> simp_all⟩
  have rightOnly : ∃ x, wire x a = false ∧ wire x 22 = true := by
    rcases cannot 22 with ⟨x, hx⟩
    specialize agreement x
    exact ⟨x, by cases ha : wire x a <;> cases hb : wire x 22 <;> simp_all⟩
  have lt : a < 22 := by
    obtain ⟨x, h, e⟩ := leftOnly
    by_contra! ge
    have ha : a = 22 := by omega
    rw [ha, e] at h
    contradiction
  have cover (x : Fin 9 → Bool) (hit : f x = true) : wire x a = true := by
    have eq := (agreement x).trans hit
    exact (Bool.and_eq_true_iff.mp eq).1
  have alo : 12 ≤ a := by
    obtain ⟨x,h,_⟩ := rightOnly
    exact early gs lengthGs legal a cover ⟨x,h⟩
  obtain ⟨x, bad⟩ := last gs a lengthGs legal one alo lt leftOnly rightOnly
  exact bad (agreement x)
