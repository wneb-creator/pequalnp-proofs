import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_6583_317
  (both : ∀ (C : Circuit) (a b : Fin 28), FanInTwo C → C.size = 18 →
    15 ≤ C.gates.countP (fun g => !g.op.eval [false]) →
    let W := fun (x : Fin 10 → Bool) (i : Fin 28) => (C.wires (List.ofFn x)).getD i false
    let sensitive := fun i => ∀ v : Fin 10, ∃ m ∈ ([116,201,402,554,773] : List ℕ),
      let x := fun u : Fin 10 => m.testBit u.val
      W x i = false ∧ W (Function.update x v true) i = true
    let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
    (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    sensitive a → sensitive b → (∀ x, (W x a && W x b) = F x) → False)
  (one : ∀ (C : Circuit) (a b : Fin 28), FanInTwo C → C.size = 18 →
    15 ≤ C.gates.countP (fun g => !g.op.eval [false]) →
    let W := fun (x : Fin 10 → Bool) (i : Fin 28) => (C.wires (List.ofFn x)).getD i false
    let sensitive := fun i => ∀ v : Fin 10, ∃ m ∈ ([116,201,402,554,773] : List ℕ),
      let x := fun u : Fin 10 => m.testBit u.val
      W x i = false ∧ W (Function.update x v true) i = true
    let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
    (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    sensitive a → ¬ sensitive b → (∀ x, (W x a && W x b) = F x) → False) : (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (28 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (18 : ℕ) →       (15 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) x2.gates →         have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8)).getD x9 Bool.false;         (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 ↑x3 = Bool.true ∧ x8 x9 ↑x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 ↑x3 = Bool.false ∧ x8 x10 ↑x4 = Bool.true) → ¬∀ (x11 : Fin (10 : ℕ) → Bool), (x8 x11 ↑x3 && x8 x11 ↑x4) = x1 x11) := by

  classical
  let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  intro _ C a b hfan hsize hcount
  let W := fun (x : Fin 10 → Bool) (i : Fin 28) => (C.wires (List.ofFn x)).getD i false
  intro _ ab ba computes
  let S := fun i => ∀ v : Fin 10, ∃ m ∈ ([116,201,402,554,773] : List ℕ),
      let x := fun u : Fin 10 => m.testBit u.val
      W x i = false ∧ W (Function.update x v true) i = true
  have eqn : ∀ x, (W x a && W x b) = F x := computes
  have oneFull : S a ∨ S b := by
    apply Classical.byContradiction
    intro neither
    obtain ⟨i,hi⟩ := Classical.not_forall.mp (fun h : S a => neither (Or.inl h))
    obtain ⟨j,hj⟩ := Classical.not_forall.mp (fun h : S b => neither (Or.inr h))
    let row := fun (m : ℕ) (v : Fin 10) => m.testBit v.val
    have census : ∀ i j : Fin 10, ∃ m ∈ ([116,201,402,554,773] : List ℕ),
        F (row m) = false ∧ F (Function.update (row m) i true) = true ∧
          F (Function.update (row m) j true) = true := by
      decide +kernel
    obtain ⟨m,hm,hn,pi,pj⟩ := census i j
    have hitI := Bool.and_eq_true_iff.mp ((eqn _).trans pi)
    have hitJ := Bool.and_eq_true_iff.mp ((eqn _).trans pj)
    have ha : W (row m) a = true := Bool.eq_true_of_not_eq_false (fun h => hi ⟨m,hm,h,hitI.1⟩)
    have hb : W (row m) b = true := Bool.eq_true_of_not_eq_false (fun h => hj ⟨m,hm,h,hitJ.2⟩)
    exact Bool.noConfusion ((Bool.and_eq_true_iff.mpr ⟨ha,hb⟩).symm.trans ((eqn _).trans hn))
  by_cases ha : S a
  · by_cases hb : S b
    · exact both C a b hfan hsize hcount ab ba ha hb eqn
    · exact one C a b hfan hsize hcount ab ba ha hb eqn
  · have hb := oneFull.resolve_left ha
    have swapped : ∀ x, (W x b && W x a) = F x := fun x => (Bool.and_comm _ _).trans (eqn x)
    obtain ⟨x,hx,hy⟩ := ba
    obtain ⟨y,hy1,hy2⟩ := ab
    exact one C b a hfan hsize hcount ⟨x,hy,hx⟩ ⟨y,hy2,hy1⟩ hb ha swapped
