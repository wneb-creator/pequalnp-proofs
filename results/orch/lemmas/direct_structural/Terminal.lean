import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runPrefix (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma runPrefix_extends (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, runPrefix gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [runPrefix], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change runPrefix gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]
    simp

lemma runPrefix_length (gs : List Gate) (w : List Bool) :
    (runPrefix gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := runPrefix_extends gs w
  simp [ht, hl]

lemma runPrefix_getD (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (runPrefix gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := runPrefix_extends gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma terminal_normalize (n : ℕ) (C : Circuit) (legal : FanInTwo C)
    (nonzero : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (noninput : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
      0 < D.size ∧ D.output = n + D.size - 1 := by
  have low : n ≤ C.output := by
    by_contra h
    have hi : C.output < n := by omega
    obtain ⟨x, hx⟩ := noninput ⟨C.output, hi⟩
    apply hx
    change (runPrefix C.gates (List.ofFn x)).getD C.output false = _
    rw [runPrefix_getD _ _ _ (by simpa using hi)]
    simp [hi]
  have high : C.output < n + C.size := by
    obtain ⟨x, hx⟩ := nonzero
    by_contra h
    have ge : (C.wires (List.ofFn x)).length ≤ C.output := by
      change (runPrefix C.gates (List.ofFn x)).length ≤ C.output
      rw [runPrefix_length]
      simpa [Circuit.size] using h
    change (C.wires (List.ofFn x)).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ ge] at hx
    cases hx
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by change k ≤ C.size; dsimp [k]; omega
  have hpos : 0 < k := by dsimp [k]; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have sizeD : D.size = k := by simp [D, Circuit.size, Nat.min_eq_left hk]
  refine ⟨D, ?_, by omega, ?_, by omega, ?_⟩
  · intro g hg
    exact legal g (List.mem_of_mem_take hg)
  · funext x
    change (runPrefix (C.gates.take k) (List.ofFn x)).getD C.output false =
      (runPrefix C.gates (List.ofFn x)).getD C.output false
    have decomp : runPrefix C.gates (List.ofFn x) =
        runPrefix (C.gates.drop k) (runPrefix (C.gates.take k) (List.ofFn x)) := by
      simp only [runPrefix, ← List.foldl_append, List.take_append_drop]
    rw [decomp]
    symm
    apply runPrefix_getD
    rw [runPrefix_length]
    simp only [List.length_ofFn, List.length_take]
    rw [Nat.min_eq_left hk]
    dsimp [k]
    omega
  · change C.output = n + D.size - 1
    rw [sizeD]
    dsimp [k]
    omega

def deletedPetersen (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

lemma deletedPetersen_singleton : ∀ i : Fin 9,
    deletedPetersen (fun j => decide (j = i)) = false := by
  decide +kernel

lemma deletedPetersen_terminal (s : ℕ) (h : HasCircuitSize 9 deletedPetersen s) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ s ∧ circuitFun 9 D = deletedPetersen ∧
      0 < D.size ∧ D.output = 9 + D.size - 1 := by
  obtain ⟨C, legal, small, computes⟩ := h
  have nonzero : ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) = true := by
    refine ⟨fun _ => true, ?_⟩
    rw [computes]
    rfl
  have noninput : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ x i := by
    intro i
    refine ⟨fun j => decide (j = i), ?_⟩
    rw [computes, deletedPetersen_singleton]
    simp
  obtain ⟨D, hD, hsize, hfun, hpos, hout⟩ := terminal_normalize 9 C legal nonzero noninput
  exact ⟨D, hD, le_trans hsize small, hfun.trans (funext computes), hpos, hout⟩

lemma terminal_singleton_eval (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    circuitFun n ⟨gs ++ [g], n + gs.length⟩ x =
      g.op.eval (g.inputs.map fun i => (runPrefix gs (List.ofFn x)).getD i false) := by
  have hlen : (runPrefix gs (List.ofFn x)).length = n + gs.length := by
    simp [runPrefix_length]
  change (runPrefix (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = _
  simp only [runPrefix, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((runPrefix gs (List.ofFn x)) ++
    [g.op.eval (g.inputs.map fun i => (runPrefix gs (List.ofFn x)).getD i false)]).getD
    (n + gs.length) false = _
  rw [← hlen]
  simp [runPrefix]

lemma terminal_copy_not_minimal (n : ℕ) (gs : List Gate) (a : ℕ) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ¬ IsMinimalCircuit n ⟨gs ++ [⟨op, [a]⟩], n + gs.length⟩ := by
  intro h
  let D : Circuit := ⟨gs, a⟩
  have hD : FanInTwo D := by
    intro g hg
    exact h.1 g (List.mem_append_left _ hg)
  have heq : circuitFun n D = circuitFun n ⟨gs ++ [⟨op, [a]⟩], n + gs.length⟩ := by
    funext x
    rw [terminal_singleton_eval]
    rcases hop with rfl | rfl <;> simp [D, circuitFun, Circuit.eval, Circuit.wires,
      GateOp.eval, runPrefix]
  have impossible := h.2 D hD heq
  simp [D, Circuit.size] at impossible

lemma terminal_duplicate_not_minimal (n : ℕ) (gs : List Gate) (a : ℕ) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ¬ IsMinimalCircuit n ⟨gs ++ [⟨op, [a, a]⟩], n + gs.length⟩ := by
  intro h
  let D : Circuit := ⟨gs, a⟩
  have hD : FanInTwo D := by
    intro g hg
    exact h.1 g (List.mem_append_left _ hg)
  have heq : circuitFun n D = circuitFun n ⟨gs ++ [⟨op, [a, a]⟩], n + gs.length⟩ := by
    funext x
    rw [terminal_singleton_eval]
    rcases hop with rfl | rfl <;> simp [D, circuitFun, Circuit.eval, Circuit.wires,
      GateOp.eval, runPrefix]
  have impossible := h.2 D hD heq
  simp [D, Circuit.size] at impossible

lemma terminal_empty_not_target (gs : List Gate) (op : GateOp) :
    circuitFun 9 ⟨gs ++ [⟨op, []⟩], 9 + gs.length⟩ ≠ deletedPetersen := by
  intro h
  have hon := congrFun h (fun _ => true)
  have hoff := congrFun h (fun _ => false)
  rw [terminal_singleton_eval] at hon hoff
  simp only [List.map_nil] at hon hoff
  have contradiction := hon.symm.trans hoff
  change true = false at contradiction
  cases contradiction

lemma exists_minimal (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f s) :
    ∃ C : Circuit, IsMinimalCircuit n C ∧ C.size ≤ s ∧ circuitFun n C = f := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit, FanInTwo C ∧ circuitFun n C = f ∧ C.size = k := by
    obtain ⟨C, hC, _, hf⟩ := h
    exact ⟨C.size, C, hC, funext hf, rfl⟩
  obtain ⟨C, hC, hf, hk⟩ := Nat.find_spec hex
  have minimal : IsMinimalCircuit n C := by
    refine ⟨hC, ?_⟩
    intro D hD heq
    rw [hk]
    exact Nat.find_min' hex ⟨D, hD, heq.trans hf, rfl⟩
  obtain ⟨D, hD, hs, hDf⟩ := h
  have lower : C.size ≤ D.size := minimal.2 D hD ((funext hDf).trans hf.symm)
  exact ⟨C, minimal, le_trans lower hs, hf⟩

end PEqualNP.Outside.L_meta_670
