import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Essential

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_congr_except (a b : List Bool) (i : ℕ) (g : Gate)
    (hlen : a.length = b.length)
    (hagree : ∀ j, j ≠ i → a.getD j false = b.getD j false)
    (hunread : i ∉ g.inputs) :
    ∀ j, j ≠ i → (step a g).getD j false = (step b g).getD j false := by
  have hgate : g.inputs.map (fun j => a.getD j false) =
      g.inputs.map (fun j => b.getD j false) := by
    apply List.map_congr_left
    intro j hj
    exact hagree j (fun eq => hunread (eq ▸ hj))
  intro j hj
  unfold step
  rw [hgate]
  by_cases h : j < a.length
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append, h,
      show j < b.length by omega, ite_true] using hagree j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma run_congr_except (gs : List Gate) (a b : List Bool) (i : ℕ)
    (hlen : a.length = b.length)
    (hagree : ∀ j, j ≠ i → a.getD j false = b.getD j false)
    (hunread : ∀ g ∈ gs, i ∉ g.inputs) :
    ∀ j, j ≠ i → (gs.foldl step a).getD j false =
      (gs.foldl step b).getD j false := by
  induction gs generalizing a b with
  | nil => exact hagree
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [step, hlen]
    · exact step_congr_except a b i g hlen hagree (hunread g (by simp))
    · intro g' hg'
      exact hunread g' (by simp [hg'])

lemma input_unread (n : ℕ) (C : Circuit) (i : Fin n)
    (output : C.output ≠ i.val)
    (unread : i.val ∉ C.gates.flatMap Gate.inputs)
    (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  apply run_congr_except C.gates (List.ofFn x) (List.ofFn y) i.val
      (by simp) ?_ ?_ C.output output
  · intro j hj
    by_cases h : j < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [h, dite_true, Option.getD_some]
      apply same
      intro eq
      exact hj (congrArg Fin.val eq)
    · simp [List.getD_eq_getElem?_getD, h]
  · intro g hg hi
    exact unread (List.mem_flatMap.mpr ⟨g, hg, hi⟩)

lemma input_count_pos (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (correct : ∀ x, C.eval (List.ofFn x) = f x)
    (i : Fin n) (output : C.output ≠ i.val)
    (essential : ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y) :
    1 ≤ (C.gates.flatMap Gate.inputs).count i.val := by
  obtain ⟨x, y, same, different⟩ := essential
  have occurs : i.val ∈ C.gates.flatMap Gate.inputs := by
    by_contra absent
    have eq := input_unread n C i output absent x y same
    rw [correct, correct] at eq
    exact different eq
  exact List.count_pos_iff.mpr occurs

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (step w g) (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append, hi]

lemma eval_input_output (n : ℕ) (C : Circuit) (i : Fin n)
    (output : C.output = i.val) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = x i := by
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = x i
  rw [output, run_input C.gates (List.ofFn x) i.val (by simp)]
  simp

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 := ⟨(i.val + 5) % 10, Nat.mod_lt _ (by decide)⟩

def singleton (i : Fin 10) (j : Fin 10) : Bool := decide (j = i)

def pair (i : Fin 10) (j : Fin 10) : Bool := decide (j = neighbor i ∨ j = i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma input_witnesses : ∀ i : Fin 10,
    target (singleton i) = false ∧
    target (singleton (neighbor i)) = false ∧ target (pair i) = true ∧
    (∀ j : Fin 10, j ≠ i → singleton (neighbor i) j = pair i j) := by
  decide +kernel

lemma petersen_output_ne (C : Circuit)
    (correct : ∀ x, C.eval (List.ofFn x) = target x) (i : Fin 10) :
    C.output ≠ i.val := by
  intro eq
  have h := eval_input_output 10 C i eq (singleton i)
  rw [correct, (input_witnesses i).1] at h
  simp [singleton] at h

lemma petersen_input_count_pos (C : Circuit)
    (correct : ∀ x, C.eval (List.ofFn x) = target x) (i : Fin 10) :
    1 ≤ (C.gates.flatMap Gate.inputs).count i.val := by
  apply input_count_pos 10 target C correct i (petersen_output_ne C correct i)
  refine ⟨singleton (neighbor i), pair i, (input_witnesses i).2.2.2, ?_⟩
  rw [(input_witnesses i).2.1, (input_witnesses i).2.2.1]
  decide

end PEqualNP.Outside.L_meta_2590_aux.Essential

namespace PEqualNP.Outside.L_meta_2590_aux.Compress

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.Essential

lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

lemma inputs_update (x : Fin 10 → Bool) (b : Bool) :
    ∀ j, j ≠ 0 → (List.ofFn x).getD j false =
      (List.ofFn (Function.update x 0 b)).getD j false := by
  intro j hj
  by_cases bound : j < 10
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, bound, dite_true,
      Option.getD_some]
    rw [Function.update_of_ne (by intro eq; exact hj (congrArg Fin.val eq))]
  · simp [List.getD_eq_getElem?_getD, bound]

lemma patched_single_eval (before after : List Gate) (g : Gate) (out : ℕ)
    (unread : ∀ h ∈ before ++ after, 0 ∉ h.inputs) (outne : out ≠ 0)
    (x : Fin 10 → Bool) :
    let bit := g.op.eval (g.inputs.map fun j => (before.foldl step (List.ofFn x)).getD j false)
    (⟨before ++ g :: after, out⟩ : Circuit).eval (List.ofFn x) =
      (⟨before ++ ⟨.or, [0]⟩ :: after, out⟩ : Circuit).eval
        (List.ofFn (Function.update x 0 bit)) := by
  let a := before.foldl step (List.ofFn x)
  let bit := g.op.eval (g.inputs.map fun j => a.getD j false)
  let y := Function.update x 0 bit
  let b := before.foldl step (List.ofFn y)
  have hlen : a.length = b.length := by simp [a, b, run_length]
  have same : ∀ j, j ≠ 0 → a.getD j false = b.getD j false :=
    run_congr_except before (List.ofFn x) (List.ofFn y) 0 (by simp)
      (inputs_update x bit) (fun h hh => unread h (List.mem_append_left _ hh))
  have bzero : b.getD 0 false = bit := by
    unfold b
    rw [run_input before (List.ofFn y) 0 (by simp)]
    simp [y]
  have copied : GateOp.or.eval (([0] : List ℕ).map fun j => b.getD j false) = bit := by
    change b.getD 0 false || false = bit
    rw [bzero]
    simp
  have same_step : ∀ j, j ≠ 0 → (step a g).getD j false =
      (step b ⟨.or, [0]⟩).getD j false := by
    intro j hj
    change (a ++ [bit]).getD j false =
      (b ++ [GateOp.or.eval (([0] : List ℕ).map fun j => b.getD j false)]).getD j false
    rw [copied]
    by_cases bound : j < a.length
    · rw [List.getD_append _ _ _ _ bound,
        List.getD_append _ _ _ _ (by omega)]
      exact same j hj
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen]
  have tail := run_congr_except after (step a g) (step b ⟨.or, [0]⟩) 0
    (by simp [step, hlen]) same_step
    (fun h hh => unread h (List.mem_append_right _ hh)) out outne
  simpa only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    a, b, y, bit, step] using tail

end PEqualNP.Outside.L_meta_2590_aux.Compress
