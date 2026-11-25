import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4245_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def wire {n : ℕ} (q : ℕ) (inputs : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then inputs ⟨i, h⟩ else q + (i - n)

lemma wire_lt {n q : ℕ} {inputs : Fin n → ℕ} (hinputs : ∀ a, inputs a < q)
    (i t : ℕ) (hi : i < n + t) : wire q inputs i < q + t := by
  unfold wire
  split
  · have h := hinputs ⟨i, ‹i < n›⟩
    omega
  · omega

def rewire (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) values

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma run_rewire {n q : ℕ} {inputs : Fin n → ℕ} (hinputs : ∀ a, inputs a < q)
    (gs : List Gate) (t : ℕ) (old fresh : List Bool)
    (hold : old.length = n + t) (hfresh : fresh.length = q + t)
    (hread : ∀ i, fresh.getD (wire q inputs i) false = old.getD i false) :
    ∀ i, (run (gs.map (rewire (wire q inputs))) fresh).getD (wire q inputs i) false =
      (run gs old).getD i false := by
  induction gs generalizing t old fresh with
  | nil => exact hread
  | cons g gs ih =>
    simp only [List.map_cons, run_cons]
    apply ih (t + 1)
    · simp [hold, Nat.add_assoc]
    · simp [hfresh, Nat.add_assoc]
    · intro i
      by_cases hi : i < n + t
      · rw [List.getD_append _ _ _ _ (by rw [hfresh]; exact wire_lt hinputs i t hi),
            List.getD_append _ _ _ _ (by omega)]
        exact hread i
      · have hi' : ¬ i < n := by omega
        have hoff : wire q inputs i - fresh.length = i - old.length := by
          rw [wire, dite_eq_right hi']
          omega
        have hnew : fresh.length ≤ wire q inputs i := by
          rw [wire, dite_eq_right hi']
          omega
        rw [List.getD_append_right _ _ _ _ hnew,
            List.getD_append_right _ _ _ _ (by omega), hoff]
        have hgate : (rewire (wire q inputs) g).op.eval
              ((rewire (wire q inputs) g).inputs.map fun j => fresh.getD j false) =
            g.op.eval (g.inputs.map fun j => old.getD j false) := by
          simp only [rewire, List.map_map]
          congr 1
          exact List.map_congr_left (fun j _ => hread j)
        rw [hgate]

lemma input_value {n : ℕ} (x : Fin n → Bool) (a : Fin n) :
    (List.ofFn x).getD a.val false = x a := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma substitute_or (n m : ℕ) (pos : Fin n) (a b : Fin m)
    (source : Fin n → Fin m) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack m D ∧ D.size ≤ C.size + 1 ∧
      ∀ x : Fin m → Bool, circuitFun m D x =
        circuitFun n C (fun i => if i = pos then x a || x b else x (source i)) := by
  let inputs : Fin n → ℕ := fun i => if i = pos then m else (source i).val
  have hinputs : ∀ i, inputs i < m + 1 := by
    intro i
    dsimp [inputs]
    split <;> have h := (source i).isLt <;> omega
  let f := wire (m + 1) inputs
  let headGate : Gate := ⟨GateOp.or, [a.val, b.val]⟩
  let D : Circuit := ⟨headGate :: C.gates.map (rewire f), f C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ headGate :: C.gates.map (rewire f) at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [headGate]
    · obtain ⟨original, hmem, heq⟩ := List.mem_map.mp hg
      rw [← heq]
      simpa [rewire] using mono original hmem
  · intro j hj i hi
    cases j with
    | zero =>
      change i ∈ [a.val, b.val] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simp
      · simp
    | succ j =>
      have hj' : j < C.gates.length := by simpa [D] using hj
      have hgate : gateAt D (j + 1) = rewire f (gateAt C j) := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']
        simp [D]
      rw [hgate] at hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      have h := wire_lt hinputs k j (back j hj' k hk)
      change f k < m + (j + 1)
      dsimp [f]
      omega
  · simp [D, Circuit.size]
  · intro x
    let y : Fin n → Bool := fun i => if i = pos then x a || x b else x (source i)
    let fresh := List.ofFn x ++ [x a || x b]
    have hread : ∀ i, fresh.getD (f i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < n
      · let j : Fin n := ⟨i, hi⟩
        change fresh.getD (wire (m + 1) inputs i) false = (List.ofFn y).getD j.val false
        rw [wire, dite_eq_left hi, input_value]
        change fresh.getD (inputs j) false = y j
        by_cases hj : j = pos
        · simp only [inputs, y, ite_eq_left hj, fresh]
          rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
          rfl
        · simp only [inputs, y, ite_eq_right hj, fresh]
          rw [List.getD_append _ _ _ _ (by simp), input_value]
      · change fresh.getD (wire (m + 1) inputs i) false = (List.ofFn y).getD i false
        rw [wire, dite_eq_right hi]
        rw [List.getD_eq_default _ _ (by simp [fresh]),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    have hseed : headGate.op.eval (headGate.inputs.map fun i => (List.ofFn x).getD i false) =
        (x a || x b) := by simp [headGate, GateOp.eval]
    have hev := run_rewire hinputs C.gates 0 (List.ofFn y) fresh (by simp)
      (by simp [fresh]) hread C.output
    change (run (headGate :: C.gates.map (rewire f)) (List.ofFn x)).getD (f C.output) false =
      (run C.gates (List.ofFn y)).getD C.output false
    rw [run_cons, hseed]
    exact hev

end PEqualNP.Outside.L_meta_4245_aux

theorem PEqualNP.Outside.L_meta_4245 : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12) :=
  PEqualNP.Outside.L_meta_4245_aux.substitute_or
