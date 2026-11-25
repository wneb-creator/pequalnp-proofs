import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotSamples

open PEqualNP.CircuitLowerBounds

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def bits (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def positiveRows : List ℕ :=
  [6,12,24,66,132,160,264,288,320,528,576,640,3,13,17,33,133,265,321,577,641]

def negativeRows : List ℕ :=
  [50,104,116,138,200,208,276,402,548,554,770,772,69,201,385,521,773]

def inputBelow (x y : Fin 10 → Bool) : Prop := ∀ i, x i = true → y i = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma boundary_covers : ∀ x : Fin 10 → Bool,
    (target x = true → ∃ m ∈ positiveRows, bits m 0 = x 0 ∧ inputBelow (bits m) x) ∧
    (target x = false → ∃ m ∈ negativeRows, bits m 0 = x 0 ∧ inputBelow x (bits m)) := by
  unfold inputBelow
  decide +kernel

lemma positiveRows_correct : ∀ m ∈ positiveRows, target (bits m) = true := by
  decide +kernel

lemma negativeRows_correct : ∀ m ∈ negativeRows, target (bits m) = false := by
  decide +kernel

lemma boundary_complete (F : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, x 0 = y 0 → inputBelow x y → F x = true → F y = true)
    (positive : ∀ m ∈ positiveRows, F (bits m) = true)
    (negative : ∀ m ∈ negativeRows, F (bits m) = false) :
    ∀ x, F x = target x := by
  intro x
  cases h : target x with
  | false =>
    obtain ⟨m, hm, h0, hle⟩ := (boundary_covers x).2 h
    cases hf : F x with
    | false => rfl
    | true =>
      have := mono x (bits m) h0.symm hle hf
      rw [negative m hm] at this
      contradiction
  | true =>
    obtain ⟨m, hm, h0, hle⟩ := (boundary_covers x).1 h
    exact mono (bits m) x h0 hle (positive m hm)

def above (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases hi : i < w.length
  · rw [ite_eq_right (Nat.ne_of_lt hi)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · by_cases he : i = w.length
    · simp [he]
    · rw [ite_eq_right he]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma above_snoc {w z : List Bool} {b c : Bool} (h : above w z)
    (hbc : b = true → c = true) : above (w ++ [b]) (z ++ [c]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [getD_snoc] at hi ⊢
  by_cases he : i = w.length
  · simpa [he, ← h.1] using hbc (by simpa [he] using hi)
  · simp only [he, ite_false] at hi
    simpa [← h.1, he] using h.2 i hi

lemma above_fold (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w z : List Bool, above w z →
      above (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w)
        (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) z) := by
  induction gs with
  | nil => intro w z h; exact h
  | cons g gs ih =>
    intro w z h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => legal g' (by simp [hg']))
    apply above_snoc h
    rcases legal g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro all b hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h.2 i (all _ ⟨i, hi, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hb⟩

lemma seed_above (x y : Fin 10 → Bool) (h0 : x 0 = y 0) (hxy : inputBelow x y) :
    above (List.ofFn x ++ [!x 0]) (List.ofFn y ++ [!y 0]) := by
  apply above_snoc
  · refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hlt : i < 10
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_eq_left,
        Option.getD_some] at hi ⊢
      exact hxy ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at hi
      contradiction
  · simp [h0]

lemma one_not_tail_mono (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 10 → Bool) (h0 : x 0 = y 0) (hxy : inputBelow x y) :
    C.eval (List.ofFn x ++ [!x 0]) = true →
      C.eval (List.ofFn y ++ [!y 0]) = true := by
  exact (above_fold C.gates legal _ _ (seed_above x y h0 hxy)).2 C.output

lemma one_not_tail_complete (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (positive : ∀ m ∈ positiveRows,
      C.eval (List.ofFn (bits m) ++ [!bits m 0]) = true)
    (negative : ∀ m ∈ negativeRows,
      C.eval (List.ofFn (bits m) ++ [!bits m 0]) = false) :
    ∀ x, C.eval (List.ofFn x ++ [!x 0]) = target x := by
  exact boundary_complete _ (one_not_tail_mono C legal) positive negative

lemma initial_not_eval (gs : List Gate) (out : ℕ) (x : Fin 10 → Bool) :
    Circuit.eval ⟨⟨GateOp.not, [0]⟩ :: gs, out⟩ (List.ofFn x) =
      Circuit.eval ⟨gs, out⟩ (List.ofFn x ++ [!x 0]) := by
  simp [Circuit.eval, Circuit.wires, GateOp.eval]

end PEqualNP.Outside.L_meta_2592_aux.OneNotSamples
