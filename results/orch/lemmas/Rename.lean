import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

def renameWire (n : ℕ) (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then p ⟨i, h⟩ else i

def renameGate (n : ℕ) (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n p)⟩

def renameCircuit (n : ℕ) (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate n p), renameWire n p C.output⟩

def wireRelated (n : ℕ) (p : Fin n → Fin n) (w v : List Bool) : Prop :=
  ∀ i : ℕ, v.getD (renameWire n p i) false = w.getD i false

lemma related_ofFn (n : ℕ) (p : Fin n → Fin n) (x : Fin n → Bool) :
    wireRelated n p (List.ofFn (fun i => x (p i))) (List.ofFn x) := by
  intro i
  by_cases hi : i < n
  · simp [renameWire, hi]
  · simp only [renameWire, hi, dite_false]
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

lemma related_append (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (hl : w.length = v.length) (hn : n ≤ w.length) (b : Bool) :
    wireRelated n p (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hj : renameWire n p i < v.length := by
      by_cases his : i < n
      · simp only [renameWire, his, dite_true]
        have := (p ⟨i, his⟩).isLt
        omega
      · simpa [renameWire, his, ← hl] using hi
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
    exact hr i
  · have his : ¬ i < n := by omega
    simp only [renameWire, his, dite_false]
    by_cases he : i = w.length
    · subst i
      calc
        (v ++ [b]).getD w.length false = b := by rw [hl]; simp
        _ = (w ++ [b]).getD w.length false := by simp
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma renamed_gate_value (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (g : Gate) :
    (renameGate n p g).op.eval ((renameGate n p g).inputs.map (fun i => v.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [renameGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hr i

lemma related_fold (n : ℕ) (p : Fin n → Fin n) (gs : List Gate) :
    ∀ w v : List Bool, wireRelated n p w v → w.length = v.length → n ≤ w.length →
    wireRelated n p
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (renameGate n p)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs with
  | nil => intro w v hr hl hn; exact hr
  | cons g gs ih =>
    intro w v hr hl hn
    simp only [List.map_cons, List.foldl_cons]
    rw [renamed_gate_value n p w v hr g]
    apply ih
    · exact related_append n p w v hr hl hn _
    · simpa using hl
    · simp only [List.length_append, List.length_singleton]
      omega

lemma renameCircuit_eval (n : ℕ) (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (renameCircuit n p C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (p i))) := by
  exact related_fold n p C.gates _ _ (related_ofFn n p x) (by simp) (by simp) C.output

lemma renameCircuit_size (n : ℕ) (p : Fin n → Fin n) (C : Circuit) :
    (renameCircuit n p C).size = C.size := by
  simp [renameCircuit, Circuit.size]

lemma renameCircuit_fanin (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (renameCircuit n p C) := by
  intro g hg
  change g ∈ C.gates.map (renameGate n p) at hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h q hq

lemma renameCircuit_has_not (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (renameCircuit n p C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := h
  exact ⟨renameGate n p g, List.mem_map.mpr ⟨g, hg, rfl⟩, hop⟩

end PEqualNP.Outside.L_meta_2592
