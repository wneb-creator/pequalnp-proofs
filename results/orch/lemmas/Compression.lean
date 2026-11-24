import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact fold_length C.gates x

lemma wires_append (C : Circuit) (g : Gate) (x : List Bool) :
    (Circuit.mk (C.gates ++ [g]) 0).wires x =
      C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

def Represents (m : ℕ) (C : Circuit) (f : (Fin m → Bool) → Bool) : Prop :=
  ∃ i : ℕ, ∀ y : Fin m → Bool, (C.wires (List.ofFn y)).getD i false = f y

lemma represents_false (m : ℕ) (C : Circuit) :
    Represents m C (fun _ => false) := by
  refine ⟨m + C.size, ?_⟩
  intro y
  apply List.getD_eq_default
  simp [wires_length]

lemma represents_append (m : ℕ) (C : Circuit) (g : Gate)
    (f : (Fin m → Bool) → Bool) (h : Represents m C f) :
    Represents m (Circuit.mk (C.gates ++ [g]) 0) f := by
  obtain ⟨i, hi⟩ := h
  by_cases small : i < m + C.size
  · refine ⟨i, ?_⟩
    intro y
    rw [wires_append]
    rw [List.getD_append]
    · exact hi y
    · simpa [wires_length] using small
  · have eqfalse : f = fun _ => false := by
      funext y
      rw [← hi y]
      apply List.getD_eq_default
      simpa [wires_length] using Nat.le_of_not_gt small
    rw [eqfalse]
    exact represents_false m _

lemma append_gate_representation (m : ℕ) (C : Circuit) (g : Gate) :
    Represents m (Circuit.mk (C.gates ++ [g]) 0)
      (fun y : Fin m → Bool =>
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false)) := by
  refine ⟨m + C.size, ?_⟩
  intro y
  rw [wires_append]
  have hl : (C.wires (List.ofFn y)).length = m + C.size := by simp [wires_length]
  rw [← hl]
  simp

lemma append_legal (C : Circuit) (g : Gate) (hc : FanInTwo C)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    FanInTwo (Circuit.mk (C.gates ++ [g]) 0) := by
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hc q hq
  · exact hg

end PEqualNP.Outside.L_meta_3821_aux.Compression
