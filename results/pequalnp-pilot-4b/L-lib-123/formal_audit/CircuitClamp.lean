import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_123_Audit

open PEqualNP.MetaComplexity

def circuitStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def clampGate (bound : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨g.op, min g.left bound, min g.right bound⟩

def clampCircuit (d : ℕ) (C : BinaryCircuit) : BinaryCircuit :=
  ⟨C.gates.map (clampGate (d + C.size)), min C.output (d + C.size)⟩

lemma getD_min_bound (w : List Bool) (bound i : ℕ) (hlen : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [min_eq_left hi]
  · have hbi : bound ≤ i := by omega
    rw [min_eq_right hbi, List.getD_eq_default w false hlen,
      List.getD_eq_default w false (hlen.trans hbi)]

lemma circuit_fold_length (gs : List BinaryGate) (w : List Bool) :
    (gs.foldl circuitStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, circuitStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma circuit_fold_clamp (gs : List BinaryGate) (w : List Bool) (bound : ℕ)
    (hlen : w.length + gs.length ≤ bound) :
    (gs.map (clampGate bound)).foldl circuitStep w = gs.foldl circuitStep w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw : w.length ≤ bound := by simp only [List.length_cons] at hlen; omega
    have hs : circuitStep w (clampGate bound g) = circuitStep w g := by
      simp only [circuitStep, clampGate]
      rw [getD_min_bound w bound g.left hw, getD_min_bound w bound g.right hw]
    simp only [List.map_cons, List.foldl_cons]
    rw [hs]
    apply ih
    simpa [circuitStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen

lemma clampCircuit_size (C : BinaryCircuit) (d : ℕ) :
    (clampCircuit d C).size = C.size := by
  simp [clampCircuit, BinaryCircuit.size]

lemma clampCircuit_wires (C : BinaryCircuit) (d : ℕ) (x : List Bool)
    (hx : x.length = d) :
    (clampCircuit d C).wires x = C.wires x := by
  change (C.gates.map (clampGate (d + C.size))).foldl circuitStep x =
    C.gates.foldl circuitStep x
  apply circuit_fold_clamp
  simp [hx, BinaryCircuit.size]

lemma clampCircuit_eval (C : BinaryCircuit) (d : ℕ) (x : List Bool)
    (hx : x.length = d) :
    (clampCircuit d C).eval x = C.eval x := by
  unfold BinaryCircuit.eval
  rw [clampCircuit_wires C d x hx]
  change (C.wires x).getD (min C.output (d + C.size)) false =
    (C.wires x).getD C.output false
  apply getD_min_bound
  change (C.gates.foldl circuitStep x).length ≤ d + C.size
  rw [circuit_fold_length, hx]
  rfl

lemma clampCircuit_indices (C : BinaryCircuit) (d : ℕ) :
    (clampCircuit d C).output ≤ d + C.size ∧
    ∀ g ∈ (clampCircuit d C).gates,
      g.left ≤ d + C.size ∧ g.right ≤ d + C.size := by
  constructor
  · exact min_le_right _ _
  · intro g hg
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    exact ⟨min_le_right _ _, min_le_right _ _⟩

end PEqualNP.Outside.L_lib_123_Audit
