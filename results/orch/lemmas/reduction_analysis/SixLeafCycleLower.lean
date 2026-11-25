import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.L106

/- Research artifact: extra project imports are intentional. This proves a
lower bound for a twelve-input subgraph, not for the full L-meta-650 target. -/

namespace PEqualNP.Outside.L_meta_650.SixLeafCycle

open PEqualNP.MetaComplexity

def f12 (x : Fin 12 → Bool) : Bool :=
  (x 0 && (x 3 || x 4 || x 6 || x 9)) ||
  (x 1 && (x 3 || x 5 || x 7 || x 10)) ||
  (x 2 && (x 4 || x 5 || x 8 || x 11))

def f11 (x : Fin 11 → Bool) : Bool := f12 (Fin.snoc x false)
def f10 (x : Fin 10 → Bool) : Bool := f11 (Fin.snoc x false)
def f9 (x : Fin 9 → Bool) : Bool := f10 (Fin.snoc x false)
def f8 (x : Fin 8 → Bool) : Bool := f9 (Fin.snoc x false)
def f7 (x : Fin 7 → Bool) : Bool := f8 (Fin.snoc x false)
def f6 (x : Fin 6 → Bool) : Bool := f7 (Fin.snoc x false)

theorem no_thirteen : ¬ HasCircuitSize 12 f12 13 := by
  intro h
  have h11 : HasCircuitSize 11 f11 12 :=
    Helpers.gate_elim 11 f12 false 12
      (by refine ⟨fun i => decide (i.val = 2), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h
  have h10 : HasCircuitSize 10 f10 11 :=
    Helpers.gate_elim 10 f11 false 11
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h11
  have h9 : HasCircuitSize 9 f9 10 :=
    Helpers.gate_elim 9 f10 false 10
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h10
  have h8 : HasCircuitSize 8 f8 9 :=
    Helpers.gate_elim 8 f9 false 9
      (by refine ⟨fun i => decide (i.val = 2), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h9
  have h7 : HasCircuitSize 7 f7 8 :=
    Helpers.gate_elim 7 f8 false 8
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h8
  have h6 : HasCircuitSize 6 f6 7 :=
    Helpers.gate_elim 6 f7 false 7
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩; decide)
      h7
  let π : Fin 6 → Fin 6 := ![0, 2, 4, 1, 5, 3]
  have hc := Helpers.PermInputs.relabel_size π f6 7 h6
  have eq_cycle : (fun x : Fin 6 → Bool => f6 (x ∘ π)) =
      (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6,
        (i.val + 1) % 6 = j.val ∧ x i = true ∧ x j = true)) := by
    exact funext (by decide +kernel)
  rw [eq_cycle] at hc
  have := (PEqualNP.MetaComplexity.L106 6 7 (by decide)).mp hc
  omega

theorem lower (s : ℕ) (h : HasCircuitSize 12 f12 s) : 14 ≤ s := by
  by_contra hs
  obtain ⟨C, hC, hc, he⟩ := h
  exact no_thirteen ⟨C, hC, by omega, he⟩

/- Exact embedding into the seventeen-input six-row case. The twelve
essential inputs are 0, 2, 4, 7, 9, 11, 6, 15, 12, 13, 16, 14. -/
def threeRows (x : Fin 17 → Bool) : Bool :=
  (x 0 && (x 7 || x 9 || x 6 || x 13)) ||
  (x 2 && (x 7 || x 11 || x 15 || x 16)) ||
  (x 4 && (x 9 || x 11 || x 12 || x 14))

theorem three_rows_lower (s : ℕ) (h : HasCircuitSize 17 threeRows s) : 14 ≤ s := by
  let π : Fin 17 → Fin 12 := ![0, 0, 1, 0, 2, 0, 6, 3, 0, 4, 0, 5, 8, 9, 11, 7, 10]
  have hc := Helpers.PermInputs.relabel_size π threeRows s h
  exact lower s hc

end PEqualNP.Outside.L_meta_650.SixLeafCycle
