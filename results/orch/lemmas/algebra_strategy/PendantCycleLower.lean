import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.L106

namespace PEqualNP.Outside.L_meta_650_aux.PendantCycle

open PEqualNP.MetaComplexity

def f9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && (x 3 || x 4 || x 6)) ||
  (x 1 && (x 3 || x 5 || x 7)) ||
  (x 2 && (x 4 || x 5 || x 8))

def f8 (x : Fin 8 → Bool) : Bool := f9 (Fin.snoc x false)

def f7 (x : Fin 7 → Bool) : Bool := f8 (Fin.snoc x false)

def f6 (x : Fin 6 → Bool) : Bool := f7 (Fin.snoc x false)

theorem no_ten : ¬ HasCircuitSize 9 f9 10 := by
  intro h
  have h8 : HasCircuitSize 8 f8 9 :=
    Helpers.gate_elim 8 f9 false 9
      (by refine ⟨fun i => decide (i.val = 2), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩
        decide)
      h
  have h7 : HasCircuitSize 7 f7 8 :=
    Helpers.gate_elim 7 f8 false 8
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩
        decide)
      h8
  have h6 : HasCircuitSize 6 f6 7 :=
    Helpers.gate_elim 6 f7 false 7
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 3), fun _ => false, ?_⟩
        decide)
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

end PEqualNP.Outside.L_meta_650_aux.PendantCycle
