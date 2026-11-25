import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.DoubleStar

open PEqualNP.CircuitLowerBounds

lemma absorption_rewrite (a b u v : Bool)
    (hu : u = true → a = true) (hv : v = true → b = true) :
    (a && b) && (u || v) = (u && b) || (v && a) := by
  cases a <;> cases b <;> cases u <;> cases v <;> simp_all

def original : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩

def replacement : Circuit :=
  ⟨[⟨GateOp.and, [2, 1]⟩, ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma original_ao : PEqualNP.TopForm.IsAO2 4 original := by decide

lemma replacement_ao : PEqualNP.TopForm.IsAO2 4 replacement := by decide

lemma same_size : original.size = replacement.size ∧ replacement.size = 3 := by decide

lemma original_eval : ∀ x : Fin 4 → Bool,
    original.eval (List.ofFn x) = (x 0 && x 1) && (x 2 || x 3) := by decide

lemma replacement_eval : ∀ x : Fin 4 → Bool,
    replacement.eval (List.ofFn x) = (x 2 && x 1) || (x 3 && x 0) := by decide

lemma replace_on_reachable_ports (x : Fin 4 → Bool)
    (hu : x 2 = true → x 0 = true) (hv : x 3 = true → x 1 = true) :
    original.eval (List.ofFn x) = replacement.eval (List.ofFn x) := by
  rw [original_eval, replacement_eval]
  exact absorption_rewrite _ _ _ _ hu hv

lemma replacement_read_one : PEqualNP.ReadK.IsReadK 4 replacement 1 := by decide

end PEqualNP.Outside.L_meta_2583_aux.DoubleStar
