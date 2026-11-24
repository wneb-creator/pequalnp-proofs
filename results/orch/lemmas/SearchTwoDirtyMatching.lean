import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.SearchTwoDirtyMatching

open PEqualNP.CircuitLowerBounds

def firstFactor (a b u v : Bool) : Bool := (a || b) && (u || v)

def secondFactor (a b u v : Bool) : Bool := (a || u) && (b || v)

def matchingValue (a b u v : Bool) : Bool := (a && v) || (b && u)

lemma factors_compute_matching : ∀ a b u v : Bool,
    (firstFactor a b u v && secondFactor a b u v) = matchingValue a b u v := by
  decide

def matchingCircuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩], 10⟩

lemma matchingCircuit_monotone : PEqualNP.MetaComplexity.Monotone2 matchingCircuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, matchingCircuit]

lemma matchingCircuit_size : matchingCircuit.size = 7 := by decide

lemma matchingCircuit_correct : ∀ a b u v : Bool,
    matchingCircuit.eval [a, b, u, v] = matchingValue a b u v := by
  decide

lemma first_factor_dirty : firstFactor true false true false = true ∧
    matchingValue true false true false = false := by decide

lemma second_factor_dirty : secondFactor true true false false = true ∧
    matchingValue true true false false = false := by decide

lemma first_factor_no_variable_cleaner : ∀ i : Fin 4, ∃ a b u v : Bool,
    (firstFactor a b u v && [a, b, u, v].getD i.val false) = true ∧
    matchingValue a b u v = false := by decide

lemma second_factor_no_variable_cleaner : ∀ i : Fin 4, ∃ a b u v : Bool,
    (secondFactor a b u v && [a, b, u, v].getD i.val false) = true ∧
    matchingValue a b u v = false := by decide

end PEqualNP.Outside.L_meta_1477.SearchTwoDirtyMatching
