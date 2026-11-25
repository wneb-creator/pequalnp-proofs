import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.DirtyObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core

lemma path_factor : ∀ a b c d : Bool,
    (((a || d) && (b || c)) && (a || b)) =
      ((a && (b || c)) || (d && b)) := by decide

def dirty : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [6, 7]⟩], 8⟩

def clean : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩,
    ⟨.and, [3, 1]⟩, ⟨.or, [5, 6]⟩], 7⟩

abbrev pathGraph : SimpleGraph (Fin 4) :=
  edgeGraph 4 [(0, 1), (0, 2), (3, 1)]

def bypassLeft : Circuit :=
  ⟨dirty.gates.set 2 ⟨.or, [4, 4]⟩, dirty.output⟩

def bypassRight : Circuit :=
  ⟨dirty.gates.set 2 ⟨.or, [5, 5]⟩, dirty.output⟩

lemma dirty_ao : IsAO2 4 dirty := by decide

lemma clean_ao : IsAO2 4 clean := by decide

lemma dirty_size : dirty.size = 5 := rfl

lemma clean_size : clean.size = 4 := rfl

lemma dirty_eval : ∀ z : Fin 4 → Bool,
    circuitFun 4 dirty z =
      ((z 0 && z 1) || (z 0 && z 2) || (z 3 && z 1)) := by decide

lemma clean_eval : ∀ z : Fin 4 → Bool,
    circuitFun 4 clean z =
      ((z 0 && z 1) || (z 0 && z 2) || (z 3 && z 1)) := by decide

lemma same_function : circuitFun 4 clean = circuitFun 4 dirty := by
  funext z
  rw [clean_eval, dirty_eval]

lemma dirty_computes_graph : circuitFun 4 dirty = graphFun pathGraph ∅ := by
  funext z
  revert z
  decide

lemma dirty_gate_not_below : ¬ BelowF pathGraph dirty 2 := by decide

lemma output_below : BelowF pathGraph dirty 4 := by decide

set_option maxRecDepth 100000 in
lemma dirty_not_read_one : ¬ IsReadK 4 dirty 1 := by decide

set_option maxRecDepth 100000 in
lemma clean_read_one : IsReadK 4 clean 1 := by decide

set_option maxRecDepth 100000 in
lemma dirty_lift_fixed : IsLiftFixedPoint pathGraph dirty := by decide

set_option maxRecDepth 100000 in
lemma no_and_operand_below :
    ∀ k < dirty.gates.length, (gateAt dirty k).op = .and →
      ∀ t ∈ (gateAt dirty k).inputs,
        ¬ (∀ z : Fin 4 → Bool,
          Circuit.eval ⟨dirty.gates, t⟩ (List.ofFn z) = true →
            graphFun pathGraph ∅ z = true) := by
  intro k hk hop t ht
  change k < 5 at hk
  interval_cases k <;> simp [dirty, gateAt] at hop ht
  all_goals rcases ht with rfl | rfl <;> decide

lemma bypass_left_fails :
    circuitFun 4 bypassLeft (fun i => decide (i = 0)) = true ∧
    circuitFun 4 dirty (fun i => decide (i = 0)) = false := by decide

lemma bypass_right_fails :
    circuitFun 4 bypassRight (fun i => decide (i = 1)) = true ∧
    circuitFun 4 dirty (fun i => decide (i = 1)) = false := by decide

lemma smaller_read_one_replacement :
    ∃ D : Circuit, IsAO2 4 D ∧ circuitFun 4 D = circuitFun 4 dirty ∧
      D.size < dirty.size ∧ IsReadK 4 D 1 :=
  ⟨clean, clean_ao, same_function, by decide, clean_read_one⟩

end PEqualNP.Outside.L_meta_2583_aux.DirtyObstruction
