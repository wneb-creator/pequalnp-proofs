import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- This refutes only a local proof strategy, not the statement of L-meta-1904.
-- Its first unsafe AND is true on a singleton and cannot be replaced by
-- either operand. A different
-- four-gate circuit does satisfy the desired safety property.
def pathGraph : SimpleGraph (Fin 4) where
  Adj a b := (a=0 ∧ b=2) ∨ (a=2 ∧ b=0) ∨ (a=0 ∧ b=3) ∨
    (a=3 ∧ b=0) ∨ (a=1 ∧ b=2) ∨ (a=2 ∧ b=1)
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel

instance : DecidableRel pathGraph.Adj := by
  intro a b
  change Decidable ((a=0 ∧ b=2) ∨ (a=2 ∧ b=0) ∨ (a=0 ∧ b=3) ∨
    (a=3 ∧ b=0) ∨ (a=1 ∧ b=2) ∨ (a=2 ∧ b=1))
  infer_instance

def pathFun (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)

def original : Circuit := ⟨
  [⟨.or,[0,2]⟩, ⟨.or,[0,1]⟩, ⟨.and,[4,5]⟩,
   ⟨.or,[2,3]⟩, ⟨.and,[6,7]⟩], 8⟩

def bypassLeft : Circuit := ⟨
  [⟨.or,[0,2]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[4,6]⟩], 7⟩

def bypassRight : Circuit := ⟨
  [⟨.or,[0,2]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.and,[5,6]⟩], 7⟩

def repaired : Circuit := ⟨
  [⟨.or,[0,1]⟩, ⟨.and,[2,4]⟩, ⟨.and,[0,3]⟩, ⟨.or,[5,6]⟩], 7⟩

theorem path_triangle_free : ∀ a b c : Fin 4,
    pathGraph.Adj a b → pathGraph.Adj b c → ¬pathGraph.Adj c a := by
  decide +kernel

theorem path_square_free : ∀ a b c d : Fin 4,
    pathGraph.Adj a b → pathGraph.Adj b c → pathGraph.Adj c d →
    pathGraph.Adj d a → a=c ∨ b=d := by
  decide +kernel

theorem path_expansion : ∀ x : Fin 4 → Bool,
    pathFun x = decide (∃ a b, pathGraph.Adj a b ∧ x a=true ∧ x b=true) := by
  decide +kernel

theorem original_monotone : Monotone2 original := by simp [Monotone2, original]

theorem original_computes : ∀ x : Fin 4 → Bool,
    original.eval (List.ofFn x) = pathFun x := by
  decide +kernel

theorem first_and_unsafe :
    (original.wires (List.ofFn (fun i : Fin 4 => i == 0))).getD 6 false = true ∧
    pathFun (fun i : Fin 4 => i == 0) = false := by
  decide +kernel

theorem bypass_left_wrong :
    bypassLeft.eval (List.ofFn (fun i : Fin 4 => i == 2)) ≠
      pathFun (fun i : Fin 4 => i == 2) := by
  decide +kernel

theorem bypass_right_wrong :
    bypassRight.eval (List.ofFn (fun i : Fin 4 => i == 1 || i == 3)) ≠
      pathFun (fun i : Fin 4 => i == 1 || i == 3) := by
  decide +kernel

theorem repair_computes : ∀ x : Fin 4 → Bool,
    repaired.eval (List.ofFn x) = pathFun x := by
  decide +kernel

theorem repair_monotone : Monotone2 repaired := by simp [Monotone2, repaired]

theorem repair_smaller : repaired.size + 1 = original.size := rfl

theorem repair_and_safe : ∀ j : Fin 4,
    ∀ x : Fin 4 → Bool, (repaired.gates.getD j.val ⟨.or, []⟩).op = .and →
      (repaired.wires (List.ofFn x)).getD (4+j.val) false = true → pathFun x = true := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  simp [repaired] <;> decide +kernel

end PEqualNP.Outside.L_meta_1904_aux
