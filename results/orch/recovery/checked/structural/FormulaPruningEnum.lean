import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

def occurs {n : Nat} : DMFormula n → Fin n → Nat
  | .lit j _, i => if j = i then 1 else 0
  | .and a b, i => occurs a i + occurs b i
  | .or a b, i => occurs a i + occurs b i

def literalTable (i : Fin 3) (b : Bool) : Nat :=
  let p := if i.val = 0 then 170 else if i.val = 1 then 204 else 240
  if b then p else Nat.xor 255 p

def pruningTables : DMFormula 3 → List Nat
  | .lit i b => [0, 255, literalTable i b]
  | .and a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.land x))).eraseDups
  | .or a b => ([0, 255] ++ (pruningTables a).flatMap
      (fun x => (pruningTables b).map (Nat.lor x))).eraseDups


def literals : List (DMFormula 3) :=
  [.lit 0 false, .lit 0 true, .lit 1 false, .lit 1 true, .lit 2 false, .lit 2 true]

def formulas : Nat → Nat → List (DMFormula 3)
  | 0, _ => []
  | fuel + 1, leaves =>
    if leaves = 1 then literals
    else (List.range leaves).flatMap fun k =>
      (formulas fuel k).flatMap fun a =>
        (formulas fuel (leaves - k)).flatMap fun b => [.and a b, .or a b]

lemma leaves_pos {n : Nat} (f : DMFormula n) : 0 < f.leaves := by
  induction f with
  | lit i b => simp [DMFormula.leaves]
  | and a b ha hb => simp only [DMFormula.leaves]; omega
  | or a b ha hb => simp only [DMFormula.leaves]; omega

lemma mem_literals (i : Fin 3) (b : Bool) : .lit i b ∈ literals := by
  fin_cases i <;> cases b <;> simp [literals]

lemma mem_formulas (fuel : Nat) (f : DMFormula 3) (bound : f.leaves ≤ fuel) :
    f ∈ formulas fuel f.leaves := by
  induction fuel generalizing f with
  | zero => have pos := leaves_pos f; omega
  | succ fuel ih =>
    cases f with
    | lit i b => change .lit i b ∈ literals; exact mem_literals i b
    | and a b =>
      have ha := leaves_pos a
      have hb := leaves_pos b
      change a.leaves + b.leaves ≤ fuel + 1 at bound
      change _ ∈ formulas (fuel + 1) (a.leaves + b.leaves)
      rw [formulas, if_neg (show a.leaves + b.leaves ≠ 1 by omega)]
      apply List.mem_flatMap.mpr
      refine ⟨a.leaves, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨a, ih a (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨b, ?_, by simp⟩
      simpa only [Nat.add_sub_cancel_left] using ih b (by omega)
    | or a b =>
      have ha := leaves_pos a
      have hb := leaves_pos b
      change a.leaves + b.leaves ≤ fuel + 1 at bound
      change _ ∈ formulas (fuel + 1) (a.leaves + b.leaves)
      rw [formulas, if_neg (show a.leaves + b.leaves ≠ 1 by omega)]
      apply List.mem_flatMap.mpr
      refine ⟨a.leaves, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨a, ih a (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨b, ?_, by simp⟩
      simpa only [Nat.add_sub_cancel_left] using ih b (by omega)

def candidates : List (DMFormula 3) :=
  (List.range 5).flatMap (formulas 4)

lemma mem_candidates (f : DMFormula 3) (bound : f.leaves ≤ 4) : f ∈ candidates := by
  exact List.mem_flatMap.mpr ⟨f.leaves, List.mem_range.mpr (by omega), mem_formulas 4 f bound⟩

def obstructionTest (f : DMFormula 3) : Bool :=
  decide ((∀ i : Fin 3, occurs f i ≤ 2) →
    ¬ (200 ∈ pruningTables f ∧ 234 ∈ pruningTables f ∧ 254 ∈ pruningTables f))

end PEqualNP.Outside.L_meta_2592.FormulaPruning
