import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sharedOrExample : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩,
    ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 0]⟩,
    ⟨.and, [10, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 9]⟩], 14⟩

def sharedOrIncidence (p l : Fin 3) : Prop :=
  (p = 0 ∧ (l = 0 ∨ l = 1)) ∨ (p = 1 ∧ l = 1) ∨ (p = 2 ∧ l = 2)

def sharedOrClean : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩,
    ⟨.or, [7, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma sharedOrExample_sizes : sharedOrExample.size = 9 ∧ sharedOrClean.size = 6 := by
  decide

set_option synthInstance.maxSize 1000 in
lemma sharedOrIncidence_c4_free :
    ∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
      ¬ (sharedOrIncidence p l ∧ sharedOrIncidence p l' ∧
        sharedOrIncidence p' l ∧ sharedOrIncidence p' l') := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_model :
    Monotone2 sharedOrExample ∧ NestedCover.ReadsBack 6 sharedOrExample ∧
      Monotone2 sharedOrClean ∧ NestedCover.ReadsBack 6 sharedOrClean := by
  let := NestedCover.gateOpDecEq
  unfold Monotone2
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma sharedOrExample_computes :
    ∀ z : Fin 6 → Bool, circuitFun 6 sharedOrExample z = true ↔
      ∃ p l : Fin 3, sharedOrIncidence p l ∧
        z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true := by
  unfold sharedOrIncidence
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma sharedOrClean_computes :
    ∀ z : Fin 6 → Bool, circuitFun 6 sharedOrClean z = true ↔
      ∃ p l : Fin 3, sharedOrIncidence p l ∧
        z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_dirty :
    ¬ sharedOrIncidence 1 0 ∧
      (sharedOrExample.wires (List.ofFn (fun k : Fin 6 => decide (k = 1 ∨ k = 3)))).getD
        8 false = true := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_replace_left :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => 6))
      (fun k => decide (k = 0)) = true ∧
    circuitFun 6 sharedOrExample (fun k => decide (k = 0)) = false := by
  decide

lemma sharedOrExample_replace_right :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => 7))
      (fun k => decide (k = 4)) = true ∧
    circuitFun 6 sharedOrExample (fun k => decide (k = 4)) = false := by
  decide

lemma sharedOrExample_only_reader :
    PEqualNP.TopForm.readers 6 sharedOrExample 2 = {4} := by
  decide

lemma sharedOrExample_no_factor_substitution (sigma : ℕ → ℕ)
    (hs : sigma 4 = 6 ∨ sigma 4 = 7) :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 sigma) ≠
      circuitFun 6 sharedOrExample := by
  have heq : PEqualNP.FactorSubst.substReads sharedOrExample 6 2 sigma =
      PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => sigma 4) := by
    rfl
  rw [heq]
  rcases hs with hs | hs
  · rw [hs]
    intro he
    have hx := congrFun he (fun k => decide (k = 0))
    rw [sharedOrExample_replace_left.1, sharedOrExample_replace_left.2] at hx
    cases hx
  · rw [hs]
    intro he
    have hx := congrFun he (fun k => decide (k = 4))
    rw [sharedOrExample_replace_right.1, sharedOrExample_replace_right.2] at hx
    cases hx

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
lemma sharedOrClean_rejects :
    (∀ j < sharedOrClean.gates.length, (NestedCover.gateAt sharedOrClean j).op = GateOp.and →
      ∀ p l : Fin 3, ¬ sharedOrIncidence p l →
        (sharedOrClean.wires (List.ofFn (fun k : Fin 6 =>
          decide (k = Fin.castAdd 3 p ∨ k = Fin.natAdd 3 l)))).getD (6 + j) false = false) ∧
    (∀ j < sharedOrClean.gates.length, (NestedCover.gateAt sharedOrClean j).op = GateOp.and →
      ∀ k : Fin 6, (sharedOrClean.wires (List.ofFn (fun w : Fin 6 => decide (w = k)))).getD
        (6 + j) false = false) := by
  let := NestedCover.gateOpDecEq
  unfold sharedOrIncidence
  decide

end PEqualNP.Outside.L_meta_3451_aux
