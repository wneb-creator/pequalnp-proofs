import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451_aux.Two

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Bool → Bool → Bool → Bool → Circuit
  | false, false, false, false => ⟨[], 4⟩
  | true, false, false, false => ⟨[⟨.and, [0, 2]⟩], 4⟩
  | false, true, false, false => ⟨[⟨.and, [0, 3]⟩], 4⟩
  | true, true, false, false => ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩], 5⟩
  | false, false, true, false => ⟨[⟨.and, [1, 2]⟩], 4⟩
  | true, false, true, false => ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 2]⟩], 5⟩
  | false, true, true, false =>
      ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩
  | true, true, true, false =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, false, false, true => ⟨[⟨.and, [1, 3]⟩], 4⟩
  | true, false, false, true =>
      ⟨[⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩
  | false, true, false, true => ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 3]⟩], 5⟩
  | true, true, false, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, false, true, true => ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩], 5⟩
  | true, false, true, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, true, true, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | true, true, true, true =>
      ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩], 6⟩

def relation (a b c d : Bool) (p l : Fin 2) : Prop :=
  (if p = 0 then if l = 0 then a else b else if l = 0 then c else d) = true

def truth (a b c d : Bool) (z : Fin 4 → Bool) : Bool :=
  (a && z 0 && z 2) || (b && z 0 && z 3) ||
    (c && z 1 && z 2) || (d && z 1 && z 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma witness_props : ∀ a b c d : Bool,
    Monotone2 (witness a b c d) ∧ NestedCover.ReadsBack 4 (witness a b c d) ∧
    (∀ z : Fin 4 → Bool, circuitFun 4 (witness a b c d) z = truth a b c d z) ∧
    (∀ j < (witness a b c d).gates.length,
      (NestedCover.gateAt (witness a b c d) j).op = GateOp.and →
      ∀ p l : Fin 2, ¬ relation a b c d p l →
        ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
    (∀ j < (witness a b c d).gates.length,
      (NestedCover.gateAt (witness a b c d) j).op = GateOp.and →
      (∀ p : Fin 2, ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
        decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
      ∀ l : Fin 2, ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
        decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  let _ : DecidableEq GateOp := NestedCover.gateOpDecEq
  unfold Monotone2 NestedCover.ReadsBack relation
  decide

lemma relation_truth (a b c d : Bool) (z : Fin 4 → Bool) :
    truth a b c d z = true ↔
      ∃ p l : Fin 2, relation a b c d p l ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, relation, truth]
  simp
  tauto

lemma relation_encode (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] :
    ∀ p l : Fin 2, relation (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1)) p l ↔ I p l := by
  intro p l
  fin_cases p <;> fin_cases l <;> simp [relation]

def code (a b c d : Bool) : Fin 16 :=
  Fin.ofNat 16 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat)

lemma code_bits : ∀ a b c d : Bool,
    (code a b c d).val.testBit 0 = a ∧ (code a b c d).val.testBit 1 = b ∧
    (code a b c d).val.testBit 2 = c ∧ (code a b c d).val.testBit 3 = d := by
  decide

lemma witness_size : ∀ a b c d : Bool, (witness a b c d).size =
    ([0, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4, 2, 4, 4, 3] : List ℕ).getD
      (code a b c d).val 0 := by
  decide

lemma witness_size_le_four : ∀ a b c d : Bool, (witness a b c d).size ≤ 4 := by
  decide

lemma circuit_truth (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∀ z : Fin 4 → Bool, circuitFun 4 C z =
      truth (decide (I 0 0)) (decide (I 0 1)) (decide (I 1 0)) (decide (I 1 1)) z := by
  intro z
  apply Bool.eq_iff_iff.mpr
  rw [sem, relation_truth]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨p, l, (relation_encode I p l).mpr hi, hp, hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨p, l, (relation_encode I p l).mp hi, hp, hl⟩

lemma from_size (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hsize : (witness (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1))).size ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  let a := decide (I 0 0)
  let b := decide (I 0 1)
  let c := decide (I 1 0)
  let d := decide (I 1 1)
  obtain ⟨hm, hb, he, hp, hz⟩ := witness_props a b c d
  have rel : ∀ p l, relation a b c d p l ↔ I p l := relation_encode I
  refine ⟨witness a b c d, hm, hb, hsize, ?_, ?_, hz⟩
  · intro z
    rw [he, relation_truth]
    constructor
    · rintro ⟨p, l, hi, hzp, hzl⟩
      exact ⟨p, l, (rel p l).mp hi, hzp, hzl⟩
    · rintro ⟨p, l, hi, hzp, hzl⟩
      exact ⟨p, l, (rel p l).mpr hi, hzp, hzl⟩
  · intro j hj hand p l hn
    exact hp j hj hand p l (fun hi => hn ((rel p l).mp hi))

lemma large_enough (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hsize : 4 ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) :=
  from_size I C ((witness_size_le_four _ _ _ _).trans hsize)

end PEqualNP.Outside.L_meta_3451_aux.Two
