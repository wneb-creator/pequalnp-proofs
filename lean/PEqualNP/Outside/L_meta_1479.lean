import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1479

def BinaryAO (n : ℕ) (C : Circuit) : Prop :=
  ∀ j (g : Gate), C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

def binaryGateCheck (n j : ℕ) (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [a,b] => decide (a ≠ b ∧ a < n+j ∧ b < n+j)
  | .or, [a,b] => decide (a ≠ b ∧ a < n+j ∧ b < n+j)
  | _, _ => false

lemma binaryGateCheck_sound {n j : ℕ} {g : Gate}
    (h : binaryGateCheck n j g = true) :
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j := by
  unfold binaryGateCheck at h
  split at h
  · rename_i a b hop hin
    exact ⟨Or.inl hop,a,b,hin,of_decide_eq_true h⟩
  · rename_i a b hop hin
    exact ⟨Or.inr hop,a,b,hin,of_decide_eq_true h⟩
  · contradiction

lemma binaryAO_of_check {n : ℕ} {C : Circuit}
    (h : ∀ j : Fin C.gates.length, binaryGateCheck n j C.gates[j] = true) :
    BinaryAO n C := by
  intro j g hj
  obtain ⟨hlt,heq⟩ := List.getElem?_eq_some_iff.mp hj
  subst g
  exact binaryGateCheck_sound (h ⟨j,hlt⟩)

def DerivativeTrace (n : ℕ) (C : Circuit) (base seed : Fin n → Bool)
    (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = seed i) ∧
  ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
    (g.op = .and → d (n+j) =
      (((C.wires (List.ofFn base)).getD a false && d b) ||
        (d a && (C.wires (List.ofFn base)).getD b false))) ∧
    (g.op = .or → d (n+j) = (d a || d b))

lemma derivativeTrace_exists {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base seed : Fin n → Bool) : ∃ d : ℕ → Bool, DerivativeTrace n C base seed d := by
  classical
  let step (m : ℕ) (prev : (i : ℕ) → i < m → Bool) : Bool :=
    if h : m < n then seed ⟨m,h⟩ else
    let g := C.gates[m-n]?.getD ⟨GateOp.or,[]⟩
    let a := g.inputs[0]?.getD 0
    let b := g.inputs[1]?.getD 0
    if ha : a < m then if hb : b < m then
      if g.op = .and then
        ((C.wires (List.ofFn base)).getD a false && prev b hb) ||
          (prev a ha && (C.wires (List.ofFn base)).getD b false)
      else prev a ha || prev b hb
    else false else false
  let d (m : ℕ) : Bool := Nat.strongRecOn m step
  have unfoldD (m : ℕ) : d m = step m (fun i _ => d i) := Nat.strongRecOn_eq step m
  refine ⟨d,?_,?_⟩
  · intro i
    rw [unfoldD]
    simp [step,i.isLt]
  · intro j g a b hj hab
    obtain ⟨_,u,v,huv,_,hu,hv⟩ := normal j g hj
    rw [hab] at huv
    simp only [List.cons.injEq,and_true] at huv
    obtain ⟨rfl,rfl⟩ := huv
    have big : ¬ n+j < n := by omega
    have eqj : n+j-n = j := by omega
    constructor <;> intro hop <;> rw [unfoldD] <;>
      simp [step,big,eqj,hj,hab,hu,hv,hop]

lemma derivativeTrace_dark_and {n : ℕ} {C : Circuit} (normal : BinaryAO n C)
    (base seed : Fin n → Bool) (j a b : ℕ)
    (atGate : C.gates[j]? = some ⟨.and,[a,b]⟩)
    (left : (C.wires (List.ofFn base)).getD a false = false)
    (right : (C.wires (List.ofFn base)).getD b false = false) :
    ∃ d : ℕ → Bool, DerivativeTrace n C base seed d ∧ d (n+j) = false := by
  obtain ⟨d,inputs,gates⟩ := derivativeTrace_exists normal base seed
  refine ⟨d,⟨inputs,gates⟩,?_⟩
  rw [(gates j _ a b atGate rfl).1 rfl,left,right]
  simp

end PEqualNP.Outside.L_meta_1479
