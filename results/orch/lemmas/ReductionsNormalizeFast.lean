import ReductionsSemantics

namespace PEqualNP.Outside.Pilot64Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def distinctFast (c : Candidate) : Prop :=
  c.a0 ≠ c.b0 ∧ c.a1 ≠ c.b1 ∧ c.a2 ≠ c.b2 ∧ c.a3 ≠ c.b3 ∧ c.a4 ≠ c.b4

def orderedLeft {n : Nat} (a b : Fin n) : Fin n := if a.val < b.val then a else b
def orderedRight {n : Nat} (a b : Fin n) : Fin n := if a.val < b.val then b else a

def normalizeFast (c : Candidate) : Candidate :=
  {
    op0 := c.op0
    a0 := orderedLeft c.a0 c.b0
    b0 := orderedRight c.a0 c.b0
    op1 := c.op1
    a1 := orderedLeft c.a1 c.b1
    b1 := orderedRight c.a1 c.b1
    op2 := c.op2
    a2 := orderedLeft c.a2 c.b2
    b2 := orderedRight c.a2 c.b2
    op3 := c.op3
    a3 := orderedLeft c.a3 c.b3
    b3 := orderedRight c.a3 c.b3
    op4 := c.op4
    a4 := orderedLeft c.a4 c.b4
    b4 := orderedRight c.a4 c.b4
  }

theorem ordered_val {n : Nat} (a b : Fin n) (op : Bool) (w : List Bool) :
    (if op then w.getD (orderedLeft a b).val false && w.getD (orderedRight a b).val false
      else w.getD (orderedLeft a b).val false || w.getD (orderedRight a b).val false) =
    (if op then w.getD a.val false && w.getD b.val false
      else w.getD a.val false || w.getD b.val false) := by
  by_cases h : a.val < b.val
  · simp [orderedLeft, orderedRight, h]
  · simp [orderedLeft, orderedRight, h, Bool.and_comm, Bool.or_comm]

theorem ordered_deriv {n : Nat} (a b : Fin n) (op : Bool) (v d : List Bool) :
    (if op then
       (v.getD (orderedLeft a b).val false && d.getD (orderedRight a b).val false) ||
       (d.getD (orderedLeft a b).val false && v.getD (orderedRight a b).val false)
     else d.getD (orderedLeft a b).val false || d.getD (orderedRight a b).val false) =
    (if op then (v.getD a.val false && d.getD b.val false) ||
       (d.getD a.val false && v.getD b.val false)
     else d.getD a.val false || d.getD b.val false) := by
  by_cases h : a.val < b.val
  · simp [orderedLeft, orderedRight, h]
  · simp [orderedLeft, orderedRight, h, Bool.and_comm, Bool.or_comm]

theorem normalizeFast_valid (c : Candidate) (hd : distinctFast c) : valid (normalizeFast c) := by
  rcases hd with ⟨h0, h1, h2, h3, h4⟩
  have hn0 : (normalizeFast c).a0.val < (normalizeFast c).b0.val := by
    by_cases h : c.a0.val < c.b0.val
    · simp [normalizeFast, orderedLeft, orderedRight, h]
    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]
      have hn : c.a0.val ≠ c.b0.val := by
        intro he
        exact h0 (Fin.ext he)
      omega
  have hn1 : (normalizeFast c).a1.val < (normalizeFast c).b1.val := by
    by_cases h : c.a1.val < c.b1.val
    · simp [normalizeFast, orderedLeft, orderedRight, h]
    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]
      have hn : c.a1.val ≠ c.b1.val := by
        intro he
        exact h1 (Fin.ext he)
      omega
  have hn2 : (normalizeFast c).a2.val < (normalizeFast c).b2.val := by
    by_cases h : c.a2.val < c.b2.val
    · simp [normalizeFast, orderedLeft, orderedRight, h]
    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]
      have hn : c.a2.val ≠ c.b2.val := by
        intro he
        exact h2 (Fin.ext he)
      omega
  have hn3 : (normalizeFast c).a3.val < (normalizeFast c).b3.val := by
    by_cases h : c.a3.val < c.b3.val
    · simp [normalizeFast, orderedLeft, orderedRight, h]
    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]
      have hn : c.a3.val ≠ c.b3.val := by
        intro he
        exact h3 (Fin.ext he)
      omega
  have hn4 : (normalizeFast c).a4.val < (normalizeFast c).b4.val := by
    by_cases h : c.a4.val < c.b4.val
    · simp [normalizeFast, orderedLeft, orderedRight, h]
    · simp only [normalizeFast, orderedLeft, orderedRight, h, ↓reduceIte]
      have hn : c.a4.val ≠ c.b4.val := by
        intro he
        exact h4 (Fin.ext he)
      omega
  exact ⟨hn0, hn1, hn2, hn3, hn4⟩

theorem evalCircuit_normalizeFast (c : Candidate) (mask : Nat) :
    evalCircuit (normalizeFast c) mask = evalCircuit c mask := by
  dsimp only [evalCircuit, normalizeFast]
  simp only [ordered_val]

theorem derivativeCircuit_normalizeFast (c : Candidate) (base seed : Nat) :
    derivativeCircuit (normalizeFast c) base seed = derivativeCircuit c base seed := by
  dsimp only [derivativeCircuit, normalizeFast]
  simp only [ordered_val, ordered_deriv]

end PEqualNP.Outside.Pilot64Bridge
