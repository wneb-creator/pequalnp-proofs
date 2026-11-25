import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.WordCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wordGate {k : ℕ} (g : Gate) (w : List (BitVec k)) : BitVec k :=
  match g.op with
  | .and => w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0
  | .or => w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0
  | _ => 0

def wordWires {k : ℕ} (C : Circuit) (x : List (BitVec k)) : List (BitVec k) :=
  C.gates.foldl (fun w g => w ++ [wordGate g w]) x

def wordEval {k : ℕ} (C : Circuit) (x : List (BitVec k)) : BitVec k :=
  (wordWires C x).getD C.output 0

lemma getD_bit {k : ℕ} (xs : List (BitVec k)) (i t : ℕ) :
    (xs.getD i 0).getLsbD t = (xs.map fun w => w.getLsbD t).getD i false := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp_all

lemma gate_bit {k : ℕ} (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (xs : List (BitVec k)) (t : ℕ) :
    (wordGate g xs).getLsbD t =
      g.op.eval (g.inputs.map fun i =>
        (xs.map fun w => w.getLsbD t).getD i false) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop
  · have h : wordGate g xs = xs.getD a 0 &&& xs.getD b 0 := by
      simp [wordGate, hop, hab]
    rw [h, BitVec.getLsbD_and, getD_bit, getD_bit, hop, hab]
    simp [GateOp.eval]
  · have h : wordGate g xs = xs.getD a 0 ||| xs.getD b 0 := by
      simp [wordGate, hop, hab]
    rw [h, BitVec.getLsbD_or, getD_bit, getD_bit, hop, hab]
    simp [GateOp.eval]

lemma fold_bit {k : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
    ∀ (xs : List (BitVec k)) (t : ℕ),
      (gs.foldl (fun w g => w ++ [wordGate g w]) xs).map (fun w => w.getLsbD t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (xs.map fun w => w.getLsbD t) := by
  induction gs with
  | nil => intro h xs t; rfl
  | cons g gs ih =>
    intro h xs t
    have hg := h g (by simp)
    have hs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
      intro a ha
      exact h a (by simp [ha])
    simp only [List.foldl_cons]
    rw [ih hs]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil,
      gate_bit g hg.1 hg.2 xs t]

lemma wordEval_sound {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (t : ℕ) :
    (wordEval C (List.ofFn X)).getLsbD t =
      circuitFun n C (fun i => (X i).getLsbD t) := by
  have h := fold_bit C.gates
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (List.ofFn X) t
  have he := congrArg (fun xs : List Bool => xs.getD C.output false) h
  rw [← getD_bit] at he
  simpa only [wordEval, wordWires, circuitFun, Circuit.eval, Circuit.wires,
    List.map_ofFn, Function.comp_def] using he

lemma zero_certificate {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (hzero : wordEval C (List.ofFn X) = 0) :
    ∀ t : ℕ, circuitFun n C (fun i => (X i).getLsbD t) = false := by
  intro t
  rw [← wordEval_sound C hAO X t, hzero]
  simp

lemma equality_certificate {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (expected : BitVec k)
    (heq : wordEval C (List.ofFn X) = expected) :
    ∀ t : ℕ, circuitFun n C (fun i => (X i).getLsbD t) = expected.getLsbD t := by
  intro t
  rw [← wordEval_sound C hAO X t, heq]

end PEqualNP.Outside.L_meta_2583.WordCertificate
