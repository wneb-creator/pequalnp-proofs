import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def rawGate (g : Bool × Nat × Nat) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def rowStep {n : Nat} (w : List (BitVec n)) (g : Bool × Nat × Nat) : List (BitVec n) :=
  w ++ [if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0
    else w.getD g.2.1 0 ||| w.getD g.2.2 0]

def rowBits {n : Nat} (b : Nat) (w : List (BitVec n)) : List Bool :=
  w.map (fun v => v.getLsbD b)

lemma bits_getD {n : Nat} (b i : Nat) (w : List (BitVec n)) :
    (w.map (fun v => v.getLsbD b)).getD i false = (w.getD i 0).getLsbD b := by
  induction w generalizing i with
  | nil => simp
  | cons v w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

lemma row_step_sound {n : Nat} (b : Nat) (w : List (BitVec n))
    (g : Bool × Nat × Nat) :
    rowBits b (rowStep w g) =
      rowBits b w ++ [(rawGate g).op.eval
        ((rawGate g).inputs.map (fun i => (rowBits b w).getD i false))] := by
  rcases g with ⟨op, a, c⟩
  cases op <;> simp [rowStep, rowBits, rawGate, GateOp.eval] <;>
    cases ha : w[a]? <;> cases hc : w[c]? <;> simp_all

lemma row_run_sound {n : Nat} (b : Nat) (gs : List (Bool × Nat × Nat))
    (w : List (BitVec n)) :
    rowBits b (gs.foldl rowStep w) =
      (gs.map rawGate).foldl
        (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (rowBits b w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, row_step_sound]

def rowInput (a : Fin 33) : List (BitVec 33) :=
  List.ofFn (fun i : Fin 33 => if i = a then BitVec.allOnes 33 else 0) ++
    List.ofFn (fun i : Fin 33 => BitVec.ofNat 33 (2 ^ i.val))

lemma row_input_sound (a b : Fin 33) :
    rowBits b.val (rowInput a) = oneEach a b := by
  simp only [rowBits, rowInput, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    by_cases h : i = a
    · simp only [h, ite_true, decide_true]
      rw [BitVec.getLsbD_allOnes]
      simp [b.isLt]
    · simp [h]
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    rw [BitVec.getLsbD_ofNat]
    simp [b.isLt, Nat.testBit_two_pow, Fin.ext_iff]

lemma row_circuit_sound (gs : List (Bool × Nat × Nat)) (out : Nat) (a b : Fin 33) :
    (Circuit.mk (gs.map rawGate) out).eval (oneEach a b) =
      ((gs.foldl rowStep (rowInput a)).getD out 0).getLsbD b.val := by
  rw [← bits_getD]
  change _ = (rowBits b.val (gs.foldl rowStep (rowInput a))).getD out false
  rw [row_run_sound, row_input_sound]
  rfl

end PEqualNP.Outside.L_meta_9502
