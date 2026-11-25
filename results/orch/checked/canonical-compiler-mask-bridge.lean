import CanonicalCompilerDefs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

def conjunctionMasks {n : Nat} (truthMask : Nat) (values : Fin n → Nat)
    (xs : List (Fin n)) : Nat :=
  xs.foldr (fun i mask => values i &&& mask) truthMask

def evaluateMasks {n : Nat} : (k : Nat) → Program n k → Nat → (Fin n → Nat) → Nat
  | 0, output, truthMask, values => conjunctionMasks truthMask values output
  | k + 1, program, truthMask, values =>
      evaluateMasks k program.2 truthMask
        (Fin.snoc values
          (conjunctionMasks truthMask values program.1.1 |||
            conjunctionMasks truthMask values program.1.2))

lemma conjunctionMasks_testBit {n : Nat} (truthMask : Nat) (values : Fin n → Nat)
    (xs : List (Fin n)) (r : Nat) (htruth : truthMask.testBit r = true) :
    (conjunctionMasks truthMask values xs).testBit r = xs.all (fun i => (values i).testBit r) := by
  induction xs with
  | nil => simpa [conjunctionMasks] using htruth
  | cons i xs ih =>
    simpa only [conjunctionMasks, List.foldr_cons, Nat.testBit_land, List.all_cons] using
      congrArg (fun b => (values i).testBit r && b) ih

lemma evaluateMasks_testBit {n : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (values : Fin n → Nat) (r : Nat)
    (htruth : truthMask.testBit r = true) :
    (evaluateMasks k program truthMask values).testBit r =
      evaluate k program (fun i => (values i).testBit r) := by
  induction k generalizing n with
  | zero => exact conjunctionMasks_testBit truthMask values program r htruth
  | succ k ih =>
    simp only [evaluateMasks, evaluate]
    rw [ih]
    apply congrArg (evaluate k program.2)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Nat.testBit_lor,
        conjunctionMasks_testBit truthMask values _ r htruth]
    · simp only [Fin.snoc_castSucc]

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
