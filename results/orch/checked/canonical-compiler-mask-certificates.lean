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


def checkMasks {n : Nat} :
    (k : Nat) → Program n k → Nat → (Fin n → Nat) → List Nat → Nat → Bool
  | 0, output, truthMask, values, certificates, result =>
      certificates.isEmpty && (conjunctionMasks truthMask values output == result)
  | _ + 1, _, _, _, [], _ => false
  | k + 1, program, truthMask, values, expected :: certificates, result =>
      ((conjunctionMasks truthMask values program.1.1 |||
          conjunctionMasks truthMask values program.1.2) == expected) &&
        checkMasks k program.2 truthMask (Fin.snoc values expected) certificates result

lemma checkMasks_sound {n : Nat} (k : Nat) (program : Program n k)
    (truthMask : Nat) (values : Fin n → Nat) (certificates : List Nat) (result : Nat)
    (hcheck : checkMasks k program truthMask values certificates result = true) :
    evaluateMasks k program truthMask values = result := by
  induction k generalizing n certificates with
  | zero =>
    simp only [checkMasks, Bool.and_eq_true, beq_iff_eq] at hcheck
    exact hcheck.2
  | succ k ih =>
    cases certificates with
    | nil => simp [checkMasks] at hcheck
    | cons expected certificates =>
      simp only [checkMasks, Bool.and_eq_true, beq_iff_eq] at hcheck
      rw [evaluateMasks, hcheck.1]
      exact ih (program := program.2) (values := Fin.snoc values expected)
        (certificates := certificates) hcheck.2

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
