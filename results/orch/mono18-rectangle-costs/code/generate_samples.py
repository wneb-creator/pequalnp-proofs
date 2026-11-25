from pathlib import Path
import json
p=Path(__file__).resolve().parent
ms=json.loads((p.parent/'mono18-oredge-weak-census/matrices.json').read_text())
s='''import Mono18RectangleBase

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle

open Live1024 RectangleRun

def matrixSpecs : List (Nat × List Nat × List Nat) := [
'''+',\n'.join('  ('+str(m['weight'])+', ['+','.join(map(str,m['positive_rows']))+'], ['+','.join(map(str,m['negative_rows']))+'])' for m in ms)+''']

def matrixSpec (m : Nat) : Nat × List Nat × List Nat := matrixSpecs.getD m (0, [], [])
def matrixWeight (m : Nat) : Nat := (matrixSpec m).1
def positiveSample (m i : Nat) : Row := Fin.ofNat 1024 ((matrixSpec m).2.1.getD i 0)
def negativeSample (m i : Nat) : Row := Fin.ofNat 1024 ((matrixSpec m).2.2.getD i 0)

def supportCheck (m record : Nat) (v : Sig) : Bool :=
  let w := matrixWeight m
  (List.range (rowCount w)).all (fun r => !bit (positiveSample m r) v ||
    decide (r ∈ mask (rowCount w) (posMask w (recordCode w record)))) &&
  (List.range (colCount w)).all (fun c => bit (negativeSample m c) v ||
    decide (c ∈ mask (colCount w) (negMask w (recordCode w record))))

lemma bounds_of_support (m record : Nat) (v : Sig)
    (cost : checkRecord (matrixWeight m) record = true)
    (support : supportCheck m record v = true) :
    Bounds (fun r : Fin (rowCount (matrixWeight m)) => positiveSample m r.val)
      (fun c : Fin (colCount (matrixWeight m)) => negativeSample m c.val)
      (fun r c => weight (matrixWeight m) r.val c.val) (observe v)
      (recordCap (matrixWeight m) record) := by
  apply bounds_of_record _ _ (matrixWeight m) record (observe v) cost
  · intro r pos
    change bit (positiveSample m r.val) v = true at pos
    have checks := support
    simp only [supportCheck, Bool.and_eq_true] at checks
    have checked := checks.1
    have h := List.all_eq_true.mp checked r.val (List.mem_range.mpr r.isLt)
    simpa only [pos, Bool.not_true, Bool.false_or, decide_eq_true_eq] using h
  · intro c neg
    change bit (negativeSample m c.val) v = false at neg
    have checks := support
    simp only [supportCheck, Bool.and_eq_true] at checks
    have checked := checks.2
    have h := List.all_eq_true.mp checked c.val (List.mem_range.mpr c.isLt)
    simpa only [neg, Bool.false_or, decide_eq_true_eq] using h

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle
'''
(p/'Mono18RectangleSamples.lean').write_text(s)
print('bytes',len(s.encode()))
