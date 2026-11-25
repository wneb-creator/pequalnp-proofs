import DirectFilterCore
import PairLocalization

namespace PEqualNP.Outside.L_meta_1884.DirectFilter

open PEqualNP.CircuitLowerBounds

lemma operand_positive (pre : List Gate) (tail : List Nat) (x : Fin 10 → Bool) :
    operand pre (0 :: tail) x = x 0 := by
  simp only [operand, List.map_cons, List.headD_cons]
  rw [SoleReader.run_input pre _ 0 (by simp [seed])]
  exact SoleReader.free_input_pin x 0

lemma operand_negative (pre : List Gate) (tail : List Nat) (x : Fin 10 → Bool) :
    operand pre (10 :: tail) x = !x 0 := by
  simp only [operand, List.map_cons, List.headD_cons]
  rw [SoleReader.run_input pre _ 10 (by simp [seed])]
  simp [seed, List.getD_eq_getElem?_getD]

lemma excludes_positive_operand (pre : List Gate) (tail : List Nat) (v : Fin 10)
    (hv : v ≠ 0) (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (hfactor : ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
      (x v || operand pre (0 :: tail) x) = (y v || operand pre (0 :: tail) y) →
      SoleOrPartner.target x = SoleOrPartner.target y) : False := by
  have h := SoleOrPartner.rejects_other_singleton v hv (operand pre (0 :: tail))
    (operand_fiber_mono pre (0 :: tail) allowed) hfactor 0 (Ne.symm hv)
  simp [operand_positive, SoleOrPartner.singleton] at h

lemma excludes_negative_operand (pre : List Gate) (tail : List Nat) (v : Fin 10)
    (hv : v ≠ 0) (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (hfactor : ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
      (x v || operand pre (10 :: tail) x) = (y v || operand pre (10 :: tail) y) →
      SoleOrPartner.target x = SoleOrPartner.target y) : False := by
  have h := SoleOrPartner.rejects_zero v hv (operand pre (10 :: tail))
    (operand_fiber_mono pre (10 :: tail) allowed) hfactor
  simp [operand_negative] at h

end PEqualNP.Outside.L_meta_1884.DirectFilter
