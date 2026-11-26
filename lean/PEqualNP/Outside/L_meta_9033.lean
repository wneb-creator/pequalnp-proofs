import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_9033_aux.K2R1BPayloadUpper

def seed (row sa sc mask : Nat) : Bool :=
  (row &&& mask != 0) ||
    (row.testBit 0 && (sa &&& mask == sa)) ||
    (row.testBit 2 && (sc &&& mask == sc))

def outputUpper (hp leaf1 leaf2 : Nat × Nat) (sa sc row : Nat) : Bool :=
  let h := seed row sa sc hp.1 && seed row sa sc hp.2
  let q := row.testBit 1 || h
  let port := fun mask => seed row sa sc mask || (mask.testBit 1 && q)
  (port leaf1.1 && port leaf1.2) || (port leaf2.1 && port leaf2.2)

lemma left_misses_EG (sa sc : Nat) :
    outputUpper (64, 176) (8, 162) (18, 32) sa sc 80 = false := by
  rfl

lemma right_misses_EG (sa sc : Nat) :
    outputUpper (16, 224) (8, 162) (32, 66) sa sc 80 = false := by
  rfl

lemma C_irrelevant_AG (sa sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa sc 65 =
      outputUpper (88, 160) (2, 40) (16, 64) sa 0 65 := by
  rfl

lemma C_irrelevant_AH (sa sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa sc 129 =
      outputUpper (88, 160) (2, 40) (16, 64) sa 0 129 := by
  rfl

lemma middle_finite : ∀ sa : Fin 256, sa.val ≠ 0 →
    outputUpper (88, 160) (2, 40) (16, 64) sa.val 0 65 = false ∨
      outputUpper (88, 160) (2, 40) (16, 64) sa.val 0 129 = false := by
  decide +kernel

lemma middle_misses_A_edge (sa : Fin 256) (hsa : sa.val ≠ 0) (sc : Nat) :
    outputUpper (88, 160) (2, 40) (16, 64) sa.val sc 65 = false ∨
      outputUpper (88, 160) (2, 40) (16, 64) sa.val sc 129 = false := by
  rw [C_irrelevant_AG, C_irrelevant_AH]
  exact middle_finite sa hsa

end PEqualNP.Outside.L_meta_9033_aux.K2R1BPayloadUpper
