import Lean
namespace PEqualNP.Outside.L_meta_2592_aux.Projection
abbrev Sig := BitVec 512
def zero : Sig := 0
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
namespace Extended
abbrev Sig := BitVec 1024
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def first : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
end Extended
def projected (a : Extended.Sig) : Sig := a.setWidth 512
end PEqualNP.Outside.L_meta_2592_aux.Projection
namespace PEqualNP.Outside.L_meta_2592_aux.Projection

theorem projected_bin (d : Nat) (a b : Extended.Sig) :
    projected (Extended.bin d a b) = bin d (projected a) (projected b) := by
  unfold projected Extended.bin bin
  by_cases h0 : d = 0
  · simp [h0]
  by_cases h1 : d = 1
  · simp [h0, h1]
  by_cases h2 : d = 2
  · simp [h0, h1, h2, BitVec.setWidth_not (by decide : 512 ≤ 1024)]
  · simp [h0, h1, h2, BitVec.setWidth_not (by decide : 512 ≤ 1024)]

theorem projected_bin_zero_left (d : Nat) (a b : Extended.Sig)
    (ha : projected a = zero) :
    projected (Extended.bin d a b) =
      if d = 0 then zero else if d = 1 then projected b else
        if d = 2 then zero else projected b := by
  rw [projected_bin, ha]
  unfold bin
  rw [show zero = 0#512 by rfl]
  simp only [BitVec.zero_and, BitVec.zero_or, BitVec.not_zero,
    BitVec.allOnes_and]

theorem projected_bin_zero_right (d : Nat) (a b : Extended.Sig)
    (hb : projected b = zero) :
    projected (Extended.bin d a b) =
      if d = 0 then zero else if d = 1 then projected a else
        if d = 2 then projected a else zero := by
  rw [projected_bin, hb]
  unfold bin
  rw [show zero = 0#512 by rfl]
  simp only [BitVec.and_zero, BitVec.or_zero, BitVec.not_zero,
    BitVec.and_allOnes]

theorem projected_first_zero : projected Extended.first = zero := by
  decide +kernel

theorem projected_first_and (b : Extended.Sig) :
    projected (Extended.bin 0 Extended.first b) = zero := by
  rw [projected_bin_zero_left _ _ _ projected_first_zero]
  rfl

theorem projected_first_signedAnd (b : Extended.Sig) :
    projected (Extended.bin 2 Extended.first b) = zero := by
  rw [projected_bin_zero_left _ _ _ projected_first_zero]
  rfl

theorem projected_first_or (b : Extended.Sig) :
    projected (Extended.bin 1 Extended.first b) = projected b := by
  rw [projected_bin_zero_left _ _ _ projected_first_zero]
  rfl

theorem projected_first_signedOther (b : Extended.Sig) :
    projected (Extended.bin 3 Extended.first b) = projected b := by
  rw [projected_bin_zero_left _ _ _ projected_first_zero]
  rfl

end PEqualNP.Outside.L_meta_2592_aux.Projection
