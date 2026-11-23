import Fast982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4
def table : Nat := 0xfedcba9876543210eeccaa8866442200dcdc989854541010cccc888844440000ba98ba9832103210aa88aa88220022009898989810101010888888880000000076543210765432106644220066442200545410105454101044440000444400003210321032103210220022002200220010101010101010100000000000000000
def digit (a b : Nat) : Nat :=
  (table / 2^(4*(a + 16*b))) % 16

set_option maxRecDepth 100000 in
theorem digit_fin : ∀ a b : Fin 16, digit a.val b.val = a.val &&& b.val := by
  decide +kernel

theorem digit_eq (a b : Nat) (ha : a < 16) (hb : b < 16) :
    digit a b = a &&& b :=
  digit_fin ⟨a, ha⟩ ⟨b, hb⟩

def blockAnd : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, a, b =>
    digit (a % 16) (b % 16) + 16 * blockAnd fuel (a/16) (b/16)

theorem blockAnd_eq_of_lt (fuel a b : Nat)
    (ha : a < 16^fuel) (hb : b < 16^fuel) :
    blockAnd fuel a b = a &&& b := by
  induction fuel generalizing a b with
  | zero =>
    have ha0 : a = 0 := by simpa using ha
    have hb0 : b = 0 := by simpa using hb
    subst a; subst b
    rfl
  | succ fuel ih =>
    have ha' : a / 16 < 16 ^ fuel := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).2
      simpa [Nat.pow_succ] using ha
    have hb' : b / 16 < 16 ^ fuel := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).2
      simpa [Nat.pow_succ] using hb
    rw [blockAnd, digit_eq _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)), ih _ _ ha' hb']
    have hmod := @Nat.and_mod_two_pow a b 4
    have hdiv := @Nat.and_div_two_pow a b 4
    norm_num only at hmod hdiv
    rw [← hmod, ← hdiv]
    exact Nat.mod_add_div _ _

def safeAnd (fuel a b : Nat) : Nat :=
  if a < 16^fuel ∧ b < 16^fuel then blockAnd fuel a b else a &&& b

theorem safeAnd_eq (fuel a b : Nat) : safeAnd fuel a b = a &&& b := by
  unfold safeAnd
  split
  next h => exact blockAnd_eq_of_lt fuel a b h.1 h.2
  next _ => rfl
end PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4
