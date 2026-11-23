import Mathlib.Data.Nat.Bitwise
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4

theorem add_bitwise (a b : Nat) :
    a+b = (a ||| b)+(a &&& b) ∧ a+b = (a ^^^ b)+2*(a &&& b) := by
  induction b using Nat.div2Induction generalizing a with
  | ind b ih =>
    obtain rfl | hb := Nat.eq_zero_or_pos b
    · simp
    · have hh := ih hb (a := a/2)
      have aa := Nat.mod_add_div a 2
      have bb := Nat.mod_add_div b 2
      have oo := Nat.mod_add_div (a ||| b) 2
      have nn := Nat.mod_add_div (a &&& b) 2
      have xx := Nat.mod_add_div (a ^^^ b) 2
      have hm : (a &&& b) % 2 = (a%2) &&& (b%2) := Nat.and_mod_two_pow (n := 1)
      have hx : (a ^^^ b) % 2 = (a%2) ^^^ (b%2) := Nat.xor_mod_two_pow (n := 1)
      rw [Nat.or_mod_two, Nat.or_div_two] at oo
      rw [hm, Nat.and_div_two] at nn
      rw [hx, Nat.xor_div_two] at xx
      obtain ha | ha := Nat.mod_two_eq_zero_or_one a
      all_goals obtain hb | hb := Nat.mod_two_eq_zero_or_one b
      all_goals simp [ha,hb] at oo nn xx
      all_goals omega

end PEqualNP.Outside.L_meta_982_aux.Finite.Chunk4
