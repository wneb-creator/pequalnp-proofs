import Seed8SymCheck0
import Seed8SymCheck1
import Seed8SymCheck2
import Seed8SymCheck3
import Seed8SymCheck4
import Seed8SymCheck5
import Seed8SymCheck6
import Seed8SymCheck7
import Seed8SymCheck8
import Seed8SymCheck9
import Seed8SymCheck10
import Seed8SymCheck11
import Seed8SymCheck12
import Seed8SymCheck13

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Reduced
set_option maxRecDepth 100000 in
theorem seed8_pair_checks (g : Fin 14) :
    (seed8PairPerms.getD g []).length = 218 ∧
    ∀ j : Fin 218, seed8PairRow g j < 218 ∧
      seed8PairRow (seed8InversePerms.getD g 0) j < 218 ∧
      seed8PairRow g (seed8PairRow (seed8InversePerms.getD g 0) j) = j := by
  fin_cases g
  · exact seed8_pair_check_0
  · exact seed8_pair_check_1
  · exact seed8_pair_check_2
  · exact seed8_pair_check_3
  · exact seed8_pair_check_4
  · exact seed8_pair_check_5
  · exact seed8_pair_check_6
  · exact seed8_pair_check_7
  · exact seed8_pair_check_8
  · exact seed8_pair_check_9
  · exact seed8_pair_check_10
  · exact seed8_pair_check_11
  · exact seed8_pair_check_12
  · exact seed8_pair_check_13


set_option maxRecDepth 100000 in
theorem seed8_pool_checks (g : Fin 14) :
    seed8Forbidden.Subset (seed8Forbidden.map (seed8SymWord g)) := by
  fin_cases g
  · exact seed8_pool_check_0
  · exact seed8_pool_check_1
  · exact seed8_pool_check_2
  · exact seed8_pool_check_3
  · exact seed8_pool_check_4
  · exact seed8_pool_check_5
  · exact seed8_pool_check_6
  · exact seed8_pool_check_7
  · exact seed8_pool_check_8
  · exact seed8_pool_check_9
  · exact seed8_pool_check_10
  · exact seed8_pool_check_11
  · exact seed8_pool_check_12
  · exact seed8_pool_check_13


set_option maxRecDepth 100000 in
theorem seed8_sym_run (g : Nat) {u : Nat} {ys : List Nat}
    (h : RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u ys) :
    RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u (ys.map (seed8SymWord g)) := by
  let a : Fin 14 := ⟨g % 14, Nat.mod_lt _ (by decide)⟩
  have hs := seed8_pair_checks a
  have heq : seed8SymWord g = Symmetry.permWord (218+218)
      (Symmetry.liftHalf 218 (seed8PairRow a)) := by
    funext word
    exact Symmetry.fastHalfPerm_eq 218 (seed8PairPerms.getD a []) hs.1 word
  have hp : ∀ j < 218, seed8PairRow a j < 218 := fun j hj => (hs.2 ⟨j,hj⟩).1
  have hq : ∀ j < 218, seed8PairRow (seed8InversePerms.getD a 0) j < 218 :=
    fun j hj => (hs.2 ⟨j,hj⟩).2.1
  have hinv : ∀ j < 218, seed8PairRow a (seed8PairRow (seed8InversePerms.getD a 0) j) = j :=
    fun j hj => (hs.2 ⟨j,hj⟩).2.2
  have hmod : seed8SymWord (g % 14) = seed8SymWord g := by
    funext word
    simp only [seed8SymWord, Nat.mod_mod]
  have hf : seed8Forbidden.Subset (seed8Forbidden.map (seed8SymWord g)) := by
    have hh := seed8_pool_checks a
    change seed8Forbidden.Subset (seed8Forbidden.map (seed8SymWord (g % 14))) at hh
    rw [hmod] at hh
    exact hh
  rw [heq] at hf
  have hh := Symmetry.permWord_liftHalf_run 218 (seed8PairRow a)
    (seed8PairRow (seed8InversePerms.getD a 0)) hp hq hinv hf h
  simpa only [heq, Live.mask, Live.goal, Live.lo, seed8K] using hh

theorem seed8_orient_run (payload : Nat → Nat → Nat → Nat) (s i tag : Nat)
    {u : Nat} {ys : List Nat}
    (h : RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u ys) :
    RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u
      (if payload s i tag = 0 then ys else ys.map (seed8SymWord ((payload s i tag-1)%64))) := by
  split
  · exact h
  · exact seed8_sym_run _ h


theorem seed8Orient_preserves (s i tag : Nat) {u : Nat} {ys : List Nat}
    (h : Reduced.RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u ys) :
    Reduced.RNatRun seed8Forbidden (Live.mask seed8K) (Live.goal seed8K) u
      (seed8Orient s i tag ys) := by
  exact seed8_orient_run seed8Payload s i tag h

end PEqualNP.Outside.L_meta_982_aux.Finite
