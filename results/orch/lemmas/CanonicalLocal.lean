import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

open PEqualNP.CircuitLowerBounds

def canonicalWire (gs : List Gate) (i : ℕ) : ℕ :=
  if i < 13 + gs.length then i else 22

def canonicalParent (gs : List Gate) (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (b : Bool) : ℕ :=
  if b then
    if canonicalWire gs (parent e true) = canonicalWire gs (parent e false) then 22
    else canonicalWire gs (parent e true)
  else canonicalWire gs (parent e false)

lemma canonical_parent_bound (gs : List Gate) (hsmall : gs.length ≤ 9)
    (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (b : Bool) :
    canonicalParent gs parent e b ≤ 22 := by
  have hw (i : ℕ) : canonicalWire gs i ≤ 22 := by
    unfold canonicalWire
    split_ifs <;> omega
  cases b
  · exact hw _
  · dsimp only [canonicalParent]
    split_ifs
    · exact Nat.le_refl _
    · exact hw _
    · exact hw _

lemma canonical_parent_valid (gs : List Gate) (parent : Fin 5 → Bool → ℕ)
    (e : Fin 5) (b : Bool) (h : canonicalParent gs parent e b ≠ 22) :
    canonicalParent gs parent e b < 13 + gs.length := by
  have hw (i : ℕ) (hi : canonicalWire gs i ≠ 22) : canonicalWire gs i < 13 + gs.length := by
    unfold canonicalWire at *
    split_ifs at * <;> omega
  cases b
  · exact hw _ h
  · dsimp only [canonicalParent] at *
    split_ifs at *
    · exact False.elim (h rfl)
    · exact hw _ h
    · exact hw _ h

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore
