import CofactorMoves
import Mono18CanonicalCofactors

namespace PEqualNP.Outside.L_meta_2373.Live1024.CofactorCatalog

open CofactorMoves

abbrev ProfileEntry := Nat × Nat × Fin 17 × List Nat

def input (i : Nat) : Sig := inputs.getD i zero

def domain (e : ProfileEntry) : Sig :=
  (List.range 10).foldl (fun a i => a &&&
    (if e.1.testBit i then ~~~(input i) else if e.2.1.testBit i then input i else one)) one

def decodeMove (v : Nat) : Move :=
  if v < 256 then
    let i := v &&& 15
    let j := v >>> 4
    (input i &&& ~~~(input j), input j &&& ~~~(input i),
      Fin.ofNat 1024 ((1 <<< j) - (1 <<< i)))
  else if v < 272 then
    let i := v - 256
    (input i, zero, Fin.ofNat 1024 (1024 - (1 <<< i)))
  else
    let i := v - 272
    (~~~(input i), zero, Fin.ofNat 1024 (1 <<< i))

def canonicalRoots (i : Fin 17) : List Sig :=
  (NineSigned.vars (NineSigned.Mono18Cofactors.freeMask i)).map sliceNineLift

def canonicalTarget (i : Fin 17) : Sig := sliceNineLift (NineSigned.Mono18Cofactors.target i)

def canonicalBound (i : Fin 17) : Nat := NineSigned.Mono18Cofactors.bound i

lemma canonical_lower {u : Bool} (i : Fin 17) :
    Lower u (canonicalRoots i) (canonicalTarget i) (canonicalBound i) :=
  lower_lift (NineSigned.Mono18Cofactors.lower i)

lemma canonical_proper (i : Fin 17) : proper (canonicalTarget i) := by
  have positive : 0 < canonicalBound i := by fin_cases i <;> decide
  constructor
  · intro eq
    have available : Available false ((canonicalRoots i).map observe) (observe (canonicalTarget i)) := by
      rw [eq]
      exact Or.inr (Or.inl ⟨false, funext (fun r => by simp [observe, bit, zero])⟩)
    have bound := canonical_lower (u := false) i 0 _ Reach.start available
    omega
  · intro eq
    have available : Available false ((canonicalRoots i).map observe) (observe (canonicalTarget i)) := by
      rw [eq]
      refine Or.inr (Or.inl ⟨true, ?_⟩)
      funext r
      unfold observe bit one
      rw [BitVec.getLsbD_allOnes]
      simp
    have bound := canonical_lower (u := false) i 0 _ Reach.start available
    omega

def check (e : ProfileEntry) : Bool :=
  checkMap (e.2.2.2.map decodeMove) inputs graph (canonicalRoots e.2.2.1)
    (canonicalTarget e.2.2.1) &&
  (movedWord (e.2.2.2.map decodeMove) (domain e) == one)

lemma check_sound {u : Bool} {e : ProfileEntry} (ok : check e = true) :
    Slice u inputs graph (domain e) (canonicalBound e.2.2.1) := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.1 ok.2 (canonical_proper e.2.2.1) (canonical_lower e.2.2.1)

end PEqualNP.Outside.L_meta_2373.Live1024.CofactorCatalog
