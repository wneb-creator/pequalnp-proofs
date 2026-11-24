import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_5112_aux

def monoStep (xs : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

lemma mono_getD_snoc (xs : List Nat) (a i : Nat) :
    (xs ++ [a]).getD i 0 = if i = xs.length then a else xs.getD i 0 := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
  · by_cases he : i = xs.length
    · subst i
      simp
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma mono_step (xs ys : List Nat) (g : Bool × Nat × Nat) (r s : Nat)
    (hlen : xs.length = ys.length)
    (hin : ∀ i, (xs.getD i 0).testBit r = true → (ys.getD i 0).testBit s = true) :
    ∀ i, ((monoStep xs g).getD i 0).testBit r = true →
      ((monoStep ys g).getD i 0).testBit s = true := by
  intro i
  unfold monoStep
  rw [mono_getD_snoc, mono_getD_snoc]
  by_cases hi : i = xs.length
  · rw [ite_eq_left hi, ite_eq_left (hi.trans hlen)]
    cases hb : g.1 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_and,
        Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true]
    · intro h
      exact ⟨hin _ h.1, hin _ h.2⟩
    · intro h
      exact h.elim (fun h => Or.inl (hin _ h)) (fun h => Or.inr (hin _ h))
  · rw [ite_eq_right hi, ite_eq_right (fun h => hi (h.trans hlen.symm))]
    exact hin i

lemma mono_fold (xs ys : List Nat) (gs : List (Bool × Nat × Nat)) (r s k : Nat)
    (hlen : xs.length = ys.length)
    (hin : ∀ i, (xs.getD i 0).testBit r = true → (ys.getD i 0).testBit s = true) :
    ((gs.foldl monoStep xs).getD k 0).testBit r = true →
      ((gs.foldl monoStep ys).getD k 0).testBit s = true := by
  induction gs generalizing xs ys with
  | nil => exact hin k
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [monoStep, List.length_append, List.length_singleton, hlen]
    · exact mono_step xs ys g r s hlen hin

lemma evaluator_row_monotone (xs ys : List Nat) (gs : List (Bool × Nat × Nat)) (r s k : Nat)
    (hlen : xs.length = ys.length)
    (hin : ∀ i, (xs.getD i 0).testBit r = true → (ys.getD i 0).testBit s = true) :
    ((gs.foldl (fun (x2 : List Nat) (x3 : Bool × Nat × Nat) =>
      x2 ++ [if x3.1 = true then x2.getD x3.2.1 0 ||| x2.getD x3.2.2 0
        else x2.getD x3.2.1 0 &&& x2.getD x3.2.2 0]) xs).getD k 0).testBit r = true →
    ((gs.foldl (fun (x2 : List Nat) (x3 : Bool × Nat × Nat) =>
      x2 ++ [if x3.1 = true then x2.getD x3.2.1 0 ||| x2.getD x3.2.2 0
        else x2.getD x3.2.1 0 &&& x2.getD x3.2.2 0]) ys).getD k 0).testBit s = true := by
  exact mono_fold xs ys gs r s k hlen hin

end PEqualNP.Outside.L_meta_5112_aux
