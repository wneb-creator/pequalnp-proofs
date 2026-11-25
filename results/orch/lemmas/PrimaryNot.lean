import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_2592.PrimaryNot

lemma primary_not_monotone_closure {n : Nat} (i : Fin n)
    (G : (Fin n → Bool) → Bool → Bool)
    (hG : ∀ x y, x ≤ y → ∀ a b, a ≤ b → G x a ≤ G y b)
    (hf : Monotone (fun x => G x (!(x i)))) (x : Fin n → Bool) :
    G x (!(x i)) = (G x false || G (Function.update x i false) true) := by
  have hy : Function.update x i false ≤ x := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  have hright : G (Function.update x i false) true ≤ G x (!(x i)) := by
    simpa using hf hy
  cases hi : x i with
  | false =>
      have heq : Function.update x i false = x := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [hi]
        · simp [Function.update_of_ne hji]
      have hleft := hG x x le_rfl false true (by decide)
      rw [heq]
      cases h0 : G x false <;> cases h1 : G x true <;> simp_all [Bool.le_iff_imp]
  | true =>
      cases h0 : G x false <;>
        cases h1 : G (Function.update x i false) true <;> simp_all [Bool.le_iff_imp]

def replacementExample (x y z : Bool) : Bool :=
  x && z || y && z || x && y

lemma replacementExample_computes (x y : Bool) :
    replacementExample x y (!x) = y := by
  cases x <;> cases y <;> rfl

lemma replacementExample_no_constant :
    ∀ b : Bool, ∃ x y : Bool,
      replacementExample x y b ≠ replacementExample x y (!x) := by
  decide

end PEqualNP.Outside.L_meta_2592.PrimaryNot
