import DynamicMemoTest
import FastRecipeImportTest
import ClosedDomains12Test
namespace PEqualNP.Outside.L_meta_670_aux.DynamicMemo

open LiveCheck DynamicLeaf

def fastInitial {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (v : List Sig) (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    CheckedContext oracles v :=
  ⟨FastRecipe.initial oracles rho hint v programs,
    FastRecipe.initial_valid oracles rho hint hr v programs⟩

def runFast {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoProtocol.Memo :=
  MemoProtocol.solve (CheckedContext oracles) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (fastInitial oracles rho hint hr v programs) .empty

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(runFast oracles rho hint hr k t v programs).1

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint hr k t v programs = true) : Impossible k t v := by
  have hs := MemoProtocol.solve_sound (CheckedContext oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound)
    k t v (fastInitial oracles rho hint hr v programs) .empty
    (show MemoProtocol.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint hr k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint hr k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicMemo
