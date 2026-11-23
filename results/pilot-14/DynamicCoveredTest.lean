import DynamicForcedTest
import ProjectedCoverageTest
namespace PEqualNP.Outside.L_meta_670_aux.DynamicCovered

open LiveCheck DynamicLeaf

abbrev CheckedContext {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) :=
  {ctx : Context n // Valid oracles v ctx}

def cut {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : Bool :=
  ((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (c.val i).vals == Base1007.top)) ||
      pruned oracles k c.val

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (k t : Nat) (v : List Sig) (c : CheckedContext oracles v)
    (hv : v.Nodup) (hc : cut oracles k t v c = true) : Impossible k t v := by
  rcases Bool.or_eq_true_iff.mp hc with hcover | hprefix
  · obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hcover
    have hf : Base1007.unionSep (decide (0<t)) (c.val i).vals ≠ Base1007.top := by
      intro he
      simp only [he,beq_self_eq_true,Bool.not_true,Bool.false_eq_true] at hbad
    exact ProjectedCoverage.directed_failure (htarget i) (oracles i).mapNeg
      (oracles i).mapBin (c.property i) hf
  · exact pruned_sound hsound hv c.property hprefix

def recipe : MemoChildren.Move → Recipe
  | .unary a => .unary a
  | .binary d a b => .binary d a b

def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : List (MemoForced.Child (CheckedContext oracles)) :=
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        (⟨updateWithRecipe oracles v p.wires c.val (some (recipe p.move)),
          @updateWithRecipe_valid n oracles v c.val c.property p.wires
            (some (recipe p.move))⟩ : CheckedContext oracles p.wires) })
    (MemoChildren.proposals k t v)

def initial {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    CheckedContext oracles v :=
  ⟨DynamicLeaf.initial oracles v programs,DynamicLeaf.initial_valid oracles v programs⟩

def run {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoForced.Memo :=
  MemoForced.solve (CheckedContext oracles) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (initial oracles v programs) .empty

def leafCheck {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(run oracles k t v programs).1

lemma leafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target) {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : leafCheck oracles k t v programs = true) : Impossible k t v := by
  have hs := MemoForced.solve_sound (CheckedContext oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound htarget)
    k t v (initial oracles v programs) .empty (show MemoForced.Sound .empty from trivial)
  apply hs.2
  change (run oracles k t v programs).1 = false
  unfold leafCheck at hc
  cases h : (run oracles k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicCovered
namespace PEqualNP.Outside.L_meta_670_aux.DynamicCovered

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
    Bool × MemoForced.Memo :=
  MemoForced.solve (CheckedContext oracles) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (fastInitial oracles rho hint hr v programs) .empty

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(runFast oracles rho hint hr k t v programs).1

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint hr k t v programs = true) : Impossible k t v := by
  have hs := MemoForced.solve_sound (CheckedContext oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound htarget)
    k t v (fastInitial oracles rho hint hr v programs) .empty
    (show MemoForced.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint hr k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint hr k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicCovered
