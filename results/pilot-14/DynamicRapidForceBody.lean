namespace PEqualNP.Outside.L_meta_670_aux.DynamicRapidForce

open LiveCheck DynamicLeaf

abbrev CheckedContext {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) :=
  DynamicCovered.CheckedContext oracles v


def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : List (MemoBoolFast.Child (CheckedContext oracles)) :=
  let flat := ForceContext.materialize c.val id
  have hflat : Valid oracles v flat := by
    dsimp only [flat]
    rw [ForceContext.materialize_eq]
    exact c.property
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        (⟨DynamicRapid.updatePrepared oracles v p.wires flat (some (DynamicCovered.recipe p.move)),
          @DynamicRapid.updatePrepared_valid n oracles v flat hflat p.wires
            (some (DynamicCovered.recipe p.move))⟩ : CheckedContext oracles p.wires) })
    (MemoChildren.proposals k t v)

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
    Bool × MemoBoolFast.Memo :=
  MemoLocalBoolFast.solve (CheckedContext oracles) (DynamicCovered.cut oracles) (next oracles)
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
  have hs := MemoLocalBoolFast.solve_sound (CheckedContext oracles) (DynamicCovered.cut oracles)
    (next oracles) (fun _ _ _ => true) (DynamicCovered.cut_sound oracles hsound htarget)
    k t v (fastInitial oracles rho hint hr v programs) .empty
    (show MemoBoolFast.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint hr k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint hr k t v programs).1 with
  | false => rfl
  | true => simp only [h, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicRapidForce
