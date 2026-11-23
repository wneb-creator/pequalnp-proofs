namespace PEqualNP.Outside.L_meta_670_aux.DynamicRaw

open LiveCheck DynamicLeaf

abbrev RawContext (n : Nat) (_ : List Sig) := Context n

def cut {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (_v : List Sig)
    (ctx : Context n) : Bool :=
  ((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (ctx i).vals == Base1007.top)) ||
      pruned oracles k ctx

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hctx : Valid oracles v ctx)
    (hv : v.Nodup) (hc : cut oracles k t v ctx = true) : Impossible k t v := by
  rcases Bool.or_eq_true_iff.mp hc with hcover | hprefix
  · obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hcover
    have hf : Base1007.unionSep (decide (0<t)) (ctx i).vals ≠ Base1007.top := by
      intro he
      simp only [he,beq_self_eq_true,Bool.not_true,Bool.false_eq_true] at hbad
    exact ProjectedCoverage.directed_failure (htarget i) (oracles i).mapNeg
      (oracles i).mapBin (hctx i) hf
  · exact pruned_sound hsound hv hctx hprefix

def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (ctx : Context n) : List (MemoBoolFast.Child (RawContext n)) :=
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        StrictPrefix.updateWithRecipe oracles v p.wires ctx (some (DynamicCovered.recipe p.move)) })
    (MemoChildren.proposals k t v)

lemma next_valid {n : Nat} (oracles : Fin n → Oracle)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hctx : Valid oracles v ctx) :
    ∀ child ∈ next oracles k t v ctx, Valid oracles child.wires (child.context ()) := by
  intro child hchild
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hchild
  exact StrictPrefix.updateWithRecipe_valid hctx p.wires (some (DynamicCovered.recipe p.move))

def runFast {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoBoolFast.Memo :=
  MemoLocalBoolFast.solve (RawContext n) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (FastRecipe.initial oracles rho hint v programs) .empty

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(runFast oracles rho hint k t v programs).1

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint k t v programs = true) : Impossible k t v := by
  have hs := MemoInvariant.solve_sound (RawContext n) (Valid oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound htarget) (next_valid oracles)
    k t v (FastRecipe.initial oracles rho hint v programs) .empty
    (FastRecipe.initial_valid oracles rho hint hr v programs)
    (show MemoBoolFast.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint k t v programs).1 with
  | false => rfl
  | true => simp only [h,Bool.not_true,Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicRaw
