import MemoBoolFastTest
import PreparedBoolUpdateTest
import StrictPrefixTest
import CheapPrefixTest
import DynamicCoveredTest
namespace PEqualNP.Outside.L_meta_670_aux.DynamicRapid
open LiveCheck DynamicLeaf DynamicPreparedBool
def strictUpdateOne {v w : List Sig} (o : Oracle) (p : Plan v w) (c : PrefixCtx) : PrefixCtx :=
  let q := p.value.value o c.vals
  let old := c.vals.idxOf q
  let cached := old < c.vals.length
  let free := o.inputs.contains q
  let fresh := !(free || cached)
  let out := if free then o.inputs.idxOf q
    else if cached then c.roots.getD old 8 else 10+c.gates.length
  StrictPrefix.compact ⟨if fresh then c.gates ++ [p.value.gate c.roots] else c.gates,
    p.routes.roots c.roots out,
    p.routes.values o.project c.vals q⟩

lemma strictUpdateOne_valid {v w : List Sig} (o : Oracle) (p : Plan v w) (c : PrefixCtx)
    (hc : c.vals = v.map o.project) :
    (strictUpdateOne o p c).vals = w.map o.project := by
  simp only [strictUpdateOne,StrictPrefix.compact_vals,hc,Expression.value_map]
  exact p.routes.values_map _

def updatePrepared {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  forcePlan (plan v w r) fun p => fun i => strictUpdateOne (oracles i) p (ctx i)

lemma updatePrepared_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updatePrepared oracles v w ctx r) := by
  simp only [updatePrepared,forcePlan_eq]
  intro i
  exact strictUpdateOne_valid _ _ _ (h i)


end PEqualNP.Outside.L_meta_670_aux.DynamicRapid

namespace PEqualNP.Outside.L_meta_670_aux.DynamicRapid

open LiveCheck DynamicLeaf

abbrev CheckedContext {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) :=
  DynamicCovered.CheckedContext oracles v


def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (c : CheckedContext oracles v) : List (MemoBoolFast.Child (CheckedContext oracles)) :=
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        (⟨updatePrepared oracles v p.wires c.val (some (DynamicCovered.recipe p.move)),
          @updatePrepared_valid n oracles v c.val c.property p.wires
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

end PEqualNP.Outside.L_meta_670_aux.DynamicRapid
