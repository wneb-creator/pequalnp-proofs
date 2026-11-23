import DynamicRawNoMemoTest
import ForceContextTest
import MemoBoolFastTest

namespace PEqualNP.Outside.L_meta_670_aux.DynamicRawNormalized

open LiveCheck DynamicLeaf

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

def update {n : Nat} (oracles : Fin n → Oracle) (unary : Bool)
    (v w : List Sig) (ctx : Context n) : Context n :=
  let r := if unary then findUnary v (w.headD zero) else findBinary v (w.headD zero)
  StrictPrefix.updateWithRecipe oracles v w ctx r

lemma update_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (u : Bool) (w : List Sig) :
    Valid oracles w (update oracles u v w ctx) :=
  StrictPrefix.updateWithRecipe_valid h w _

def search {n : Nat} (oracles : Fin n → Oracle) :
    Nat → Nat → List Sig → Context n → Bool
  | 0,t,v,ctx => if cut oracles 0 t v ctx then false else v == [target]
  | k+1,t,v,ctx =>
      if cut oracles (k+1) t v ctx then false else
        MemoBoolFast.forceWires v fun values =>
          ForceContext.materialize ctx fun flat => stepTest k t values
            (fun w => search oracles k (t-1) w (update oracles true values w flat))
            (fun w => search oracles k t w (update oracles false values w flat))

lemma search_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hv : v.Nodup)
    (hctx : Valid oracles v ctx) (hc : search oracles k t v ctx = false) :
    Impossible k t v := by
  induction k generalizing t v ctx with
  | zero =>
      by_cases hp : cut oracles 0 t v ctx = true
      · exact cut_sound oracles hsound htarget 0 t v ctx hctx hv hp
      · have hs : (v == [target]) = false := by
          simpa only [search,if_neg hp,MemoBoolFast.forceWires_eq,ForceContext.materialize_eq] using hc
        exact exclude_search hv hs
  | succ k ih =>
      by_cases hp : cut oracles (k+1) t v ctx = true
      · exact cut_sound oracles hsound htarget (k+1) t v ctx hctx hv hp
      · have hs : stepTest k t v
            (fun w => search oracles k (t-1) w (update oracles true v w ctx))
            (fun w => search oracles k t w (update oracles false v w ctx)) = false := by
          simpa only [search,if_neg hp,MemoBoolFast.forceWires_eq,ForceContext.materialize_eq] using hc
        apply exclude_step_nodup hv ?_ ?_ hs
        · intro w hn hw
          exact ih (t-1) w _ hn (update_valid hctx true w) hw
        · intro w hn hw
          exact ih t w _ hn (update_valid hctx false w) hw

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  BoolNodup.check v && !(search oracles k t v (FastRecipe.initial oracles rho hint v programs))

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint k t v programs = true) : Impossible k t v := by
  have hh := Bool.and_eq_true_iff.mp hc
  apply search_sound oracles hsound htarget k t v
    (FastRecipe.initial oracles rho hint v programs) (BoolNodup.sound hh.1)
    (FastRecipe.initial_valid oracles rho hint hr v programs)
  cases hs : search oracles k t v (FastRecipe.initial oracles rho hint v programs) with
  | false => rfl
  | true =>
      have hbad : False := by
        simpa only [hs,Bool.not_true,Bool.false_eq_true] using hh.2
      exact hbad.elim

end PEqualNP.Outside.L_meta_670_aux.DynamicRawNormalized

#print axioms PEqualNP.Outside.L_meta_670_aux.DynamicRawNormalized.fastLeafCheck_sound
