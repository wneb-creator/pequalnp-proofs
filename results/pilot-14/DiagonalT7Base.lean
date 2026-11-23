import Cut12StrictRuntimeSmoke
export private PEqualNP.Outside.L_meta_670_aux.LiveCheck.reduced_step from Smoke
namespace PEqualNP.Outside.L_meta_670_aux.LiveCheck

lemma exclude_step_nodup {k t : Nat} {v : List Sig} {u b : List Sig → Bool}
    (hv : v.Nodup)
    (hu : ∀ w, w.Nodup → u w = false → Impossible k (t-1) w)
    (hb : ∀ w, w.Nodup → b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Live j (t-1) w.toFinset → u w = true := by
    intro w hn j hj r
    cases e : u w
    · exact (hu _ hn e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Live j t w.toFinset → b w = true := by
    intro w hn j hj r
    cases e : b w
    · exact (hb _ hn e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

end PEqualNP.Outside.L_meta_670_aux.LiveCheck
namespace PEqualNP.Outside.L_meta_670_aux.DynamicRawNoMemo

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
        stepTest k t v
          (fun w => search oracles k (t-1) w (update oracles true v w ctx))
          (fun w => search oracles k t w (update oracles false v w ctx))

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
          simpa only [search,if_neg hp] using hc
        exact exclude_search hv hs
  | succ k ih =>
      by_cases hp : cut oracles (k+1) t v ctx = true
      · exact cut_sound oracles hsound htarget (k+1) t v ctx hctx hv hp
      · have hs : stepTest k t v
            (fun w => search oracles k (t-1) w (update oracles true v w ctx))
            (fun w => search oracles k t w (update oracles false v w ctx)) = false := by
          simpa only [search,if_neg hp] using hc
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

end PEqualNP.Outside.L_meta_670_aux.DynamicRawNoMemo
namespace PEqualNP.Outside.L_meta_670_aux.Cut12Certificate
open LiveCheck

lemma oracleSound (q : Fin 12) : (ClosedDomains12.oracles q).Sound := by
  apply ClosedDomains12.oracles_sound_from_base
  · intro m hm t T hT
    exact Base1007.noSmallSubset hm hT
  · intro m hm t T hT
    exact Base1007.noThetaSubset 0 hm hT

def terminal (k t j : Nat) (v : List Sig) : Bool :=
  k == 12 && DynamicRawNoMemo.fastLeafCheck ClosedDomains12.oracles CachedProjection.cachedRaw
    (Cut12StrictReplay.hint k t j) k t v (Cut12StrictReplay.programs (Cut12StrictReplay.hint k t j) v)

lemma terminal_sound (k t j : Nat) (v : List Sig) (h : terminal k t j v = true) :
    Impossible k t v := by
  have hh := Bool.and_eq_true_iff.mp h
  exact DynamicRawNoMemo.fastLeafCheck_sound ClosedDomains12.oracles oracleSound
    (fun q => ProjectionDomains.project_target q) CachedProjection.cachedRaw
    (Cut12StrictReplay.hint k t j) Cut12StrictReplay.rhoCorrect hh.2

def config : MetadataReplay.Config := Cut12StrictReplay.config terminal

lemma config_valid : MetadataReplay.Valid config :=
  Cut12StrictReplay.config_valid oracleSound terminal terminal_sound

lemma certified
    (checks : ∀ k ≤ 15, ∀ t ≤ 7, MetadataReplay.levelCheck config k t = true)
    (links : ∀ t ≤ 7, MetadataReplay.linkCheck config (Cut12StrictReplay.hint 15 t 1876) 15 t raw = true) :
    ∀ t ≤ 7, Impossible 15 t raw := by
  intro t ht
  exact MetadataReplay.checked_link_sound config config_valid 15 checks (by omega) ht (links t ht)

end PEqualNP.Outside.L_meta_670_aux.Cut12Certificate
namespace PEqualNP.Outside.L_meta_670_aux.DiagonalT7
open LiveCheck

def config : MetadataReplay.Config :=
  { Cut12Certificate.config with count := fun k t =>
      if t+8 = k then Cut12StrictReplay.count k t else 0 }

lemma config_valid : MetadataReplay.Valid config :=
  ⟨Cut12Certificate.config_valid.transport,Cut12Certificate.config_valid.terminal,
    Cut12Certificate.config_valid.cuts⟩

def nodes12 : List Nat := [5,9,15,16,17,165,166,167,175,180,181,186,187,193,194,213,344,355,356,362,363,364,370,399,576,579,583,696,697,702,703,707,714,725,726,884,885,886,891,892,893,901,931,1111,1112,1113,1120,1121,1166,1325]
def nodes13 : List Nat := [212,345,379,398,713,724,899,900,930,1118,1119,1165,1323,1324]
def nodes14 : List Nat := [723,1522]
def nodes15 : List Nat := [1876]

end PEqualNP.Outside.L_meta_670_aux.DiagonalT7
