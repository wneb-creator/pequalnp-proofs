namespace PEqualNP.Outside.L_meta_670_aux.FreshCodeSearch

open LiveCheck DynamicLeaf

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig) (codes : List Nat)
    (hv : v.Nodup) (hc : cut oracles rho programs k t v codes = true) :
    Impossible k t v := by
  let hint := MetadataStrictEdges.listHint v codes
  let ctx := FastRecipe.initial oracles rho hint v (programs hint v)
  have hctx : Valid oracles v ctx :=
    FastRecipe.initial_valid oracles rho hint hr v (programs hint v)
  change (((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (ctx i).vals == Base1007.top)) ||
      pruned oracles k ctx) = true at hc
  rcases Bool.or_eq_true_iff.mp hc with hcover | hprefix
  · obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hcover
    have hf : Base1007.unionSep (decide (0<t)) (ctx i).vals ≠ Base1007.top := by
      intro he
      simp only [he,beq_self_eq_true,Bool.not_true,Bool.false_eq_true] at hbad
    exact ProjectedCoverage.directed_failure (htarget i) (oracles i).mapNeg
      (oracles i).mapBin (hctx i) hf
  · exact pruned_sound hsound hv hctx hprefix

lemma search_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    (k t : Nat) (v : List Sig) (codes : List Nat) (hv : v.Nodup)
    (hc : search oracles rho programs k t v codes = false) : Impossible k t v := by
  induction k generalizing t v codes with
  | zero =>
      by_cases hp : cut oracles rho programs 0 t v codes = true
      · exact cut_sound oracles hsound htarget rho programs hr 0 t v codes hv hp
      · have hs : (v == [target]) = false := by
          simpa only [search,if_neg hp] using hc
        exact exclude_search hv hs
  | succ k ih =>
      have hh : (if cut oracles rho programs (k+1) t v codes then false else
          stepTest k t v
            (fun w => search oracles rho programs k (t-1) w (nextCodes true v codes w))
            (fun w => search oracles rho programs k t w (nextCodes false v codes w))) = false := by
        simpa only [search,MemoBoolFast.forceWires_eq,forceCodes_eq] using hc
      by_cases hp : cut oracles rho programs (k+1) t v codes = true
      · exact cut_sound oracles hsound htarget rho programs hr (k+1) t v codes hv hp
      · have hs : stepTest k t v
            (fun w => search oracles rho programs k (t-1) w (nextCodes true v codes w))
            (fun w => search oracles rho programs k t w (nextCodes false v codes w)) = false := by
          simpa only [if_neg hp] using hh
        apply exclude_step_nodup hv ?_ ?_ hs
        · intro w hn hw
          exact ih (t-1) w _ hn hw
        · intro w hn hw
          exact ih t w _ hn hw

lemma leafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig} {codes : List Nat}
    (hc : leafCheck oracles rho programs k t v codes = true) : Impossible k t v := by
  have hh := Bool.and_eq_true_iff.mp hc
  exact search_sound oracles hsound htarget rho programs hr k t v codes
    (BoolNodup.sound hh.1) (by simpa only [Bool.not_eq_true'] using hh.2)

end PEqualNP.Outside.L_meta_670_aux.FreshCodeSearch
