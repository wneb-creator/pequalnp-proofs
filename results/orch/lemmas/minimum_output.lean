import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saMinimumOutputValid (n : ℕ) (C : Circuit)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) : C.output < n + C.gates.length := by
  by_contra hn
  let D : Circuit := ⟨[], n⟩
  have hfun : circuitFun n D = circuitFun n C := by
    funext z
    have hc : circuitFun n C z = false := by
      change (C.wires (List.ofFn z)).getD C.output false = false
      apply List.getD_eq_default
      change (C.gates.foldl decStep (List.ofFn z)).length ≤ C.output
      rw [lcLength, List.length_ofFn]
      omega
    have hd : circuitFun n D z = false := by
      change (List.ofFn z).getD n false = false
      apply List.getD_eq_default
      simp
    exact hd.trans hc.symm
  have hdm : Monotone2 D := by intro g hg; simp [D] at hg
  have hdr : ReadsBack n D := by intro k hk; simp [D] at hk
  have hs := hmin D hdm hdr hfun
  change C.gates.length ≤ 0 at hs
  omega

end PEqualNP.Outside.L_meta_3451
