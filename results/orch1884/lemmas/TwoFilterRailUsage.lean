import DirectFilterStructure
import TwoFilterNoNegativePrefix
import NoPositiveRailCore

namespace PEqualNP.Outside.L_meta_1884.TwoFilterRailUsage

open PEqualNP.CircuitLowerBounds DirectFilterStructure

theorem both_used (pre post : List Gate) (ins : List Nat) (o : Nat) (v w : Fin 10)
    (hv : v = 1 ∨ v = 4 ∨ v = 5) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18) (hins : ins.length ≤ 1)
    (hpv : ∀ g ∈ pre, v.val ∉ g.inputs) (hpw : ∀ g ∈ pre, w.val ∉ g.inputs)
    (hiv : v.val ∉ ins) (hiw : w.val ∉ ins) (hov : o ≠ v.val) (how : o ≠ w.val)
    (hpostv : soleAfter pre post v) (hpostw : soleAfter pre post w)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (DirectFilter.seed x) =
        SoleOrPartner.target x) :
    (∃ g ∈ pre ++ post, 0 ∈ g.inputs) ∧ (∃ g ∈ pre, 10 ∈ g.inputs) := by
  have hv0 : v ≠ 0 := by rcases hv with rfl | rfl | rfl <;> decide
  obtain ⟨_,hind,hfactor⟩ := facts pre post ins o v hv0 (fun g hg => (hp g hg).1)
    hpv hiv hov hpostv hcompute
  constructor
  · by_contra hnone
    push Not at hnone
    exact NoPositiveRail.impossible pre post ins o v hv
      (fun g hg => (hp g hg).1) (fun g hg => (hs g hg).1)
      (fun g hg => hnone g (List.mem_append.mpr (Or.inl hg)))
      (fun g hg => hnone g (List.mem_append.mpr (Or.inr hg))) hcompute hind hfactor
  · by_contra hnone
    push Not at hnone
    exact TwoFilterNoNegativePrefix.impossible pre post ins o v w hv0 hw0 hvw hp hs hsize hins
      hnone hpv hpw hiv hiw hov how hpostv hpostw hcompute

end PEqualNP.Outside.L_meta_1884.TwoFilterRailUsage
