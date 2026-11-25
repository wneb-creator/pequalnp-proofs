import DirectFilterStructure
import SafeOperandImpossible

namespace PEqualNP.Outside.L_meta_1884.TwoFilterOutsideNeighbors

open PEqualNP.CircuitLowerBounds SharedFilter DirectFilterStructure

theorem impossible (pre post : List Gate) (ins : List Nat) (o : Nat) (v w : Fin 10)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hv1 : v ≠ 1) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18)
    (hpv : ∀ g ∈ pre, v.val ∉ g.inputs) (hpw : ∀ g ∈ pre, w.val ∉ g.inputs)
    (hiv : v.val ∉ ins) (hiw : w.val ∉ ins) (hov : o ≠ v.val) (how : o ≠ w.val)
    (hpostv : soleAfter pre post v) (hpostw : soleAfter pre post w)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (DirectFilter.seed x) =
        SoleOrPartner.target x) : False := by
  obtain ⟨hm,indv,factv⟩ := facts pre post ins o v hv0 (fun g hg => (hp g hg).1)
    hpv hiv hov hpostv hcompute
  obtain ⟨_,indw,factw⟩ := facts pre post ins o w hw0 (fun g hg => (hp g hg).1)
    hpw hiw how hpostw hcompute
  have hsafe := safe_if_filter_not_neighbor v w hv0 hw0 hvw hv1 hv4 hv5
    (DirectFilter.operand pre ins) hm indv indw factv factw
  exact SafeOperandImpossible.impossible pre post ins o hp hs hsize hcompute hsafe

end PEqualNP.Outside.L_meta_1884.TwoFilterOutsideNeighbors
