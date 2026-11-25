import GlobalMonoFilterSafe
import SafeOperandImpossible

namespace PEqualNP.Outside.L_meta_1884.TwoFilterNoNegativePrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SharedFilter

theorem impossible (pre post : List Gate) (ins : List Nat) (o : Nat) (v w : Fin 10)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18) (hins : ins.length ≤ 1)
    (hfree : ∀ g ∈ pre, 10 ∉ g.inputs)
    (hpv : ∀ g ∈ pre, v.val ∉ g.inputs) (hpw : ∀ g ∈ pre, w.val ∉ g.inputs)
    (hiv : v.val ∉ ins) (hiw : w.val ∉ ins) (hov : o ≠ v.val) (how : o ≠ w.val)
    (hpostv : ∃ mid tail : List Gate,
      post = mid ++ ⟨GateOp.and,[v.val,11 + pre.length]⟩ :: tail ∧
        (∀ g ∈ mid ++ tail, v.val ∉ g.inputs))
    (hpostw : ∃ mid tail : List Gate,
      post = mid ++ ⟨GateOp.and,[w.val,11 + pre.length]⟩ :: tail ∧
        (∀ g ∈ mid ++ tail, w.val ∉ g.inputs))
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (DirectFilter.seed x) =
        SoleOrPartner.target x) : False := by
  let H := DirectFilter.operand pre ins
  have hfm : fiberMono H := DirectFilter.operand_fiber_mono pre ins (fun g hg => (hp g hg).1)
  have hindv : independent v H := DirectFilter.operand_independent pre ins v hv0 hpv hiv
  have hindw : independent w H := DirectFilter.operand_independent pre ins w hw0 hpw hiw
  have hfv : factor v H := by
    obtain ⟨mid,tail,hpost,haway⟩ := hpostv
    apply DirectFilter.factor pre mid tail ins v hv0 o SoleOrPartner.target hpv hiv
      (fun g hg => haway g (List.mem_append.mpr (Or.inl hg)))
      (fun g hg => haway g (List.mem_append.mpr (Or.inr hg))) hov
    intro x
    simpa only [hpost,List.append_assoc,List.cons_append] using hcompute x
  have hfw : factor w H := by
    obtain ⟨mid,tail,hpost,haway⟩ := hpostw
    apply DirectFilter.factor pre mid tail ins w hw0 o SoleOrPartner.target hpw hiw
      (fun g hg => haway g (List.mem_append.mpr (Or.inl hg)))
      (fun g hg => haway g (List.mem_append.mpr (Or.inr hg))) how
    intro x
    simpa only [hpost,List.append_assoc,List.cons_append] using hcompute x
  have hno10 : 10 ∉ ins := by
    cases ins with
    | nil => simp
    | cons i tail =>
      cases tail with
      | cons j rest => simp at hins
      | nil =>
        intro hmem
        have hi : i = 10 := (List.mem_singleton.mp hmem).symm
        subst i
        have hfalse := SoleOrPartner.rejects_zero v hv0 H hfm hfv
        have htrue : H (fun _ => false) = true := by
          change (SoleReader.run pre (DirectFilter.seed (fun _ => false))).getD 10 false = true
          rw [SoleReader.run_input pre _ _ (by simp [DirectFilter.seed])]
          simp [DirectFilter.seed,List.getD_eq_getElem?_getD]
        rw [hfalse] at htrue
        cases htrue
  have hm : ∀ x y, (∀ i, x i = true → y i = true) → H x = true → H y = true :=
    GlobalMonoFilterSafe.operand_mono pre ins (fun g hg => (hp g hg).1) hfree hno10
  have hsafe := GlobalMonoFilterSafe.safe v w hv0 hw0 hvw H hm hindv hindw hfv hfw
  exact SafeOperandImpossible.impossible pre post ins o hp hs hsize hcompute hsafe

end PEqualNP.Outside.L_meta_1884.TwoFilterNoNegativePrefix
