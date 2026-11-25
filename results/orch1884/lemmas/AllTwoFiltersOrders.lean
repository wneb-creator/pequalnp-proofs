import AllTwoFilters

namespace PEqualNP.Outside.L_meta_1884.AllTwoFiltersOrders

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open ElimManyCount

lemma and_step (v q : Nat) (g : Gate)
    (hg : g = ⟨GateOp.and, [v, q]⟩ ∨ g = ⟨GateOp.and, [q, v]⟩) (xs : List Bool) :
    SoleReader.step xs g = SoleReader.step xs ⟨GateOp.and, [v, q]⟩ := by
  rcases hg with rfl | rfl
  · rfl
  · simp only [SoleReader.step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and, id, Bool.and_comm]

theorem impossible (v w : Fin 10) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (hw : w = 1 ∨ w = 4 ∨ w = 5) (hvw : v ≠ w)
    (pre before between after : List Gate) (ins : List Nat) (o : Nat) (gv gw : Gate)
    (hgv : gv = ⟨GateOp.and, [v.val, 11 + pre.length]⟩ ∨
      gv = ⟨GateOp.and, [11 + pre.length, v.val]⟩)
    (hgw : gw = ⟨GateOp.and, [w.val, 11 + pre.length]⟩ ∨
      gw = ⟨GateOp.and, [11 + pre.length, w.val]⟩)
    (legal : ∀ g ∈ pre ++ before ++ between ++ after,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (awayv : ∀ g ∈ pre ++ before ++ between ++ after, v.val ∉ g.inputs)
    (awayw : ∀ g ∈ pre ++ before ++ between ++ after, w.val ∉ g.inputs)
    (insv : v.val ∉ ins) (insw : w.val ∉ ins) (outv : o ≠ v.val) (outw : o ≠ w.val)
    (hsize : pre.length + before.length + between.length + after.length + 3 ≤ 18)
    (hread : 2 ≤ (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails))
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++ [gv] ++ between ++ [gw] ++ after,o⟩
        (TwoFilterAuxBridge.input x) = SoleOrPartner.target x) : False := by
  apply AllTwoFilters.impossible v w hv hw hvw pre before between after ins o legal
    awayv awayw insv insw outv outw hsize hread
  intro x
  have he : Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++ [gv] ++ between ++ [gw] ++ after,o⟩
      (TwoFilterAuxBridge.input x) =
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++
        [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
        [⟨.and,[w.val,11 + pre.length]⟩] ++ after,o⟩ (TwoFilterAuxBridge.input x) := by
    change ((pre ++ [Gate.mk GateOp.not ins] ++ before ++ [gv] ++ between ++ [gw] ++ after).foldl
        SoleReader.step (TwoFilterAuxBridge.input x)).getD o false =
      ((pre ++ [Gate.mk GateOp.not ins] ++ before ++ [Gate.mk GateOp.and [v.val,11 + pre.length]] ++ between ++
        [Gate.mk GateOp.and [w.val,11 + pre.length]] ++ after).foldl
        SoleReader.step (TwoFilterAuxBridge.input x)).getD o false
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [and_step v.val _ gv hgv, and_step w.val _ gw hgw]
  exact he.symm.trans (hcompute x)

end PEqualNP.Outside.L_meta_1884.AllTwoFiltersOrders
