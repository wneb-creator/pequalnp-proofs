import AllTwoFiltersOrders
import TwoRailReadersCore
import NotRailOperandCore

namespace PEqualNP.Outside.L_meta_1884.TwoFiltersRailCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open SharedFilter ElimManyCount

theorem impossible (v w : Fin 10) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (hw : w = 1 ∨ w = 4 ∨ w = 5) (hvw : v ≠ w)
    (pre before between after : List Gate) (ins : List Nat) (o : Nat)
    (legal : ∀ g ∈ pre ++ before ++ between ++ after,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (awayv : ∀ g ∈ pre ++ before ++ between ++ after, v.val ∉ g.inputs)
    (awayw : ∀ g ∈ pre ++ before ++ between ++ after, w.val ∉ g.inputs)
    (insv : v.val ∉ ins) (insw : w.val ∉ ins) (outv : o ≠ v.val) (outw : o ≠ w.val)
    (hins : ins.length ≤ 1)
    (hsize : pre.length + before.length + between.length + after.length + 3 ≤ 18)
    (used0 : ∃ g ∈ pre ++ [⟨.not,ins⟩] ++ before ++
      [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
      [⟨.and,[w.val,11 + pre.length]⟩] ++ after, 0 ∈ g.inputs)
    (used10 : ∃ g ∈ pre ++ [⟨.not,ins⟩] ++ before ++
      [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
      [⟨.and,[w.val,11 + pre.length]⟩] ++ after, 10 ∈ g.inputs)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++
        [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
        [⟨.and,[w.val,11 + pre.length]⟩] ++ after,o⟩ (TwoFilterAuxBridge.input x) =
          SoleOrPartner.target x) : False := by
  have hv0 : v ≠ 0 := by rcases hv with rfl | rfl | rfl <;> decide
  have hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    apply legal g
    simp [hg]
  have hpv : ∀ g ∈ pre, v.val ∉ g.inputs := by
    intro g hg
    apply awayv g
    simp [hg]
  have hbefore : ∀ g ∈ before, v.val ∉ g.inputs := by
    intro g hg
    apply awayv g
    simp [hg]
  have htail : ∀ g ∈ between ++ [⟨GateOp.and, [w.val, 11 + pre.length]⟩] ++ after,
      v.val ∉ g.inputs := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton, or_assoc] at hg
    rcases hg with hg | rfl | hg
    · apply awayv g; simp [hg]
    · have hvw' : v.val ≠ w.val := fun he => hvw (Fin.ext he)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hvw', by have := v.isLt; omega⟩
    · apply awayv g; simp [hg]
  have hfactor : factor v (DirectFilter.operand pre ins) := by
    apply DirectFilter.factor pre before
      (between ++ [⟨GateOp.and, [w.val, 11 + pre.length]⟩] ++ after) ins v hv0 o
      SoleOrPartner.target hpv insv hbefore htail outv
    intro x
    simpa only [List.append_assoc, List.cons_append, List.nil_append,
      DirectFilter.seed, TwoFilterAuxBridge.input] using hcompute x
  have hno : 0 ∉ ins ∧ 10 ∉ ins := by
    cases ins with
    | nil => simp
    | cons i tail =>
      have ht : tail = [] := by cases tail <;> simp_all
      subst tail
      constructor
      · intro hi
        have he : i = 0 := (List.mem_singleton.mp hi).symm
        subst i
        exact DirectFilter.excludes_positive_operand pre [] v hv0 (fun g hg => (hp g hg).1) hfactor
      · intro hi
        have he : i = 10 := (List.mem_singleton.mp hi).symm
        subst i
        exact DirectFilter.excludes_negative_operand pre [] v hv0 (fun g hg => (hp g hg).1) hfactor
  let fv : Gate := ⟨.and,[v.val,11 + pre.length]⟩
  let fw : Gate := ⟨.and,[w.val,11 + pre.length]⟩
  let C : Circuit := ⟨pre ++ [⟨.not,ins⟩] ++ before ++ [fv] ++ between ++ [fw] ++ after,o⟩
  have hbase (g : Gate) (hg : g ∈ C.gates) :
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∨ g = ⟨.not,ins⟩ := by
    simp only [C, List.mem_append, List.mem_singleton, or_assoc] at hg
    rcases hg with hg | rfl | hg | rfl | hg | rfl | hg
    · left; apply legal g; simp [hg]
    · exact Or.inr rfl
    · left; apply legal g; simp [hg]
    · exact Or.inl ⟨Or.inl rfl, by simp [fv]⟩
    · left; apply legal g; simp [hg]
    · exact Or.inl ⟨Or.inl rfl, by simp [fw]⟩
    · left; apply legal g; simp [hg]
  have hlegal : FanInTwo C := by
    intro g hg
    rcases hbase g hg with ⟨hop, hlen⟩ | rfl
    · refine ⟨?_, hlen⟩
      rcases hop with hop | hop <;> simp [hop]
    · exact ⟨by simp, by simpa using Nat.le_trans hins (by decide : 1 ≤ 2)⟩
  have htrim : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1 := by
    intro g hg hnot
    rcases hbase g hg with ⟨hop, _⟩ | rfl
    · rcases hop with hop | hop <;> rw [hnot] at hop <;> cases hop
    · exact hins
  have hcount := TwoRailReaders.at_least_two C hlegal htrim hcompute used0 used10
  have hnotread : reads Forced13Compile.rails ⟨GateOp.not, ins⟩ = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    rcases (TwoRailReaders.reader_iff _).mp htrue with h | h
    · exact hno.1 h
    · exact hno.2 h
  have filter_free (z : Fin 10) (hz : z ≠ 0) :
      reads Forced13Compile.rails ⟨GateOp.and, [z.val, 11 + pre.length]⟩ = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hzin : 0 = z.val ∨ 0 = 11 + pre.length ∨ 10 = z.val ∨ 10 = 11 + pre.length := by
      simpa [List.mem_cons, List.mem_singleton, or_assoc] using (TwoRailReaders.reader_iff _).mp htrue
    have hz0 : z.val ≠ 0 := fun he => hz (Fin.ext he)
    have := z.isLt
    omega
  have hfv := filter_free v hv0
  have hfw := filter_free w (by rcases hw with rfl | rfl | rfl <;> decide)
  have hread : 2 ≤ (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails) := by
    simpa only [C, fv, fw, List.countP_append, List.countP_cons, List.countP_nil,
      hnotread, hfv, hfw, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] using hcount
  exact AllTwoFilters.impossible v w hv hw hvw pre before between after ins o legal
    awayv awayw insv insw outv outw hsize hread hcompute

end PEqualNP.Outside.L_meta_1884.TwoFiltersRailCount
