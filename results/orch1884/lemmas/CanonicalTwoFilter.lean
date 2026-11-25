import DirectFilterCore
import TwoFilterAuxBridge
import RelaxationFloor

namespace PEqualNP.Outside.L_meta_1884.CanonicalTwoFilter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SharedFilter StrongRelaxRows ElimManyCount

theorem auxiliary (pre before between after : List Gate) (ins : List Nat) (o : Nat)
    (legal : ∀ g ∈ pre ++ before ++ between ++ after,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (away1 : ∀ g ∈ pre ++ before ++ between ++ after, 1 ∉ g.inputs)
    (away5 : ∀ g ∈ pre ++ before ++ between ++ after, 5 ∉ g.inputs)
    (ins1 : 1 ∉ ins) (ins5 : 5 ∉ ins) (out1 : o ≠ 1) (out5 : o ≠ 5)
    (hsize : pre.length + before.length + between.length + after.length + 3 ≤ 18)
    (hread : 2 ≤ (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails))
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++
        [⟨.and,[1,11 + pre.length]⟩] ++ between ++
        [⟨.and,[5,11 + pre.length]⟩] ++ after,o⟩ (TwoFilterAuxBridge.input x) =
          SoleOrPartner.target x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 13 ∧
      (∀ m ∈ positives, D.eval (List.ofFn (StrongRelaxRows.row m)) = true) ∧
      (∀ m ∈ negatives, D.eval (List.ofFn (StrongRelaxRows.row m)) = false) := by
  let f1 : Gate := ⟨.and,[1,11 + pre.length]⟩
  let f5 : Gate := ⟨.and,[5,11 + pre.length]⟩
  let post := before ++ [f1] ++ between ++ [f5] ++ after
  have hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    apply legal g
    simp [hg]
  have hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simp only [post,List.mem_append,List.mem_singleton,or_assoc] at hg
    rcases hg with hg | rfl | hg | rfl | hg
    · apply legal g; simp [hg]
    · exact ⟨Or.inl rfl,by simp [f1]⟩
    · apply legal g; simp [hg]
    · exact ⟨Or.inl rfl,by simp [f5]⟩
    · apply legal g; simp [hg]
  have hp1 : ∀ g ∈ pre, 1 ∉ g.inputs := by intro g hg; apply away1 g; simp [hg]
  have hp5 : ∀ g ∈ pre, 5 ∉ g.inputs := by intro g hg; apply away5 g; simp [hg]
  have hbefore1 : ∀ g ∈ before, 1 ∉ g.inputs := by intro g hg; apply away1 g; simp [hg]
  have hafter5 : ∀ g ∈ after, 5 ∉ g.inputs := by intro g hg; apply away5 g; simp [hg]
  have htail1 : ∀ g ∈ between ++ [f5] ++ after, 1 ∉ g.inputs := by
    intro g hg
    simp only [List.mem_append,List.mem_singleton,or_assoc] at hg
    rcases hg with hg | rfl | hg
    · apply away1 g; simp [hg]
    · simp [f5]; omega
    · apply away1 g; simp [hg]
  have hmid5 : ∀ g ∈ before ++ [f1] ++ between, 5 ∉ g.inputs := by
    intro g hg
    simp only [List.mem_append,List.mem_singleton,or_assoc] at hg
    rcases hg with hg | rfl | hg
    · apply away5 g; simp [hg]
    · simp [f1]; omega
    · apply away5 g; simp [hg]
  have hm : fiberMono (TwoFilterAuxBridge.operand pre ins) := by
    exact DirectFilter.operand_fiber_mono pre ins (fun g hg => (hp g hg).1)
  have hi1 : independent 1 (TwoFilterAuxBridge.operand pre ins) := by
    exact DirectFilter.operand_independent pre ins 1 (by decide) hp1 ins1
  have hi5 : independent 5 (TwoFilterAuxBridge.operand pre ins) := by
    exact DirectFilter.operand_independent pre ins 5 (by decide) hp5 ins5
  have hf1 : factor 1 (TwoFilterAuxBridge.operand pre ins) := by
    apply DirectFilter.factor pre before (between ++ [f5] ++ after) ins 1 (by decide) o
      SoleOrPartner.target hp1 ins1 hbefore1 htail1 out1
    intro x
    simpa [f1,f5,List.append_assoc,DirectFilter.seed,TwoFilterAuxBridge.input] using hcompute x
  have hf5 : factor 5 (TwoFilterAuxBridge.operand pre ins) := by
    apply DirectFilter.factor pre (before ++ [f1] ++ between) after ins 5 (by decide) o
      SoleOrPartner.target hp5 ins5 hmid5 hafter5 out5
    intro x
    simpa [f1,f5,List.append_assoc,DirectFilter.seed,TwoFilterAuxBridge.input] using hcompute x
  apply TwoFilterAuxBridge.auxiliary pre post ins o hp hs
  · simp only [post,List.length_append,List.length_cons,List.length_nil] at ⊢
    omega
  · simp only [post,List.countP_append,List.countP_cons,List.countP_nil] at ⊢
    simp only [List.countP_append] at hread
    omega
  · simp [post,f1]
  · simp [post,f5]
  · intro x
    simpa only [post,f1,f5,List.cons_append,List.nil_append,List.append_assoc] using hcompute x
  · exact hm
  · exact hi1
  · exact hi5
  · exact hf1
  · exact hf5

theorem impossible (pre before between after : List Gate) (ins : List Nat) (o : Nat)
    (legal : ∀ g ∈ pre ++ before ++ between ++ after,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (away1 : ∀ g ∈ pre ++ before ++ between ++ after, 1 ∉ g.inputs)
    (away5 : ∀ g ∈ pre ++ before ++ between ++ after, 5 ∉ g.inputs)
    (ins1 : 1 ∉ ins) (ins5 : 5 ∉ ins) (out1 : o ≠ 1) (out5 : o ≠ 5)
    (hsize : pre.length + before.length + between.length + after.length + 3 ≤ 18)
    (hread : 2 ≤ (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails))
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++
        [⟨.and,[1,11 + pre.length]⟩] ++ between ++
        [⟨.and,[5,11 + pre.length]⟩] ++ after,o⟩ (TwoFilterAuxBridge.input x) =
          SoleOrPartner.target x) : False := by
  obtain ⟨D,hm,hs,hp,hn⟩ := auxiliary pre before between after ins o legal away1 away5
    ins1 ins5 out1 out5 hsize hread hcompute
  have hfloor := RelaxationFloor.fourteen D hm hp hn
  omega

end PEqualNP.Outside.L_meta_1884.CanonicalTwoFilter
