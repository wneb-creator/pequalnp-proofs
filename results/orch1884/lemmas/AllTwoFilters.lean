import TwoFilterSymmetry

namespace PEqualNP.Outside.L_meta_1884.AllTwoFilters

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open TwoFilterSymmetry ElimManyCount

theorem impossible (v w : Fin 10) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (hw : w = 1 ∨ w = 4 ∨ w = 5) (hvw : v ≠ w)
    (pre before between after : List Gate) (ins : List Nat) (o : Nat)
    (legal : ∀ g ∈ pre ++ before ++ between ++ after,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (awayv : ∀ g ∈ pre ++ before ++ between ++ after, v.val ∉ g.inputs)
    (awayw : ∀ g ∈ pre ++ before ++ between ++ after, w.val ∉ g.inputs)
    (insv : v.val ∉ ins) (insw : w.val ∉ ins) (outv : o ≠ v.val) (outw : o ≠ w.val)
    (hsize : pre.length + before.length + between.length + after.length + 3 ≤ 18)
    (hread : 2 ≤ (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails))
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨.not,ins⟩] ++ before ++
        [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
        [⟨.and,[w.val,11 + pre.length]⟩] ++ after,o⟩ (TwoFilterAuxBridge.input x) =
          SoleOrPartner.target x) : False := by
  let π := permutation v w
  obtain ⟨h0, h1, h5, hinj⟩ := permutation_properties v w hv hw hvw
  have hv' : rename π v.val = 1 := by rw [rename_raw]; exact congrArg Fin.val h1
  have hw' : rename π w.val = 5 := by rw [rename_raw]; exact congrArg Fin.val h5
  have hnot : rename π (11 + pre.length) = 11 + pre.length := rename_large π _ (by omega)
  have hlegal : ∀ g ∈ (pre ++ before ++ between ++ after).map (gate π),
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa only [gate, List.length_map] using legal g' hg'
  have haven : ∀ g ∈ (pre ++ before ++ between ++ after).map (gate π), 1 ∉ g.inputs := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have ha := away π hinj v g'.inputs (awayv g' hg')
    rw [show π v = 1 from h1] at ha
    exact ha
  have hawen : ∀ g ∈ (pre ++ before ++ between ++ after).map (gate π), 5 ∉ g.inputs := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have ha := away π hinj w g'.inputs (awayw g' hg')
    rw [show π w = 5 from h5] at ha
    exact ha
  have hiv : 1 ∉ ins.map (rename π) := by
    have ha := away π hinj v ins insv
    rw [show π v = 1 from h1] at ha
    exact ha
  have hiw : 5 ∉ ins.map (rename π) := by
    have ha := away π hinj w ins insw
    rw [show π w = 5 from h5] at ha
    exact ha
  have hov : rename π o ≠ 1 := by
    intro heq
    exact outv (rename_injective π hinj (heq.trans hv'.symm))
  have how : rename π o ≠ 5 := by
    intro heq
    exact outw (rename_injective π hinj (heq.trans hw'.symm))
  have hcount : ((pre ++ before ++ between ++ after).map (gate π)).countP
      (reads Forced13Compile.rails) =
      (pre ++ before ++ between ++ after).countP (reads Forced13Compile.rails) := by
    rw [List.countP_map]
    congr 1
    funext g
    exact reads_preserved π hinj h0 g
  apply CanonicalTwoFilter.impossible (pre.map (gate π)) (before.map (gate π))
    (between.map (gate π)) (after.map (gate π)) (ins.map (rename π)) (rename π o)
    (by simpa only [List.map_append] using hlegal)
    (by simpa only [List.map_append] using haven)
    (by simpa only [List.map_append] using hawen) hiv hiw hov how
    (by simpa only [List.length_map] using hsize)
  · rw [List.map_append, List.map_append, List.map_append] at hcount
    rw [hcount]
    exact hread
  · intro x
    let C : Circuit := ⟨pre ++ [⟨.not,ins⟩] ++ before ++
      [⟨.and,[v.val,11 + pre.length]⟩] ++ between ++
      [⟨.and,[w.val,11 + pre.length]⟩] ++ after,o⟩
    have he := eval_relabel π h0 C x
    have hc : C.eval (TwoFilterAuxBridge.input (x ∘ π)) = SoleOrPartner.target x :=
      (hcompute (x ∘ π)).trans (permutation_target v w hv hw hvw x)
    rw [hc] at he
    simpa only [C, gate, List.map_append, List.map_cons, List.map_nil, List.length_map,
      hv', hw', hnot] using he

end PEqualNP.Outside.L_meta_1884.AllTwoFilters
