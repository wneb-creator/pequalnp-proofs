import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

lemma no_two_colour_of_zero (n : ℕ) (C : Circuit) (isLine : ℕ → Bool)
    (h : tCount n C isLine = 0) (g : ℕ) : ¬ IsTwoColour n C isLine g := by
  intro hg
  have hm : g ∈ twoColour n C isLine := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  have hz : twoColour n C isLine = ∅ := Finset.card_eq_zero.mp h
  rw [hz] at hm
  exact Finset.notMem_empty _ hm

lemma or_reach_monochrome (p l : ℕ) (C : Circuit)
    (h : tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn (p + l) C (p + l + g), (i : ℕ) < p) ∨
    (∀ i ∈ orIn (p + l) C (p + l + g), p ≤ (i : ℕ)) := by
  classical
  by_cases hp : ∃ i ∈ orIn (p + l) C (p + l + g), (i : ℕ) < p
  · left
    intro i hi
    by_contra hli
    obtain ⟨j, hj, hjp⟩ := hp
    apply no_two_colour_of_zero (p + l) C (fun i => decide (p ≤ i)) h g
    exact ⟨hg, hop, ⟨j, hj, by simp only [decide_eq_false_iff_not]; omega⟩,
      ⟨i, hi, by simp only [decide_eq_true_eq]; omega⟩⟩
  · right
    intro i hi
    by_contra hip
    exact hp ⟨i, hi, by omega⟩

open PEqualNP.MetaComplexity

lemma circuit_dependencies (k : ℕ) (C : Circuit) (ao : IsAO2 k C) : ∃ S : Finset (Fin k),
    S.card ≤ C.size + 1 ∧ ∀ x y : Fin k → Bool, (∀ v ∈ S, x v = y v) → circuitFun k C x = circuitFun k C y := by
  classical
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  have tailRead (w : List Bool) (b : Bool) (j : ℕ) (h : j ≠ w.length) :
      (w ++ [b]).getD j false = w.getD j false := by
    by_cases small : j < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have plan (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2) (l : ℕ) :
      ∃ P : Finset ℕ, P.card ≤ gs.length + 1 ∧ ∀ a b : List Bool,
        a.length=l → b.length=l → (∀ j ∈ P, a.getD j false = b.getD j false) →
        (gs.foldl step a).getD C.output false = (gs.foldl step b).getD C.output false := by
    induction gs generalizing l with
    | nil => exact ⟨{C.output},by simp,fun _ _ _ _ h => h _ (by simp)⟩
    | cons g gs ih =>
      obtain ⟨T,cost,agree⟩ := ih (fun v hv => arity v (List.mem_cons_of_mem _ hv)) (l+1)
      by_cases present : l ∈ T
      · let P := T.erase l ∪ g.inputs.toFinset
        refine ⟨P,?_,?_⟩
        · have h1 := Finset.card_union_le (T.erase l) g.inputs.toFinset
          have h2 := Finset.card_erase_add_one present
          have h3 := List.toFinset_card_le g.inputs
          have h4 := arity g List.mem_cons_self
          change (T.erase l ∪ g.inputs.toFinset).card ≤ gs.length+1+1
          omega
        · intro a b ha hb h
          apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
          intro j hj
          by_cases hit : j=l
          · subst j
            have vals : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) :=
              List.map_congr_left (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
            have last (u : List Bool) (hu : u.length=l) :
                (step u g).getD l false = g.op.eval (g.inputs.map fun i => u.getD i false) := by
              rw [← hu]; simp [step]
            rw [last a ha,last b hb,vals]
          · unfold step
            rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega)]
            exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hit,hj⟩))
      · refine ⟨T,by simp only [List.length_cons]; omega,?_⟩
        intro a b ha hb h
        apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
        intro j hj
        have ne : j ≠ l := fun eq => present (eq ▸ hj)
        unfold step
        rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega),h j hj]
  obtain ⟨P,bound,agrees⟩ := plan C.gates ao.2.2 k
  let S := Finset.univ.filter (fun i : Fin k => i.val ∈ P)
  have cap : S.card ≤ P.card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  refine ⟨S,cap.trans bound,?_⟩
  intro x y h
  apply agrees (List.ofFn x) (List.ofFn y) (by simp) (by simp)
  intro j hj
  by_cases small : j<k
  · let i : Fin k := ⟨j,small⟩
    have atInput (a : Fin k → Bool) : (List.ofFn a).getD j false = a i := by
      rw [List.getD_eq_getElem _ _ (by simpa)]
      exact List.getElem_ofFn _
    rw [atInput,atInput]
    exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4970
